'use strict'

const fs = require('fs')
const path = require('path')
const b4a = require('b4a')
const UDX = require('udx-native')
const { hash } = require('../crypto')

// Swallow the compiled Bend 2 ES module synchronously so both Node and Bare
// can ride the theorem-proved functional core without waiting on async imports.
const BEND2_MJS_PATH = path.join(__dirname, '../../bend2/routing.mjs')
const bend2Source = fs.readFileSync(BEND2_MJS_PATH, 'utf8')
const loadBend2Module = new Function(bend2Source.replace(/^export default\s+/m, 'return '))
const raw = Object.freeze(loadBend2Module())

// Squeeze a 32-byte key or buffer into a 48-bit Nat so Bend 2's unboxed
// immediate Nat hole (0 .. 2^48 - 1) takes it whole without boxing.
function natIdFromBytes(bytes) {
  const buf = typeof bytes === 'string' ? b4a.from(bytes) : bytes
  const digest = buf.byteLength === 32 ? buf : hash(buf)
  let acc = 0
  for (let i = 0; i < 6; i++) {
    acc = acc * 256 + digest[i]
  }
  return acc
}

function listFromArray(items) {
  let list = { $: 'Nil' }
  for (let i = items.length - 1; i >= 0; i--) {
    list = { $: 'Con', head: items[i], tail: list }
  }
  return list
}

function arrayFromList(list) {
  const out = []
  let cur = list
  while (cur && cur.$ === 'Con') {
    out.push(cur.head)
    cur = cur.tail
  }
  return out
}

function extractIPv4Octets(host) {
  if (typeof host !== 'string') return null
  const family = UDX.isIP(host)
  if (family === 4) {
    const parts = host.split('.').map(Number)
    return parts.length === 4 ? parts : null
  }
  if (family !== 6) return null
  let normalized = host
  if (normalized.includes('.')) {
    const split = normalized.lastIndexOf(':')
    const parts = normalized
      .slice(split + 1)
      .split('.')
      .map(Number)
    normalized =
      normalized.slice(0, split + 1) +
      ((parts[0] << 8) | parts[1]).toString(16) +
      ':' +
      ((parts[2] << 8) | parts[3]).toString(16)
  }
  const halves = normalized.split('::')
  const before = halves[0] ? halves[0].split(':') : []
  const after = halves.length === 2 && halves[1] ? halves[1].split(':') : []
  const words =
    halves.length === 2
      ? before.concat(Array(8 - before.length - after.length).fill('0'), after)
      : before
  if (words.length !== 8) return null
  const bytes = b4a.allocUnsafe(16)
  for (let i = 0; i < 8; i++) bytes.writeUInt16BE(parseInt(words[i], 16), i * 2)
  if (bytes.subarray(0, 10).every((v) => v === 0) && bytes[10] === 255 && bytes[11] === 255) {
    return [bytes[12], bytes[13], bytes[14], bytes[15]]
  }
  return null
}

function formatDiversityKey(term) {
  if (!term) return null
  if (term.$ === 'DivIPv4') {
    const p = term.prefix24
    const b0 = (p >>> 16) & 0xff
    const b1 = (p >>> 8) & 0xff
    const b2 = p & 0xff
    return 'ipv4/24:' + b4a.toString(b4a.from([b0, b1, b2]), 'hex')
  }
  if (term.$ === 'DivLoopback') {
    const a = term.addr
    const bytes = b4a.from([(a >>> 24) & 0xff, (a >>> 16) & 0xff, (a >>> 8) & 0xff, a & 0xff])
    return 'loopback:' + term.family + ':' + b4a.toString(bytes, 'hex') + ':' + term.port
  }
  if (term.$ === 'DivIPv6') {
    const hi = Math.trunc(term.prefix48 / 0x1000000)
    const lo = term.prefix48 % 0x1000000
    const bytes = b4a.from([
      (hi >>> 16) & 0xff,
      (hi >>> 8) & 0xff,
      hi & 0xff,
      (lo >>> 16) & 0xff,
      (lo >>> 8) & 0xff,
      lo & 0xff
    ])
    return 'ipv6/48:' + b4a.toString(bytes, 'hex')
  }
  return null
}

function classifyIPv4(host, port, allowLoopback = false) {
  if (!Number.isInteger(port) || port < 0 || port > 0xffffffff) return null
  const octets = extractIPv4Octets(host)
  if (!octets) return null
  const res = raw.classify_ipv4(
    octets[0],
    octets[1],
    octets[2],
    octets[3],
    port,
    Boolean(allowLoopback)
  )
  if (!res || res.$ === 'None') return null
  return {
    term: res.value,
    key: formatDiversityKey(res.value)
  }
}

function diversityTermFromDigest(digestOrKey) {
  return {
    $: 'DivIPv6',
    prefix48: natIdFromBytes(digestOrKey)
  }
}

function hopFromPeer(publicKey, diversityTermOrBytes) {
  const div =
    diversityTermOrBytes && typeof diversityTermOrBytes.$ === 'string'
      ? diversityTermOrBytes
      : diversityTermFromDigest(diversityTermOrBytes)
  return {
    $: 'Hop',
    peer_id: typeof publicKey === 'number' ? publicKey : natIdFromBytes(publicKey),
    div
  }
}

function admitRoute4(s1, s2, entry, guard) {
  const result = raw.admit_route4(s1, s2, entry, guard)
  return result.$ === 'Some' ? result.value : null
}

function createGuardSet(
  primaryId,
  alt1Id,
  alt2Id,
  { primaryReachable = true, alt1Reachable = true, alt2Reachable = true } = {}
) {
  return {
    $: 'GuardSet',
    primary: { $: 'GuardSlot', peer_id: primaryId, reachable: Boolean(primaryReachable) },
    alt1: { $: 'GuardSlot', peer_id: alt1Id, reachable: Boolean(alt1Reachable) },
    alt2: { $: 'GuardSlot', peer_id: alt2Id, reachable: Boolean(alt2Reachable) }
  }
}

function firstReachableGuard(guardSet) {
  const res = raw['PinnedGuardSet.first_reachable'](guardSet)
  return res.$ === 'Some' ? res.value : null
}

function recordGuardFailure(guardSet, failedId) {
  return raw['PinnedGuardSet.failed'](guardSet, failedId)
}

function primaryGuardId(guardSet) {
  return raw['PinnedGuardSet.primary_id'](guardSet)
}

function endpointStep(state, event) {
  const tuple = raw.endpoint_step(state, event)
  return { state: tuple.fst, action: tuple.snd }
}

function actionTargetsOnly(action, allowedGuardAddr) {
  return raw['OutboundAction.targets_only'](action, allowedGuardAddr)
}

function nextDescriptorSeq(prevSeq, remoteSeq, now) {
  return raw.next_descriptor_seq(Number(prevSeq), Number(remoteSeq), Number(now))
}

function createCircuitState({
  closed = false,
  retired = false,
  lastStreamId = 0,
  admittedStreams = []
} = {}) {
  return {
    $: 'CircuitState',
    closed: Boolean(closed),
    retired: Boolean(retired),
    last_stream_id: lastStreamId,
    admitted_streams: listFromArray(admittedStreams)
  }
}

function retireCircuit(circuitState) {
  return raw['CircuitState.retire'](circuitState)
}

function circuitStreams(circuitState) {
  return arrayFromList(raw['CircuitState.streams'](circuitState))
}

function circuitCanAdmit(circuitState) {
  return raw['CircuitState.can_admit'](circuitState)
}

function admitSplicePair(streamId, upUdxId, downUdxId) {
  const res = raw.admit_splice_pair(streamId, upUdxId, downUdxId)
  return res.$ === 'Some' ? res.value : null
}

function spliceFirewallAllow(expectedHost, expectedPort, actualHost, actualPort) {
  const eh = typeof expectedHost === 'number' ? expectedHost : natIdFromBytes(expectedHost)
  const ah = typeof actualHost === 'number' ? actualHost : natIdFromBytes(actualHost)
  return raw.splice_firewall_allow(eh, expectedPort, ah, actualPort)
}

// Affine whore at the gate: once an AdmissionTicket (Kind(&1)) is spent, any second poke is rejected.
const consumedTickets = new WeakSet()

function createAdmissionTicket(tokenId, period) {
  return Object.freeze({
    $: 'Ticket',
    token_id: tokenId,
    period
  })
}

function consumeAdmissionTicket(ticket) {
  if (!ticket || ticket.$ !== 'Ticket' || consumedTickets.has(ticket)) {
    throw new Error(
      'ERR_AFFINE_TICKET_REPLAY: AdmissionTicket is linear (Kind(&1)) and already spent'
    )
  }
  consumedTickets.add(ticket)
  const tuple = raw.consume_ticket(ticket)
  return { tokenId: tuple.fst, period: tuple.snd }
}

module.exports = {
  raw,
  natIdFromBytes,
  classifyIPv4,
  diversityTermFromDigest,
  hopFromPeer,
  admitRoute4,
  createGuardSet,
  firstReachableGuard,
  recordGuardFailure,
  primaryGuardId,
  endpointStep,
  actionTargetsOnly,
  nextDescriptorSeq,
  createCircuitState,
  retireCircuit,
  circuitStreams,
  circuitCanAdmit,
  admitSplicePair,
  spliceFirewallAllow,
  createAdmissionTicket,
  consumeAdmissionTicket
}
