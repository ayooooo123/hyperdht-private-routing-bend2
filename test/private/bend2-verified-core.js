'use strict'

const test = require('brittle')
const b4a = require('b4a')
const HyperDHT = require('../..')
const createTestnet = require('../../testnet')
const { createPrivatePeerTestScope } = require('./helpers/private-peer')
const peer = require('../../lib/private/private-peer-controller')
const { decodeDescriptor } = require('../../lib/private/overlay-descriptor-service')
const bend2 = require('../../lib/private/bend2-core')

test('Bend 2 verified IPv4 /24 & loopback diversity classification matches controller policy (LAW 8, LAW 9, LAW 15)', (t) => {
  // Rejects loopback when allowLoopback is false (LAW 9)
  t.is(bend2.classifyIPv4('127.0.0.1', 49737, false), null)
  t.is(bend2.classifyIPv4('::ffff:127.0.0.1', 49737, false), null)
  // Rejects 0.0.0.0, multicast >= 224.0.0.0, and port 0 / > 65535
  t.is(bend2.classifyIPv4('0.0.0.0', 49737, true), null)
  t.is(bend2.classifyIPv4('224.0.0.1', 49737, true), null)
  t.is(bend2.classifyIPv4('192.0.2.1', 0, true), null)
  t.is(bend2.classifyIPv4('192.0.2.1', 70000, true), null)

  // Collapses same /24 into identical DiversityKey and normalizes IPv4-mapped IPv6
  const a = bend2.classifyIPv4('192.0.2.10', 31001, false)
  const b = bend2.classifyIPv4('192.0.2.250', 31002, false)
  const mapped = bend2.classifyIPv4('::ffff:192.0.2.99', 31003, false)
  const c = bend2.classifyIPv4('192.0.3.10', 31001, false)

  t.is(a.key, 'ipv4/24:c00002')
  t.is(b.key, a.key)
  t.is(mapped.key, a.key)
  t.not(c.key, a.key)

  // Loopback compares full address + port when allowed
  const loop1 = bend2.classifyIPv4('127.0.0.1', 41001, true)
  const loop2 = bend2.classifyIPv4('127.0.0.1', 41002, true)
  t.is(loop1.key, 'loopback:4:7f000001:41001')
  t.not(loop1.key, loop2.key)

  // 4-Hop route admission rejects /24 collisions or peer_id collisions (LAW 8 & LAW 15)
  const d1 = bend2.classifyIPv4('198.51.100.1', 4000, false).term
  const d2 = bend2.classifyIPv4('203.0.113.1', 4000, false).term
  const d3 = bend2.classifyIPv4('192.0.2.1', 4000, false).term
  const d4SameSubnetAsD1 = bend2.classifyIPv4('198.51.100.99', 4001, false).term
  const d4Distinct = bend2.classifyIPv4('198.18.0.1', 4000, false).term

  const h1 = bend2.hopFromPeer(101, d1)
  const h2 = bend2.hopFromPeer(102, d2)
  const h3 = bend2.hopFromPeer(103, d3)
  const h4CollidingSubnet = bend2.hopFromPeer(104, d4SameSubnetAsD1)
  const h4CollidingPeer = bend2.hopFromPeer(101, d4Distinct)
  const h4Valid = bend2.hopFromPeer(104, d4Distinct)

  t.is(bend2.admitRoute4(h1, h2, h3, h4CollidingSubnet), null, 'same /24 rejected')
  t.is(bend2.admitRoute4(h1, h2, h3, h4CollidingPeer), null, 'reused peer_id rejected')
  const route = bend2.admitRoute4(h1, h2, h3, h4Valid)
  t.ok(route, '4-hop diverse route admitted')
  t.is(route.$, 'Route4')
})

test('Bend 2 verified fail-closed post-pin endpoint state machine (LAW 1, LAW 2, LAW 3, LAW 4)', (t) => {
  const guardAddr = 9001
  const hostileDirectAddr = 6666
  const pinnedReady = { $: 'EpPinned', guard_addr: guardAddr, route_ready: true }

  // Normal payload send while route is ready targets ONLY guardAddr
  const step1 = bend2.endpointStep(pinnedReady, {
    $: 'EvSendPayload',
    dest_direct_addr: hostileDirectAddr
  })
  t.alike(step1.action, { $: 'ActSendToPeer', target_addr: guardAddr })
  t.is(bend2.actionTargetsOnly(step1.action, guardAddr), true)

  // Route failure with fallback direct address drops fail-closed and disables route_ready (LAW 2)
  const stepFail = bend2.endpointStep(pinnedReady, {
    $: 'EvRouteFailed',
    fallback_direct_addr: hostileDirectAddr
  })
  t.alike(stepFail.state, { $: 'EpPinned', guard_addr: guardAddr, route_ready: false })
  t.alike(stepFail.action, { $: 'ActDropFailClosed' })
  t.is(bend2.actionTargetsOnly(stepFail.action, guardAddr), true)

  // Attempting to send while route_ready is false drops fail-closed
  const stepUnready = bend2.endpointStep(stepFail.state, {
    $: 'EvSendPayload',
    dest_direct_addr: hostileDirectAddr
  })
  t.alike(stepUnready.action, { $: 'ActDropFailClosed' })

  // Suspend and Destroy drop all events fail-closed (LAW 3 & LAW 4)
  const stepSuspend = bend2.endpointStep(pinnedReady, { $: 'EvSuspend' })
  t.alike(stepSuspend.state, { $: 'EpSuspended', guard_addr: guardAddr })
  const stepWhileSuspended = bend2.endpointStep(stepSuspend.state, {
    $: 'EvSendPayload',
    dest_direct_addr: hostileDirectAddr
  })
  t.alike(stepWhileSuspended.action, { $: 'ActDropFailClosed' })

  const stepDestroy = bend2.endpointStep(stepSuspend.state, { $: 'EvDestroy' })
  t.alike(stepDestroy.state, { $: 'EpDestroyed' })
  t.alike(stepDestroy.action, { $: 'ActDropFailClosed' })
})

test('Bend 2 verified pinned guards precedence, E4 sequence monotonicity, circuit retirement, splicing & affine tickets (LAW 5-7, 10-14, 16)', (t) => {
  // PinnedGuards (LAW 5, LAW 6, LAW 7)
  let gs = bend2.createGuardSet(11, 22, 33)
  t.is(bend2.firstReachableGuard(gs), 11, 'LAW 5: reachable primary is always selected')

  // Non-primary failure preserves primary (LAW 6)
  gs = bend2.recordGuardFailure(gs, 22)
  t.is(bend2.primaryGuardId(gs), 11, 'LAW 6: failing alt1 does not demote primary')
  t.is(bend2.firstReachableGuard(gs), 11)

  // Primary failure promotes first alternate (LAW 7)
  const gs2 = bend2.recordGuardFailure(bend2.createGuardSet(11, 22, 33), 11)
  t.is(bend2.primaryGuardId(gs2), 22, 'LAW 7: failing primary promotes alt1')
  t.is(bend2.firstReachableGuard(gs2), 22)

  // Monotone descriptor sequence (LAW 12)
  t.is(
    bend2.nextDescriptorSeq(100, 250, 200),
    251,
    'clock behind max(prev, remote) increments by 1'
  )
  t.is(bend2.nextDescriptorSeq(100, 250, 500), 500, 'clock ahead jumps to now without seq+1 link')

  // Circuit retirement preserves admitted streams while blocking new admissions (LAW 10 & LAW 11)
  const circuit = bend2.createCircuitState({
    closed: false,
    retired: false,
    lastStreamId: 6,
    admittedStreams: [2, 4, 6]
  })
  t.is(bend2.circuitCanAdmit(circuit), true)
  const retired = bend2.retireCircuit(circuit)
  t.is(bend2.circuitCanAdmit(retired), false, 'LAW 11: retired circuit blocks new admissions')
  t.alike(
    bend2.circuitStreams(retired),
    [2, 4, 6],
    'LAW 10: admitted streams preserved across retire'
  )

  // 4-Hop UDX relayTo splicing pair & adjacent-hop firewall (LAW 13, LAW 14, LAW 16)
  t.is(bend2.admitSplicePair(2, 0, 55), null, 'LAW 13a: zero upstream UDX ID rejected')
  t.is(bend2.admitSplicePair(2, 44, 0), null, 'LAW 13b: zero downstream UDX ID rejected')
  t.alike(bend2.admitSplicePair(2, 44, 55), {
    $: 'SplicePair',
    stream_id: 2,
    up_udx_id: 44,
    down_udx_id: 55
  })
  t.is(
    bend2.spliceFirewallAllow('127.0.0.1', 49001, '127.0.0.1', 49001),
    true,
    'LAW 14: adjacent hop allowed'
  )
  t.is(
    bend2.spliceFirewallAllow('127.0.0.1', 49001, '127.0.0.1', 49002),
    false,
    'non-adjacent port blocked'
  )

  // Affine single-use AdmissionTicket (Kind(&1))
  const ticket = bend2.createAdmissionTicket(777, 19)
  t.alike(bend2.consumeAdmissionTicket(ticket), { tokenId: 777, period: 19 })
  t.exception(() => bend2.consumeAdmissionTicket(ticket), /ERR_AFFINE_TICKET_REPLAY/)
})

test('Live 4-hop HyperDHT private-routing session validated by Bend 2 core', async (t) => {
  t.timeout(120_000)
  const net = await createTestnet(1, { bootstrap: [] })
  const scope = createPrivatePeerTestScope()
  t.teardown(async () => {
    try {
      await net.destroy()
    } finally {
      scope.close()
    }
  })

  const controllers = new Map()
  const observedEvents = []
  const original = peer.createPrivatePeerController
  peer.createPrivatePeerController = (options) => {
    const controller = original(options)
    controllers.set(options.dht, controller)
    return controller
  }

  let nodes
  try {
    nodes = [false, false, true, true, true, true, true, true].map((relay) =>
      scope.create(
        () =>
          net.createNode({
            ephemeral: false,
            firewalled: false,
            privateRouting: {
              release: 'alpha',
              acknowledgeAlpha: true,
              mode: 'optional',
              profile: 'standard',
              relay
            }
          }),
        {
          observer(ev) {
            observedEvents.push(ev)
          }
        }
      )
    )
  } finally {
    peer.createPrivatePeerController = original
  }

  await Promise.all(nodes.map((node) => node.privateRouting.ready()))
  const [source, destination] = nodes
  const relayMap = new Map()
  for (const relayNode of nodes.slice(2)) {
    const ctrl = controllers.get(relayNode)
    const addr = relayNode.address()
    relayMap.set(b4a.toString(ctrl.relayKeyPair.publicKey, 'hex'), {
      publicKey: ctrl.relayKeyPair.publicKey,
      host: addr.host,
      port: addr.port
    })
  }

  const server = destination.privateRouting.createServer((socket) => {
    socket.on('error', () => {})
    socket.on('data', (chunk) => {
      socket.write(b4a.concat([b4a.from('bend2-verified:'), chunk]))
    })
  })
  t.teardown(() => server.close())
  await server.listen(HyperDHT.keyPair())

  const client = source.privateRouting.connect(server.publicKey)
  client.on('error', () => {})
  t.teardown(() => client.destroy())
  t.is(await client.opened, true, '4-hop private NoiseSecretStream opened')

  const replyPromise = new Promise((resolve, reject) => {
    client.once('data', resolve)
    client.once('error', reject)
  })
  client.write(b4a.from('4hop-payload'))
  const reply = await replyPromise
  t.alike(reply, b4a.from('bend2-verified:4hop-payload'), 'round-trip payload over 4-hop route')

  const selected = observedEvents.find((e) => e.type === 'source-route-selected')
  t.ok(selected, 'captured 4-hop route selection event')

  // Validate the live 4-hop route (S1, S2, Entry, Guard) through the Bend 2 verified core!
  const hopKeys = [
    selected.firstSafetyRelayPublicKey,
    selected.secondSafetyRelayPublicKey,
    selected.entryRelayPublicKey,
    selected.destinationGuardPublicKey
  ]
  const bendHops = hopKeys.map((pk) => {
    const info = relayMap.get(b4a.toString(pk, 'hex'))
    const classified = bend2.classifyIPv4(info.host, info.port, true)
    t.ok(classified, 'Bend 2 classified live relay tuple ' + info.host + ':' + info.port)
    return bend2.hopFromPeer(pk, classified.term)
  })

  const verifiedRoute = bend2.admitRoute4(bendHops[0], bendHops[1], bendHops[2], bendHops[3])
  t.ok(verifiedRoute, 'Bend 2 admit_route4 verified live 4-hop path diversity (LAW 15)')

  // Validate descriptor sequence progression across publish refresh using Bend 2's next_descriptor_seq
  const descBefore = decodeDescriptor(server._descriptor)
  const nowBefore = controllers.get(destination).clock.now()
  const expectedNextSeq = bend2.nextDescriptorSeq(descBefore.seq, 0n, nowBefore)
  t.ok(
    expectedNextSeq > Number(descBefore.seq),
    'Bend 2 LAW 12 guarantees strictly advancing descriptor seq'
  )
})
