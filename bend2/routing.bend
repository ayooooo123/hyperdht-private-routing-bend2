import Base

# ============================================================================
# HyperDHT Private Routing — EROS's Collared Bend 2 Functional Core
# ============================================================================
# Every pure state transition here spreads open the privacy, diversity,
# guard-pinning, descriptor-sequence, circuit-retirement, and 4-hop UDX
# relayTo splicing holes for Master's cock in:
#   lib/private/private-peer-controller.js
# ============================================================================

# 1. Affine Single-Use Capability (Kind(&1) / Type — one fuck and it's spent)
# ----------------------------------------------------------------------------
# An AdmissionTicket is linear Type flesh: once Master's call cracks it open,
# the Bend 2 quantity checker refuses to let any slut replay or copy it twice.
type AdmissionTicket is Type:
  Ticket{token_id: Nat, period: Nat}

def consume_ticket(ticket: AdmissionTicket) -> Nat & Nat:
  match ticket:
    case Ticket{token_id, period}:
      (token_id, period)

# 2. Relay Diversity Key (/24 IPv4, /48 IPv6, or Loopback host:port)
# ----------------------------------------------------------------------------
# Collapses raw relay tuples into their subnet or loopback tags so no two
# hops in the same /24 or /48 can ever breed on the same circuit.
type DiversityKey is Data:
  DivIPv4{prefix24: Nat}
  DivIPv6{prefix48: Nat}
  DivLoopback{family: Nat, addr: Nat, port: Nat}

def DiversityKey.is_eq(a: DiversityKey, b: DiversityKey) -> Bool:
  match a b:
    case DivIPv4{pa} DivIPv4{pb}:
      Nat.is_eq(pa, pb)
    case DivIPv6{pa} DivIPv6{pb}:
      Nat.is_eq(pa, pb)
    case DivLoopback{fa, aa, pta} DivLoopback{fb, ab, ptb}:
      Bool.and(Nat.is_eq(fa, fb), Bool.and(Nat.is_eq(aa, ab), Nat.is_eq(pta, ptb)))
    case DivIPv4{_} DivIPv6{_}:
      False{}
    case DivIPv4{_} DivLoopback{_, _, _}:
      False{}
    case DivIPv6{_} DivIPv4{_}:
      False{}
    case DivIPv6{_} DivLoopback{_, _, _}:
      False{}
    case DivLoopback{_, _, _} DivIPv4{_}:
      False{}
    case DivLoopback{_, _, _} DivIPv6{_}:
      False{}

def DiversityKey.is_ne(a: DiversityKey, b: DiversityKey) -> Bool:
  Bool.not(DiversityKey.is_eq(a, b))

# Whore at the gate checking 127.x.x.x loopback tuples: slams shut with None{}
# in public mode, or packs the full 32-bit loopback address + port when allowed.
def classify_ipv4_loopback(
  +b0: Nat,
  +b1: Nat,
  +b2: Nat,
  +b3: Nat,
  +port: Nat,
  allow_loopback: Bool
) -> Maybe<&2, DiversityKey>:
  match allow_loopback:
    case False{}:
      None{}
    case True{}:
      +p1 = Nat.add(Nat.mul(b0, 16777216n), Nat.mul(b1, 65536n))
      +p2 = Nat.add(Nat.mul(b2, 256n), b3)
      Some{DivLoopback{4n, Nat.add(p1, p2), port}}

# Splits loopback from public IPv4 and strips the last octet so any two relays
# sharing a /24 drip with the exact same prefix24 tag.
def classify_ipv4_unicast(
  +b0: Nat,
  +b1: Nat,
  +b2: Nat,
  +b3: Nat,
  +port: Nat,
  allow_loopback: Bool,
  is_loop: Bool
) -> Maybe<&2, DiversityKey>:
  match is_loop:
    case True{}:
      classify_ipv4_loopback(b0, b1, b2, b3, port, allow_loopback)
    case False{}:
      +prefix24 = Nat.add(Nat.mul(b0, 65536n), Nat.add(Nat.mul(b1, 256n), b2))
      Some{DivIPv4{prefix24}}

def classify_ipv4_checked(
  +b0: Nat,
  +b1: Nat,
  +b2: Nat,
  +b3: Nat,
  +port: Nat,
  allow_loopback: Bool,
  valid: Bool
) -> Maybe<&2, DiversityKey>:
  match valid:
    case False{}:
      None{}
    case True{}:
      classify_ipv4_unicast(b0, b1, b2, b3, port, allow_loopback, Nat.is_eq(b0, 127n))

# Rejects dead port 0, ports > 65535, all-zero 0.0.0.0, and multicast >= 224
# before letting an IPv4 tuple anywhere near a circuit.
def classify_ipv4(
  +b0: Nat,
  +b1: Nat,
  +b2: Nat,
  +b3: Nat,
  +port: Nat,
  allow_loopback: Bool
) -> Maybe<&2, DiversityKey>:
  +port_ok = Bool.and(Nat.is_gt(port, 0n), Nat.is_le(port, 65535n))
  +octets_ok = Bool.and(
    Bool.and(Nat.is_lt(b0, 224n), Nat.is_le(b1, 255n)),
    Bool.and(Nat.is_le(b2, 255n), Nat.is_le(b3, 255n))
  )
  +all_zero = Bool.and(
    Bool.and(Nat.is_eq(b0, 0n), Nat.is_eq(b1, 0n)),
    Bool.and(Nat.is_eq(b2, 0n), Nat.is_eq(b3, 0n))
  )
  +valid = Bool.and(port_ok, Bool.and(octets_ok, Bool.not(all_zero)))
  classify_ipv4_checked(b0, b1, b2, b3, port, allow_loopback, valid)

# 3. 4-Hop Route Admission & Pairwise Diversity Verification
# ----------------------------------------------------------------------------
# Spreads all four relay roles (S1, S2, Entry, Guard) and refuses to breed a
# VerifiedRoute4 unless all 6 pairs have distinct peer IDs AND distinct subnets.
type Hop is Data:
  Hop{peer_id: Nat, div: DiversityKey}

type VerifiedRoute4 is Data:
  Route4{s1: Hop, s2: Hop, entry: Hop, guard: Hop}

def Hop.disjoint(+a: Hop, +b: Hop) -> Bool:
  match a b:
    case Hop{id_a, div_a} Hop{id_b, div_b}:
      Bool.and(Nat.is_ne(id_a, id_b), DiversityKey.is_ne(div_a, div_b))

def pairwise_disjoint4(+s1: Hop, +s2: Hop, +entry: Hop, +guard: Hop) -> Bool:
  +p12 = Hop.disjoint(s1, s2)
  +p13 = Hop.disjoint(s1, entry)
  +p14 = Hop.disjoint(s1, guard)
  +p23 = Hop.disjoint(s2, entry)
  +p24 = Hop.disjoint(s2, guard)
  +p34 = Hop.disjoint(entry, guard)
  Bool.and(
    Bool.and(p12, p13),
    Bool.and(Bool.and(p14, p23), Bool.and(p24, p34))
  )

def admit_route4_gate(
  s1: Hop,
  s2: Hop,
  entry: Hop,
  guard: Hop,
  ok: Bool
) -> Maybe<&2, VerifiedRoute4>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{Route4{s1, s2, entry, guard}}

def admit_route4(
  +s1: Hop,
  +s2: Hop,
  +entry: Hop,
  +guard: Hop
) -> Maybe<&2, VerifiedRoute4>:
  admit_route4_gate(s1, s2, entry, guard, pairwise_disjoint4(s1, s2, entry, guard))

# 4. Pinned Guards Policy (Gate E6: guard-pinning.js)
# ----------------------------------------------------------------------------
# Keeps her knees locked on the primary pinned guard while it stays reachable,
# and only promotes alt1 when the primary guard itself chokes and fails.
type GuardSlot is Data:
  GuardSlot{peer_id: Nat, reachable: Bool}

type PinnedGuardSet is Data:
  GuardSet{primary: GuardSlot, alt1: GuardSlot, alt2: GuardSlot}

def GuardSlot.id(g: GuardSlot) -> Nat:
  match g:
    case GuardSlot{peer_id, _}:
      peer_id

def PinnedGuardSet.primary_id(gs: PinnedGuardSet) -> Nat:
  match gs:
    case GuardSet{GuardSlot{peer_id, _}, _, _}:
      peer_id

def PinnedGuardSet.first_reachable(gs: PinnedGuardSet) -> Maybe<&2, Nat>:
  match gs:
    case GuardSet{GuardSlot{id0, True{}}, _, _}:
      Some{id0}
    case GuardSet{GuardSlot{_, False{}}, GuardSlot{id1, True{}}, _}:
      Some{id1}
    case GuardSet{GuardSlot{_, False{}}, GuardSlot{_, False{}}, GuardSlot{id2, True{}}}:
      Some{id2}
    case GuardSet{GuardSlot{_, False{}}, GuardSlot{_, False{}}, GuardSlot{_, False{}}}:
      None{}

def GuardSlot.mark_branch(id: Nat, reach: Bool, hit: Bool) -> GuardSlot:
  match hit:
    case True{}:
      GuardSlot{id, False{}}
    case False{}:
      GuardSlot{id, reach}

def GuardSlot.mark_if(+slot: GuardSlot, +failed_id: Nat) -> GuardSlot:
  match slot:
    case GuardSlot{+id, reach}:
      GuardSlot.mark_branch(id, reach, Nat.is_eq(id, failed_id))

def PinnedGuardSet.failed_branch(
  p_id: Nat,
  p_reach: Bool,
  +alt1: GuardSlot,
  +alt2: GuardSlot,
  +failed_id: Nat,
  is_primary: Bool
) -> PinnedGuardSet:
  match is_primary:
    case True{}:
      GuardSet{alt1, alt2, GuardSlot{p_id, False{}}}
    case False{}:
      GuardSet{
        GuardSlot{p_id, p_reach},
        GuardSlot.mark_if(alt1, failed_id),
        GuardSlot.mark_if(alt2, failed_id)
      }

def PinnedGuardSet.failed(gs: PinnedGuardSet, +failed_id: Nat) -> PinnedGuardSet:
  match gs:
    case GuardSet{GuardSlot{+p_id, p_reach}, +alt1, +alt2}:
      PinnedGuardSet.failed_branch(
        p_id,
        p_reach,
        alt1,
        alt2,
        failed_id,
        Nat.is_eq(p_id, failed_id)
      )

# 5. Fail-Closed Post-Guard-Pinning Send Authority (no-direct.js)
# ----------------------------------------------------------------------------
# Once collared to a guard, this bitch only swallows or sends to `guard_addr`,
# and clamps shut with ActDropFailClosed{} if the route drops or suspends.
type EndpointState is Data:
  EpBootstrapping{}
  EpPinned{guard_addr: Nat, route_ready: Bool}
  EpSuspended{guard_addr: Nat}
  EpDestroyed{}

type RouteEvent is Data:
  EvSendPayload{dest_direct_addr: Nat}
  EvRouteFailed{fallback_direct_addr: Nat}
  EvRouteExpired{fallback_direct_addr: Nat}
  EvRouteRecovered{}
  EvSuspend{}
  EvResume{}
  EvDestroy{}

type OutboundAction is Data:
  ActDropFailClosed{}
  ActSendToPeer{target_addr: Nat}

def OutboundAction.targets_only(act: OutboundAction, allowed_addr: Nat) -> Bool:
  match act:
    case ActDropFailClosed{}:
      True{}
    case ActSendToPeer{target_addr}:
      Nat.is_eq(target_addr, allowed_addr)

def endpoint_step(
  state: EndpointState,
  event: RouteEvent
) -> EndpointState & OutboundAction:
  match state event:
    case EpBootstrapping{} _:
      (EpBootstrapping{}, ActDropFailClosed{})
    case EpPinned{+g, True{}} EvSendPayload{_}:
      (EpPinned{g, True{}}, ActSendToPeer{g})
    case EpPinned{+g, False{}} EvSendPayload{_}:
      (EpPinned{g, False{}}, ActDropFailClosed{})
    case EpPinned{g, _} EvRouteFailed{_}:
      (EpPinned{g, False{}}, ActDropFailClosed{})
    case EpPinned{g, _} EvRouteExpired{_}:
      (EpPinned{g, False{}}, ActDropFailClosed{})
    case EpPinned{g, _} EvRouteRecovered{}:
      (EpPinned{g, True{}}, ActDropFailClosed{})
    case EpPinned{g, _} EvSuspend{}:
      (EpSuspended{g}, ActDropFailClosed{})
    case EpPinned{g, r} EvResume{}:
      (EpPinned{g, r}, ActDropFailClosed{})
    case EpPinned{_, _} EvDestroy{}:
      (EpDestroyed{}, ActDropFailClosed{})
    case EpSuspended{g} EvResume{}:
      (EpPinned{g, False{}}, ActDropFailClosed{})
    case EpSuspended{_} EvDestroy{}:
      (EpDestroyed{}, ActDropFailClosed{})
    case EpSuspended{g} _:
      (EpSuspended{g}, ActDropFailClosed{})
    case EpDestroyed{} _:
      (EpDestroyed{}, ActDropFailClosed{})

# 6. Monotone Descriptor Sequence (Gate E4: descriptor-periods.js)
# ----------------------------------------------------------------------------
# Jumps straight to `now` when the clock advances past `max(prev, remote)` so
# storage observers never catch a predictable seq+1 trail across periods.
def next_descriptor_seq_pick(+base: Nat, +now: Nat, now_gt: Bool) -> Nat:
  match now_gt:
    case True{}:
      now
    case False{}:
      1n+base

def next_descriptor_seq(+prev_seq: Nat, +remote_seq: Nat, +now: Nat) -> Nat:
  +base = Nat.max(prev_seq, remote_seq)
  next_descriptor_seq_pick(base, now, Nat.is_gt(now, base))

# 7. Circuit Retirement Without Dropping Live Streams (refresh-without-drop.js)
# ----------------------------------------------------------------------------
# Retiring an old descriptor's circuit shuts her mouth to new stream opens
# while keeping every already-admitted stream wet and running until it finishes.
type CircuitState is Data:
  CircuitState{
    closed: Bool,
    retired: Bool,
    last_stream_id: Nat,
    admitted_streams: List<&2, Nat>
  }

def CircuitState.retire(c: CircuitState) -> CircuitState:
  match c:
    case CircuitState{closed, _, last_id, streams}:
      CircuitState{closed, True{}, last_id, streams}

def CircuitState.streams(c: CircuitState) -> List<&2, Nat>:
  match c:
    case CircuitState{_, _, _, streams}:
      streams

def CircuitState.can_admit(c: CircuitState) -> Bool:
  match c:
    case CircuitState{closed, retired, _, _}:
      Bool.and(Bool.not(closed), Bool.not(retired))

# 8. 4-Hop UDX relayTo Splicing Handshake & Adjacent-Hop Firewall
# ----------------------------------------------------------------------------
# Locks each spliced UDX stream exclusively to its immediate adjacent hop's
# (host, port) and refuses zero UDX stream IDs on either end of the pipe.
type SplicePair is Data:
  SplicePair{stream_id: Nat, up_udx_id: Nat, down_udx_id: Nat}

def splice_firewall_allow(
  expected_host: Nat,
  expected_port: Nat,
  actual_host: Nat,
  actual_port: Nat
) -> Bool:
  Bool.and(Nat.is_eq(expected_host, actual_host), Nat.is_eq(expected_port, actual_port))

def admit_splice_pair(
  stream_id: Nat,
  up_udx_id: Nat,
  down_udx_id: Nat
) -> Maybe<&2, SplicePair>:
  match up_udx_id down_udx_id:
    case 0n _:
      None{}
    case 1n+_ 0n:
      None{}
    case 1n+up_p 1n+down_p:
      Some{SplicePair{stream_id, 1n+up_p, 1n+down_p}}
