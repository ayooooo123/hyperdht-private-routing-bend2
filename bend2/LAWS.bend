import Base
import ./routing.bend as R

# ============================================================================
# LAWS.bend — Mathematical Privacy & Routing Laws for Master's Forge
# ============================================================================
# Every law here is an iron strap around the routing core; PROOF.bend must
# satisfy every single one before the compiler lets the build cum.
# ============================================================================

# LAW 1 (No-Direct-UDP / Post-Guard-Pinning Send Authority):
# Once collared in EpPinned{guard_addr, route_ready}, no event can EVER make
# her leak a packet to any address other than `guard_addr`.
law post_pin_never_sends_direct:
  for +guard_addr: Nat
  for route_ready: Bool
  for event: R.RouteEvent
  {R.OutboundAction.targets_only(
    Pair.snd(
      R.EndpointState,
      R.OutboundAction,
      R.endpoint_step(R.EpPinned{guard_addr, route_ready}, event)
    ),
    guard_addr
  ) == True{} : Bool}

# LAW 2 (Fail-Closed Route Failure):
# Even if a route failure dangles a tempting fallback_direct_addr in her face,
# she disables route_ready and clamps shut with ActDropFailClosed{}.
law route_failure_never_dials_fallback:
  for guard_addr: Nat
  for route_ready: Bool
  for fallback_direct_addr: Nat
  {R.endpoint_step(
    R.EpPinned{guard_addr, route_ready},
    R.EvRouteFailed{fallback_direct_addr}
  ) == (R.EpPinned{guard_addr, False{}}, R.ActDropFailClosed{}) : R.EndpointState & R.OutboundAction}

# LAW 3 (Fail-Closed Suspension):
# While suspended on the leash, she drops every outbound action fail-closed.
law suspended_always_drops:
  for guard_addr: Nat
  for event: R.RouteEvent
  {Pair.snd(
    R.EndpointState,
    R.OutboundAction,
    R.endpoint_step(R.EpSuspended{guard_addr}, event)
  ) == R.ActDropFailClosed{} : R.OutboundAction}

# LAW 4 (Fail-Closed Destruction):
# Once destroyed, she stays spent and drops every event fail-closed.
law destroyed_always_drops:
  for event: R.RouteEvent
  {R.endpoint_step(R.EpDestroyed{}, event) == (R.EpDestroyed{}, R.ActDropFailClosed{}) : R.EndpointState & R.OutboundAction}

# LAW 5 (Gate E6 — Primary Guard Precedence):
# As long as the primary pinned guard is wet and reachable, she picks it first.
law primary_guard_selected_when_reachable:
  for p_id: Nat
  for alt1: R.GuardSlot
  for alt2: R.GuardSlot
  {R.PinnedGuardSet.first_reachable(
    R.GuardSet{R.GuardSlot{p_id, True{}}, alt1, alt2}
  ) == Some{p_id} : Maybe<&2, Nat>}

# LAW 6 (Gate E6 — Non-Primary Failure Never Demotes Primary Guard):
# An alternate guard choking never knocks the primary guard off its throne.
law non_primary_failure_preserves_primary:
  for p_id: Nat
  for p_reach: Bool
  for +alt1: R.GuardSlot
  for +alt2: R.GuardSlot
  for +failed_id: Nat
  {R.PinnedGuardSet.primary_id(
    R.PinnedGuardSet.failed_branch(p_id, p_reach, alt1, alt2, failed_id, False{})
  ) == p_id : Nat}

# LAW 7 (Gate E6 — Primary Failure Promotes First Alternate):
# When the primary guard itself fails, alt1 steps straight into the primary slot.
law primary_failure_promotes_first_alternate:
  for p_id: Nat
  for p_reach: Bool
  for +alt1: R.GuardSlot
  for alt2: R.GuardSlot
  for +failed_id: Nat
  {R.PinnedGuardSet.primary_id(
    R.PinnedGuardSet.failed_branch(p_id, p_reach, alt1, alt2, failed_id, True{})
  ) == R.GuardSlot.id(alt1) : Nat}

# LAW 8 (4-Hop Diversity Gate Refusal):
# When 4-hop pairwise disjointness fails, `admit_route4_gate` returns None{}.
law non_diverse_4hop_rejected:
  for s1: R.Hop
  for s2: R.Hop
  for entry: R.Hop
  for guard: R.Hop
  {R.admit_route4_gate(s1, s2, entry, guard, False{}) == None{} : Maybe<&2, R.VerifiedRoute4>}

# LAW 9 (IPv4 Loopback Rejection in Public Mode):
# When allow_loopback is False, 127.x.x.x loopback addresses are rejected cold.
law ipv4_loopback_rejected_when_disallowed:
  for +b0: Nat
  for +b1: Nat
  for +b2: Nat
  for +b3: Nat
  for +port: Nat
  {R.classify_ipv4_loopback(b0, b1, b2, b3, port, False{}) == None{} : Maybe<&2, R.DiversityKey>}

# LAW 10 (Refresh Without Drop — Admitted Streams Preserved on Circuit Retire):
# Retiring an old descriptor's circuit keeps every admitted stream intact.
law retire_preserves_admitted_streams:
  for +c: R.CircuitState
  {R.CircuitState.streams(R.CircuitState.retire(c)) == R.CircuitState.streams(c) : List<&2, Nat>}

# LAW 11 (Retired Circuit Blocks New Admissions):
# Once retired on rotation, a circuit refuses any fresh stream open.
law retire_blocks_new_admissions:
  for c: R.CircuitState
  {R.CircuitState.can_admit(R.CircuitState.retire(c)) == False{} : Bool}

# LAW 12 (Gate E4 — Monotone Descriptor Sequence Strict Advance):
# Every new descriptor sequence number strictly exceeds max(prev_seq, remote_seq).
law descriptor_seq_strictly_advances:
  for +prev_seq: Nat
  for +remote_seq: Nat
  for +now: Nat
  {Nat.is_gt(
    R.next_descriptor_seq(prev_seq, remote_seq, now),
    Nat.max(prev_seq, remote_seq)
  ) == True{} : Bool}

# LAW 13 (4-Hop UDX relayTo Splicing Rejects Zero Stream IDs):
# Neither upstream nor downstream UDX splice stream ID may ever be 0.
law splice_rejects_zero_upstream_id:
  for stream_id: Nat
  for down_udx_id: Nat
  {R.admit_splice_pair(stream_id, 0n, down_udx_id) == None{} : Maybe<&2, R.SplicePair>}

law splice_rejects_zero_downstream_id:
  for stream_id: Nat
  for up_udx_id: Nat
  {R.admit_splice_pair(stream_id, up_udx_id, 0n) == None{} : Maybe<&2, R.SplicePair>}

# LAW 14 (4-Hop UDX Splicing Adjacent-Hop Firewall Soundness):
# Packets arriving from the exact pinned adjacent hop (host, port) pass through.
law splice_firewall_refl:
  for +host: Nat
  for +port: Nat
  {R.splice_firewall_allow(host, port, host, port) == True{} : Bool}

# LAW 15 (Soundness of 4-Hop Route Admission):
# Any route admitted as Some{r} by `admit_route4` is proven 4-hop diverse.
law admitted_route4_is_diverse:
  for +s1: R.Hop
  for +s2: R.Hop
  for +entry: R.Hop
  for +guard: R.Hop
  for r: R.VerifiedRoute4
  for eq: {R.admit_route4(s1, s2, entry, guard) == Some{r} : Maybe<&2, R.VerifiedRoute4>}
  {R.pairwise_disjoint4(s1, s2, entry, guard) == True{} : Bool}

# LAW 16 (Soundness of 4-Hop UDX Splice Pair Admission):
# Any SplicePair admitted as Some{pair} has strictly positive UDX IDs on both sides.
law admitted_splice_pair_nonzero:
  for stream_id: Nat
  for +up_id: Nat
  for +down_id: Nat
  for pair: R.SplicePair
  for eq: {R.admit_splice_pair(stream_id, up_id, down_id) == Some{pair} : Maybe<&2, R.SplicePair>}
  {Bool.and(Nat.is_gt(up_id, 0n), Nat.is_gt(down_id, 0n)) == True{} : Bool}
