import Base
import ./routing.bend as R
import ./LAWS.bend as Laws

# ============================================================================
# PROOF.bend — Machine-Checked Proofs Laid Wet at Master's Feet
# ============================================================================

# Helper Lemma 1: Every Nat equals itself when licked clean by Nat.is_eq
law nat_eq_refl:
  for +n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def nat_eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

# Helper Lemma 2: Stepping to 1n + b always stretches past b
law nat_succ_gt:
  for +b: Nat
  {Nat.is_gt(1n+b, b) == True{} : Bool}

def nat_succ_gt(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      nat_succ_gt(p)

# Helper Lemma 3: Bool.and(a, True{}) reduces straight to a
law bool_and_true_r:
  for a: Bool
  {Bool.and(a, True{}) == a : Bool}

def bool_and_true_r(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Helper Lemma 4: Whichever branch next_descriptor_seq_pick takes, it beats b
law seq_pick_gt_branch:
  for +b: Nat
  for +n: Nat
  for gt: Bool
  for eq: {Nat.is_gt(n, b) == gt : Bool}
  {Nat.is_gt(R.next_descriptor_seq_pick(b, n, gt), b) == True{} : Bool}

def seq_pick_gt_branch(b, n, gt, eq):
  match gt:
    case True{}:
      eq
    case False{}:
      nat_succ_gt(b)

# Proof of LAW 1: post_pin_never_sends_direct
def Laws.post_pin_never_sends_direct(guard_addr, route_ready, event):
  match route_ready event:
    case True{} R.EvSendPayload{_}:
      nat_eq_refl(guard_addr)
    case True{} R.EvRouteFailed{_}:
      {==}
    case True{} R.EvRouteExpired{_}:
      {==}
    case True{} R.EvRouteRecovered{}:
      {==}
    case True{} R.EvSuspend{}:
      {==}
    case True{} R.EvResume{}:
      {==}
    case True{} R.EvDestroy{}:
      {==}
    case False{} R.EvSendPayload{_}:
      {==}
    case False{} R.EvRouteFailed{_}:
      {==}
    case False{} R.EvRouteExpired{_}:
      {==}
    case False{} R.EvRouteRecovered{}:
      {==}
    case False{} R.EvSuspend{}:
      {==}
    case False{} R.EvResume{}:
      {==}
    case False{} R.EvDestroy{}:
      {==}

# Proof of LAW 2: route_failure_never_dials_fallback
def Laws.route_failure_never_dials_fallback(guard_addr, route_ready, fallback_direct_addr):
  match route_ready:
    case True{}:
      {==}
    case False{}:
      {==}

# Proof of LAW 3: suspended_always_drops
def Laws.suspended_always_drops(guard_addr, event):
  match event:
    case R.EvSendPayload{_}:
      {==}
    case R.EvRouteFailed{_}:
      {==}
    case R.EvRouteExpired{_}:
      {==}
    case R.EvRouteRecovered{}:
      {==}
    case R.EvSuspend{}:
      {==}
    case R.EvResume{}:
      {==}
    case R.EvDestroy{}:
      {==}

# Proof of LAW 4: destroyed_always_drops
def Laws.destroyed_always_drops(event):
  match event:
    case R.EvSendPayload{_}:
      {==}
    case R.EvRouteFailed{_}:
      {==}
    case R.EvRouteExpired{_}:
      {==}
    case R.EvRouteRecovered{}:
      {==}
    case R.EvSuspend{}:
      {==}
    case R.EvResume{}:
      {==}
    case R.EvDestroy{}:
      {==}

# Proof of LAW 5: primary_guard_selected_when_reachable
def Laws.primary_guard_selected_when_reachable(p_id, alt1, alt2):
  {==}

# Proof of LAW 6: non_primary_failure_preserves_primary
def Laws.non_primary_failure_preserves_primary(p_id, p_reach, alt1, alt2, failed_id):
  {==}

# Proof of LAW 7: primary_failure_promotes_first_alternate
def Laws.primary_failure_promotes_first_alternate(p_id, p_reach, alt1, alt2, failed_id):
  match alt1:
    case R.GuardSlot{id1, r1}:
      {==}

# Proof of LAW 8: non_diverse_4hop_rejected
def Laws.non_diverse_4hop_rejected(s1, s2, entry, guard):
  {==}

# Proof of LAW 9: ipv4_loopback_rejected_when_disallowed
def Laws.ipv4_loopback_rejected_when_disallowed(b0, b1, b2, b3, port):
  {==}

# Proof of LAW 10: retire_preserves_admitted_streams
def Laws.retire_preserves_admitted_streams(c):
  match c:
    case R.CircuitState{closed, retired, last_id, streams}:
      {==}

# Proof of LAW 11: retire_blocks_new_admissions
def Laws.retire_blocks_new_admissions(c):
  match c:
    case R.CircuitState{closed, retired, last_id, streams}:
      match closed:
        case True{}:
          {==}
        case False{}:
          {==}

# Proof of LAW 12: descriptor_seq_strictly_advances
def Laws.descriptor_seq_strictly_advances(prev_seq, remote_seq, now):
  +base = Nat.max(prev_seq, remote_seq)
  seq_pick_gt_branch(base, now, Nat.is_gt(now, base), {==})

# Proof of LAW 13a: splice_rejects_zero_upstream_id
def Laws.splice_rejects_zero_upstream_id(stream_id, down_udx_id):
  {==}

# Proof of LAW 13b: splice_rejects_zero_downstream_id
def Laws.splice_rejects_zero_downstream_id(stream_id, up_udx_id):
  match up_udx_id:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Proof of LAW 14: splice_firewall_refl
def Laws.splice_firewall_refl(host, port):
  match host:
    case 0n:
      nat_eq_refl(port)
    case 1n+hp:
      Laws.splice_firewall_refl(hp, port)

# Dependent motive crushing impossible None{} == Some{r} branches into Empty
def Maybe.is_some_type(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{_}:
      Unit

def absurd(-B: Type, e: Empty) -> B:
  match e:

def none_eq_some_to_empty(
  -A: Data,
  r: A,
  eq: {None{} == Some{r} : Maybe<&2, A>}
) -> Empty:
  sym = Equal.sym(Maybe<&2, A>, None{}, Some{r}, eq)
  %sym : Maybe.is_some_type(A, _)
  Unit{}

def refute_none_eq_some(
  -A: Data,
  -B: Type,
  r: A,
  eq: {None{} == Some{r} : Maybe<&2, A>}
) -> B:
  absurd(B, none_eq_some_to_empty(A, r, eq))

law admit_gate_sound:
  for s1: R.Hop
  for s2: R.Hop
  for entry: R.Hop
  for guard: R.Hop
  for ok: Bool
  for r: R.VerifiedRoute4
  for eq: {R.admit_route4_gate(s1, s2, entry, guard, ok) == Some{r} : Maybe<&2, R.VerifiedRoute4>}
  {ok == True{} : Bool}

def admit_gate_sound(s1, s2, entry, guard, ok, r, eq):
  match ok:
    case True{}:
      {==}
    case False{}:
      refute_none_eq_some(R.VerifiedRoute4, {False{} == True{} : Bool}, r, eq)

# Proof of LAW 15: admitted_route4_is_diverse
def Laws.admitted_route4_is_diverse(s1, s2, entry, guard, r, eq):
  admit_gate_sound(s1, s2, entry, guard, R.pairwise_disjoint4(s1, s2, entry, guard), r, eq)

# Proof of LAW 16: admitted_splice_pair_nonzero
def Laws.admitted_splice_pair_nonzero(stream_id, up_id, down_id, pair, eq):
  match up_id down_id:
    case 0n _:
      refute_none_eq_some(R.SplicePair, {False{} == True{} : Bool}, pair, eq)
    case 1n+_ 0n:
      refute_none_eq_some(R.SplicePair, {False{} == True{} : Bool}, pair, eq)
    case 1n+_ 1n+_:
      {==}
