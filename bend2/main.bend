import Base
import ./routing.bend as R

def route_to_count(m: Maybe<&2, R.VerifiedRoute4>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{_}:
      1n

# Splits the 4-hop route verification tree across every BendRT core (`a b = ...`)
# so 2^depth candidate circuits get checked in parallel and folded back wet.
def count_admitted_routes(+depth: Nat, +seed: Nat) -> Nat:
  match depth:
    case 0n:
      route_to_count(
        R.admit_route4(
          R.Hop{Nat.add(seed, 1n), R.DivIPv4{Nat.add(seed, 65793n)}},
          R.Hop{Nat.add(seed, 2n), R.DivIPv4{Nat.add(seed, 131586n)}},
          R.Hop{Nat.add(seed, 3n), R.DivIPv4{Nat.add(seed, 197379n)}},
          R.Hop{Nat.add(seed, 4n), R.DivIPv4{Nat.add(seed, 263172n)}}
        )
      )
    case 1n+p:
      +left_seed = Nat.mul(seed, 2n)
      +right_seed = Nat.add(left_seed, 1n)
      # Parallel fork-join across BendRT worker lanes
      a b = count_admitted_routes(p, left_seed) count_admitted_routes(p, right_seed)
      Nat.add(a, b)

def main() -> IO(Unit):
  do IO<Unit>:
    # 1. Parallel fork-join 4-hop route admission check (2^10 = 1024 candidate 4-hop circuits)
    admitted : Nat = count_admitted_routes(10n, 1n)
    # 2. Verify fail-closed post-pin routing when route fails with a hostile fallback address
    step_res : R.EndpointState & R.OutboundAction = R.endpoint_step(
      R.EpPinned{9001n, True{}},
      R.EvRouteFailed{6666n}
    )
    act : R.OutboundAction = Pair.snd(R.EndpointState, R.OutboundAction, step_res)
    safe : Bool = R.OutboundAction.targets_only(act, 9001n)
    # 3. Verify Gate E4 monotone descriptor sequence advance
    seq : Nat = R.next_descriptor_seq(100n, 250n, 200n)
    IO.print(
      "BendRT parallel 4-hop circuits admitted: " ++ Nat.show(admitted) ++
      " | fail-closed guard-only: " ++ Bool.show(safe) ++
      " | E4 next seq: " ++ Nat.show(seq)
    )
