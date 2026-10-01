# The reading and the two legs: does every refinement ask for the lower transport, and does `E` descend alone at the founded modulus? (pinned before their run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the question and the rules; [measured] only in the receipt. Read-only.

## 1. The fork

The [modulus's slope](2026-10-01_THE_MODULUS_SLOPE_MEASURED_THE_NATIVE_COMPARISON_ASKS_FOR_THE_HIGHER_TRANSPORT_UNTIL_E_READS_THE_RULE.md)
found that gate A's comparison (the lock face at the decisions) asks for the higher transport
wherever gate A stood, and for the lower only where `E` already reads the rule. The float refit that
works descended a different reading: every open station at every refinement of its own release.
Gate B's `lock-all` arm is that reading's native form, and it was built but never run. Two
questions decide what the next native procedure changes.

- **(X) the reading.** At the founded opening and at gate A's constitution 1, what sign does
  `lock-all`'s `γ_ρ` take?
  - If positive at both, the decisions reading is what hides the lower transport. The next loop is
    gate A's witness procedure under `lock-all`, unchanged otherwise.
  - If negative at either, both readings share the sign obstruction, and the reading is not its
    cause.
- **(Y) the legs.** The segment probe read the joint chord. Here its two legs are read under gate
  A's comparison:
  - the `E`-leg at `ρ₀`: `E₀ + s(E* − E₀)` for `s = 1/4, 1/2, 3/4`;
  - the `ρ`-leg at `E*`: `ρ₀ + (1/2)(ρ* − ρ₀)`.

  The endpoints are known: `L` of `[500197/4096, …)` at `Θ₀`, `[310210/4096, …)` at `(E*, ρ₀)` and
  `[133292/4096, …)` at `Θ*`.
  - If `L` falls strictly along the `E`-leg (by disjoint enclosures), a descent in `E` alone at the
    founded modulus reaches a constitution below every one gate A's moves reached, where the slope
    in `ρ` already points down. The native move did not follow it, which locates the failure in
    `E`'s path (its direction or its step).
  - If `L` rises somewhere on the `E`-leg, the class preference gate A found is separated from `E*`
    at `ρ₀`. The modulus must then move with `E`, and only the joint chord is known to descend.
  - Each point also reports `γ_ρ`, which shows where along the `E`-leg the slope in `ρ` turns down.

## 2. The reads

- **(Y)**: `read_probe.sh <out>/legs 83271 334 executed rho-slopes order2 2026093061 8 lock-dec` with
  the sources `e-1/4`, `e-1/2`, `e-3/4` (`opening+<refit>@102837/131072:s`) and `rho-1/2`
  (`<refit>@1372988/2097152`). Projection: `4 · 83,271 = 333,084` ms.
- **(X)**: `read_probe.sh <out>/all 374720 750 executed rho-slopes order2 2026093061 8 lock-all` with
  `opening` and `gateA-c1`.
  - No `lock-all` incumbent read has been measured. Its unit is projected from the measured
    `lock-dec` unit (83,271 ms) by the ratio of covector reads: every candidate at every refinement,
    180 a request, against five at each decision, 40 a request. That gives `9/2 · 83,271 = 374,720`
    ms (rounded up) a constitution, and `749,440` ms for two.
  - If the first read passes 374,720 ms, the run stops there incomplete, and the projection error is
    reported.
- (Y) runs first, then (X), one after the other at 19 threads: each read already fills the threads.
- **The failures this could repeat**: 9 (fixed deadlines, nothing raised), 7 (no count here is
  progress), 3 (no consumer is built).
