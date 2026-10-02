# The release guard reads a window: its ceiling never rises, and each whole window descends

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for §1–§3 (`HNN/ExecutedComparison` §12); [definition] for §4's Rust owner;
[agent-inferred] where marked. No run.

The refit's ablation located no optimizer ingredient: plain gradient steps reach as many held-out
sections as `adam` or `rms` (the main line's ablation record, against the baseline of
[the native move at `E` alone](2026-10-02_THE_NATIVE_MOVE_AT_E_ALONE_ITS_FIXED_POINTS_AND_ONE_STEPS_REACH.md)). The candidate left is the guard. The native chain's eighth move was
refused with its solve converged: the larger trials lowered the fixed mask but raised the machine's
own release (`OwnNotBelow`). The exterior arms accept every step whatever it does to the comparison,
and along their path the comparison rises before it falls. This record states the guard that admits
such a rise and what it still certifies. It replaces the release guard's rule in its owner; it is not
a second guard.

## 1. The rule

Let `f k` be the own release's executed comparison at the `k`-th adopted state. The windowed guard
adopts a successor when

  `f (k+1) ≤ windowMax f w k − σ k`,  `windowMax f w k = max_(k−w ≤ j ≤ k) f j`,

with `σ k ≥ 0` a certified decrease. The window's length `w + 1` and the decreases `σ` are
parameters, set from the main line's measurement of how far and for how long the plain-gradient
path's comparison rises.

- **The window of one is today's guard** (`windowGuard_zero_iff`): `w = 0` reads the incumbent alone.
- **The check on enclosures is sound** (`window_enclosures_guard`): with every adopted comparison
  enclosed below by `lo j` and the successor's above by `U`, `U < windowMax lo w k − σ` certifies the
  guard strictly. With `w = 0` and `σ = 0` it is the disjoint-enclosure decrease (§4 of the module).
- **Rest points are unchanged.** The guard only adopts or refuses a metric's step. Where a step can
  rest is §9's `metric_step_zero_iff`: the stationary points of `L`.

## 2. What a window certifies

With every `σ k ≥ 0`:
- **The ceiling never rises** (`windowMax_succ_le`, `windowMax_antitone`). So **no adopted comparison
  exceeds the opening's** (`le_start`): the guard admits a rise inside the window, never above its
  first ceiling `f 0`.
- **Each whole window descends** (`windowMax_block`): over the `w + 1` steps from `k`, if every
  certified decrease is at least `s`, then `windowMax f w (k + w + 1) ≤ windowMax f w k − s`.
- **The windows' decreases are summable** (`windowMax_blocks`, `blocks_sum_le`): with `s b` a lower
  bound of the decreases in the `b`-th window and a floor `m ≤ f`, `Σ_(b<n) s b ≤ f 0 − m` for every
  `n`. **Few windows certify much** (`large_blocks_card`): at most `(f 0 − m)/ε` of them certify `ε`
  or more.

## 3. The schedule's condition

Let each window's decrease be `s b = η b · q b`, with `η b ≥ 0` the window's step and `q b ≥ 0` its
least certified first-order slope. `schedule_frequently_small`: if the decreases sum below `C` and
the steps' partial sums pass every bound, then for every `ε > 0` and every `N` some window `b ≥ N`
has `q b < ε`. **A divergent step sum is what the certificate needs**, the Robbins–Monro half of the
classical schedule. A summable step sum certifies nothing about the slope. The other half (squares
summable) is not needed here: the guard, not the step's size, bounds the excursion.

## 4. The rule in its owner

`hnn::executed::ReleaseWindow` carries `earlier` (the lower ends of the earlier adopted comparisons,
supplied by the chain) and `margin`. The ladder's `OwnNotBelow` branch now reads
`ReleaseWindow::admits`:

  `own.upper < max(before.lower, earlier…) − margin · (−slope.upper)`,

where `slope` is the carried move's certified first-order bound. So `σ k` is `margin` times the
certified first-order descent. `executed_move_in` passes `ReleaseWindow::one()`, which is exactly the
former rule. `executed_move_windowed` takes the chain's window. The fixed mask's strict decrease
(`NotBelow`) is unchanged.

What the parameters must satisfy:
- `margin ≥ 0` for §2's first two results;
- `margin > 0` for the windows' summed first-order descents to be bounded (§2, `blocks_sum_le`);
- `w + 1` at least the number of steps the measured rise lasts, and the rise's peak below the
  window's ceiling. [agent-inferred] By `le_start`, a path whose comparison rises above the opening's
  is refused by every window. If the main line measures such a rise, the rule this record proves does
  not admit it, and the guard's law must then carry an excursion above its checkpoint.

## 5. The chain's own schedules: none is summable

§3's condition is a divergent step sum. The question is whether a step schedule the native chain
already uses has a finite sum, which would make §3's guarantee void for the chain as built. Each
schedule, read from its owner:

1. **The committed move of `E` (the ladder).** It declares no decaying schedule. Each move starts at
   `power_below(min(excess/|slope|, ½/U_k))` (`ladder_start`), with `U_k` the unit move's largest
   entry, and halves at most seven times (`LADDER_DEPTH`). A rung is refused before it is read when
   `η · U_k · 2 < u`, with `u` the source port's lattice unit. So **every adopted step moves at least
   one lattice coordinate**: `η_k ≥ u/(2 U_k)`. With `U_k ≤ Ū` (a bounded unit move), every adopted
   step is at least `c = u/(2Ū) > 0`, and `floor_steps_diverge` gives `Σ η = ∞` along any chain that
   keeps adopting.
2. **The normal law's deposits.** The step is `ΔW = η Σ w g (H′⁻¹ f)ᵀ`, with the carried Gram
   `H′ = I + Σ w f fᵀ` within one unit of the exact statistic (constitution module, "the carried
   Gram"). With each return's feature energy at most `F`, `‖H′‖ ≤ 1 + mF` after `m` deposits. The
   metric step is then at least `1/(1 + mF)` along every direction, a harmonic lower bound, so its
   sum diverges. The certified step `η` (the largest `2^k` with `ηC ≤ a` and `ηc ≤ 1`) does not shrink
   with `H′`. `a` is linear in the unit step `D` and `C` quadratic, so `a/C` grows as `D` shrinks,
   and the cap `ηc ≤ 1` reads the covector, not `D`. The factor families' unit step
   `D = G_x/h_x′` with `h_x′ = h_x + e` has the same harmonic bound.
3. **The `1/m²` of the contact freeze is not a step size.** It is the fine lattice's cell,
   `2^(−k_m)` with `k_m = 2⌊log₂ m⌋ + 1`, below which a deposit's residual is released. Its Kraft sum
   bounds what rounding drops in total (`release_bounded_since_founding`). It does not scale any
   step: the remainder above the cell is carried, and the applied quotient is the update's own.
4. **The ladder's rungs** are dyadic within one move. They select the step and reset at the next
   move, so they are not a schedule across moves.

[proved-derived for the arithmetic; agent-inferred for the bounds `U_k ≤ Ū` and `F`, read from the
owners and not measured] **So no step schedule the native chain uses is summable, and §3's
condition holds for every chain that keeps adopting.** Under the step floor the guarantee is stronger
than §3's (`floor_large_slopes_card`). With `σ k ≥ c · q` (a positive margin times the floor step),
at most `(f 0 − m)/(c ε)` windows have least slope `ε` or more. So the slope falls below every `ε` in
all but finitely many windows.

**What the stall is, then.** The native move does not stall because its steps shrink. It stalls
because they cannot shrink below the floor. Along a ray with curvature at most `K`, a step `η`
along a direction of slope `−q` lowers `f` by at least `η q − ½ K η² |d|²`. That is positive only
while `q > ½ K η |d|²`. At the floor `η ≥ c`, near a point whose slope is below `½ K c |d|²`, every
rung's step can be too large to descend. The ladder then refuses at every rung: on the comparison
(`NotBelow`, `OwnNotBelow`) for the larger rungs, or on the lattice (`Guards`) once a rung moves no
coordinate. [agent-inferred] The guard needs no declared schedule. Its divergent step sum is
supplied by the lattice floor, and the floor in turn sets the slope at which the chain must stop.
That slope is about `K u Ū/4`, which only a finer source lattice lowers. The lattice rule already
refines a locus as its Gram grows (`L_s = D_ℓ + ⌈log₂ n⌉ + ⌈log₂ ‖H′‖∞⌉ + 2`). Whether the source
port's `u` follows that rule during the move chain is the read that separates the two causes:
- If the kinetic chain's terminal refusals are `Guards` with the slope at `K u Ū/4`, the stall is the
  lattice floor.
- If they are `OwnNotBelow` with the slope well above it, as at move 8 of the kinetic chain, the
  stall is the guard, and §1–§4's window is the remedy.

## 6. Verification

- `lake build Holonics.HNN.ExecutedComparison` builds with no `sorry`; its audit block prints the
  axioms of the fourteen new theorems (`propext`, `Classical.choice`, `Quot.sound`).
- `cargo check --workspace --all-targets` is clean.
- `hnn::tests::executed::the_release_window_of_one_is_the_strict_decrease_and_a_longer_window_admits_a_bounded_rise`
  passes. It checks that the window of one agrees with the former rule on seven enclosures, and that
  a longer window admits a rise below an earlier lower end and refuses one at or above it. It also
  checks that the margin takes its share of the certified descent.
