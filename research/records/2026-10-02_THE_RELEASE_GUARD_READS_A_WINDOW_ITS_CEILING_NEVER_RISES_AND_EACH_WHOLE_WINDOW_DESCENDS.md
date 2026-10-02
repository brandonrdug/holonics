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

## 5. Verification

- `lake build Holonics.HNN.ExecutedComparison` builds with no `sorry`; its audit block prints the
  axioms of the twelve new theorems (`propext`, `Classical.choice`, `Quot.sound`).
- `cargo check --workspace --all-targets` is clean.
- `hnn::tests::executed::the_release_window_of_one_is_the_strict_decrease_and_a_longer_window_admits_a_bounded_rise`
  passes. It checks that the window of one agrees with the former rule on seven enclosures, and that
  a longer window admits a rise below an earlier lower end and refuses one at or above it. It also
  checks that the margin takes its share of the certified descent.
