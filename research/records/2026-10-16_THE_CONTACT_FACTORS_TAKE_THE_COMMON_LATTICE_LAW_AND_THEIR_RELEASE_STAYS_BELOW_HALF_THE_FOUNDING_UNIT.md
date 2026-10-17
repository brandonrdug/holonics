# The contact factors take the common lattice law, and their release stays below half the founding unit

Refs #73 #62. Supersedes the law and cost contract of the section "Exact unresolved contact
material and its existing physical consumer" in
[the October 7 record](2026-10-07_ONE_CURRENT_REACHES_THE_CONTACT_RETURN_AND_THE_RECEIVING_BOUNDARY.md).
Status: reviewed by Epime as a measured candidate (October 16), proposed as the law of these
carriers in #388 and reviewed there (October 17, agent-inferred); its merge commit carries it. The
law is decided by its mathematics: the October 7 reason for the coarse split fails (below), and the
release is bounded below half the founding unit. The MNIST comparison below is a receipt of its
cost, not a gate. v25 and v26 both stay as baselines, and Athena's frozen-objective evaluation
reads this law.

## The law

[definition; agent-inferred, October 16] The C/K/D factor carriers `Factor(0..2)` and their
normalization carriers `FactorScale(0..2)` carry by the one budgeted law of every other carrier
(`HNN/LatticeDeposit.carry`; owner `carried_entry` in `crates/holonics/src/hnn/constitution.rs`):

- `y = Δ + r_old = y_f + e`, with `y_f` the nearest point of the fine lattice `2^(−L−k_m)ℤ`
  (ties upward) and `k_m = 2⌊log₂ m⌋ + 1` at the locus's clock `m`;
- `y_f = q·u + r_new`, `u = 2^(−L)`, `−u/2 ≤ r_new < u/2`;
- the entry moves by `q·u`, `r_new` is carried, and `e` is released, exactly, with
  `|e| ≤ ½·2^(−L−k_m)`.

So `value + r + Σe = value₀ + r₀ + ΣΔ` at every entry, and each remainder is
`ρ·2^(−L−k_m)` with `|ρ| ≤ 2^(k_m−1)`, at most `L + 2k_m + 1` bits.

The October 7 law gave these six carriers one exact coarse split instead,
`Δ + r_old = q·u + r_new`, with no fine release. Its reason was that no admitted-future kernel
certified dropping a physical direction.

## Why the reason does not hold

The history theorems `HNN/LatticeDeposit/Rebase.{history_accounting, history_release_lt,
history_within_founding_unit}` are formal-checked and do not depend on the carrier. Over any
history of deposits and re-bases at one entry:

- the releases since the founding stay within `u₀/2·Σ_(m ≤ clock) 2^(−k_m)`, and so below
  `u₀/2`, half the founding unit;
- the entry stays within `u₀/2 + u/2` of the exact accumulation of the same updates, `u` the
  current unit.

So the exact remainder buys less than half a founding cell of position, over the whole history.
Its cost is unbounded. Its denominator is the lcm of every step `η·G/h′` that reached the
entry, so its bits grow with every deposit, and so does the time of every later deposit.

[Epime's review, October 16] What the bound covers:

- It bounds the representation error of the supplied update history.
- After a re-base it is still a bound in the founding unit. It does not promise accuracy at
  every finer current cell.
- It is not a bound on the trajectory that never-rounded learning would take. A moved
  normalization changes later rates, and a moved C/K/D changes later covectors.

That counterfactual bound is `Objects/CommitRebase`'s `commit_chain_residual`, `Σ K^(n−1−i) r_i`.
It needs a Lipschitz bound `K` of the deposit map, which stays owed in #62, as before this change.
Under both laws an entry moves only by whole lattice units, so the successor's positivity, storage
and inertia checks read entries of the same kind. Only the remainder's carriage differs.

## The October 7 failure this keeps repaired

v80 certified a positive step while all 36 factor displacements, in `[2^-31, 2^-30)`, were
released at clock 1, where the fine half cell was `2^-17`. Under this law that early release is
bounded below `u₀/2` in total, and the same step registers once the clock's fine grid reaches it.
The test `an_early_tiny_factor_step_is_released_then_accumulates_across_a_founding_cell` reads
three histories on `2^(−15)ℤ`, at every factor and normalization carrier.

**Step `1/(3·2^24)`.** It is released whole through clock 31 and registers at clock 32. The entry
moves at deposit 815, where exact accumulation reaches the cell's tie at 768. The releases total
`255635/4194304` of the half unit.

**The same step, with a two-level re-base before deposit 500.** The re-base itself moves the
entry by the finer unit. The releases total `1008531/16777216` of the founding half unit.

**Step `1/(3·2^31)`, v80's order.** It registers at clock 256 and does not move the entry within
3,000 deposits. Its releases total `1005/4194304` of the half unit.

An independent exact simulation of the same law gives the same figures. A step this small still
moves the factor once its accumulation, after the bounded early release, reaches a cell.

## The first reach reads the same law

[definition; agent-inferred, October 16] The finite-decrease landing declares each contact
family's step at its first reach, the least exponent at which some entry with a nonzero update
moves
(`first_reach_scan`, consumed by `Constitution::first_reach` and checked after pass 2 as proposed
reach equal to committed reach). It read the October 7 split, one rounding at the lattice. Under
this law the deposit's applied coordinate is
`q = ⌊(2^k d + r)/u + 1/2 + 2^(−k_m−1)⌋` (`HNN/LatticeDeposit.{quot_fine_eq_floor,
step_coordinate_eq_floor}`), so the scan now takes the deposit's precision `k_m` and reads that
coordinate. At clock 1 the two differ: on `2^(−4)ℤ` the step `2^(−6)` is the fine tie, goes up to
`1/32`, the lattice's tie, and so to `1/16`, one dyadic step before the lattice split alone moves
it.

The scan reads the actual deposit. `k_m` is the precision of the clock that deposit advances the
locus to: its open stroke's, or `k_(m+1)` at clock `m`. `r_i` is that deposit's staged residual
plus the carried remainder.

[proved-derived; Lean owed in #62] The scan stays finite. Let `δ = 2^(−k_m−1)`.

- An entry with `d > 0` reaches exactly when `y/u + 1/2 + δ ≥ 1`. Every admitted remainder meets
  this once `2^k d ≥ u(1 − δ)`; the worst case is `r = −u/2`.
- An entry with `d < 0` reaches exactly when `y/u + 1/2 + δ < 0`. Every remainder `r < u/2`
  meets this once `2^k |d| ≥ u(1 + δ)`, and no smaller bound serves every such remainder. At the
  equality it holds only because `r < u/2` is strict: at `r = u/2` the sum is `0` and `q = 0`.

So `k_max = ⌈log₂(u(1 + δ)/max_i |d_i|)⌉` is the tight sign-independent worst-case endpoint. It
is not the first reach, which the scan finds, and a positive entry can reach below it. The ceiling
is exact. Where the ratio is a power of two, `k_max` is its logarithm, one below the strict
`⌊log₂⌋ + 1` that the coarse `HNN/FiniteDecrease.first_reach_endpoint` (`2^k max_i |d_i| > u`)
takes. The statement owed is this endpoint on the composed floor, with the non-strict coarse
bound as its `k_m → ∞` face.

[Epime's review, October 16] The review confirmed the composed ties-up floor for `k_m ≥ 1` and
named these conditions: the endpoint is the worst case, not the threshold; negative equality rests
on the strict endpoint `r < u/2`; `k_m` and `r_i` match the actual deposit clock; and the endpoint
is an exact ceiling. The test
`the_first_reach_endpoint_is_the_signed_worst_case_at_its_exact_ceiling` reads each condition at
clock 1 on `2^(−4)ℤ`:

- a positive entry `3/64 = u(1 − δ)` at `r = −u/2` reaches at `k = 0`, below the endpoint `1`;
  one part in 4096 less reaches at the endpoint;
- a negative entry `−5/64 = −u(1 + δ)` at `r = u/2 − 2^(−12)`, scanned from `k_cert = −2`,
  reaches at `k = 0`, which is the endpoint, where the strict form names `1`;
- at `r = u/2` that entry's coordinate is `0`, and the scan refuses the remainder.

That remainder also shows a case the endpoint does not need. A remainder in `[u(1/2 − δ), u/2)`
moves its coordinate (`q = +1`) with every update of its own sign, however small, and with an
opposite-sign update no larger than `r − u(1/2 − δ)`. A larger opposite-sign update can cancel
it. The negative step at `k_cert = −10` is that small, so from there the scan ends at once. No
admitted `r` lies there: a carried remainder is on the fine lattice of the locus's clock, so at
most `u/2 − u·2^(−k_m)`, a staged residual is below half a fine unit, `u·2^(−k_m−1)`, and their sum
stays below `u(1/2 − δ)`. The test reads it because the scan's domain is the whole half cell.

[Epime's review of the first final copy, October 16] The deposit skips a zero update
(`Carry::deposit_all`): an entry with `d_i = 0` keeps its coordinate, staged residual and remainder.
The scan read that entry's composed coordinate anyway. So a remainder near `u/2` there, inside the
scan's domain though not one this law carries, claimed a reach the deposit never takes, and in a mixed family it stopped the scan before the
nonzero entry's reach. The scan now reads only `d_i ≠ 0`, and the deposit is unchanged. The test
`a_zero_update_claims_no_reach_from_an_off_grid_remainder` pairs that remainder with `d = 1` at
`r = 0`, which reaches at `2^(−6)`. Epime's test
`factor_first_reach_skips_zero_updates_with_an_off_grid_carry` (inline in `constitution.rs`, since
it reads the staged residuals) checks the deposit against the scan at all six carriers, at the
certified exponent, at the first reach and above it: the zero-update entry, its remainder and its
staged residual are untouched, the moved entries are the ones the scan names, and
`value + r + e = Δ` holds at every nonzero entry.

## A restored remainder is one the law carries

[definition; agent-inferred, October 17; the #388 review] No earlier save format is read or kept:
a state written under the October 7 law is a superseded prototype (THE_MACHINE guard 13). The
continuing-state readers take any exact rational, so `Constitution::continued`, their one consumer,
refuses with `ContinuingState` every restored remainder that is not `ρ·2^(−L−k_m)`,
`−2^(k_m−1) ≤ ρ < 2^(k_m−1)`, at its locus's lattice and the precision of its clock (Lean
`HNN/LatticeDeposit.Carried.{rem_fine, rem_bounded}`). The check covers every carrier, the laws'
map and Gram carries included. A deposit only advances a clock and a re-base only refines a lattice,
so a remainder carried at an earlier clock or on a coarser lattice passes. `carried_entry` then
reads every carried remainder on its fine lattice; the fold it kept for a remainder off that
lattice is deleted.

The test `a_restored_remainder_off_its_fine_lattice_or_half_cell_is_refused` takes the lattice
successor of one storage deposit, whose contact steps are all released at clock 1. Its state
restores exactly. Written with each release as an exact coarse remainder (the October 7 form), it
is refused, and so is the grid point `u/2`, just past the half cell; the grid point `−u/2` restores
and its next deposit runs.

## Measured cost

These figures are from Epime's GSM8K octet listener, a measurement harness built during the
outage and not published here, with the factor law changed by a scratch switch. They are receipts for this change, not a claim that
the two laws agree. Matching code enclosures on a few sections are a measurement on those
sections, not an equivalence. The runs' summary lines and measured receipts are in
[receipts/2026-10-16-contact-factor-lattice](receipts/2026-10-16-contact-factor-lattice/README.md).

**One-place chart, condition B, sections 0 and 1.** The codes are identical at the enclosure under
both laws: `[674,675]` and `[582,583]` bits.

| Reading | Exact coarse law | Common lattice law |
|---|---|---|
| Constitution bits after section 0 | 5,046,369 | 604,684 |
| Constitution bits after section 1 | 9,496,044 | 799,408 |
| Channel(0) remainder bits after section 0 | 2,998,969 | 18,334 |
| Channel(0) remainder bits after section 1 | 5,824,966 | 20,944 |
| Channel(1) remainder bits after section 0 | 1,481,282 | 20,818 |
| Channel(1) remainder bits after section 1 | 2,916,077 | 23,444 |
| Deposit time, section 0 (ns) | 26,614,660,587 | 18,454,514,257 |
| Deposit time, section 1 (ns) | 43,612,161,529 | 17,903,725,862 |

**Place chart, condition B, four sections learned, two unseen sections read, one release.** The
codes are identical at the enclosure in every section, and the release draws the same 119 cells
from the same keys.

| Reading | Exact coarse law | Common lattice law |
|---|---|---|
| Code, sections 0 to 3 (bits) | `[664,665]`, `[558,559]`, `[791,792]`, `[1089,1090]` | the same |
| Code over the 1,494 learned target cells (bits) | `[3103,3104]` | the same |
| Code, unseen sections 4 and 5 (bits) | `[644,645]`, `[832,833]` | the same |
| Release | 59 octets, 1 slip, closed at the end letter | the same draws |
| Constitution bits after section 3 | 35,817,914 | 3,216,663 |
| Channel(0) remainder bits after section 3 | 20,590,163 | 26,774 |
| Channel(1) remainder bits after section 3 | 12,066,039 | 28,952 |
| Deposit time over the four sections (ns) | 993,644,334,839 | 323,237,163,476 |
| Learning time per target cell (ns) | 846,245,296 and `357/1494` | 405,091,356 and `697/1494` |
| Run wall (ns) | 2,438,893,081,416 | 1,813,856,105,307 |
| Peak resident set (KiB) | 90,828 | 69,396 |

The runs' projections were 3,460 s and 2,468 s, with deadlines 3,600 s and 2,500 s; measured over
projected, the walls are `304,861,635,177/432,500,000,000` and
`1,813,856,105,307/2,468,000,000,000`, each below one. The one-place reads had no recorded
projection. Two threads each, run together on the four-core host. The one difference besides cost: the receiving
precision event fell after section 2 under the lattice law (commit 877) and after section 3 under
the exact law (commit 1,495). It changed no code at this enclosure.

**MNIST, 200 learned and 50 development images, on the card** [Epime's measurement, October 16:
the integrated package v26 with this law against v25 with the October 7 law, a fresh matched run,
with GPU parity and checkpoint restoration passing; its summary and receipt lines are in
`mnist-v25-v26.txt` beside the listener's]. Both runs accepted all 200 updates strictly, one
attempt each, with no halvings and no precision refinements. Each had a 1,800 s deadline and no
recorded projection.

| Reading | v25 (exact coarse law) | v26 (common lattice law) |
|---|---|---|
| Checkpoint (bytes) | 4,089,682 | 1,536,990 |
| Constitution logical bits | 12,071,101 | 3,588,354 |
| Resident-state logical bits | 12,451,156 | 3,969,891 |
| Carry rational payload (bits) | 10,141,673 | 1,663,623 |
| of which contact channel 0 | 4,279,220 | 53,442 |
| of which contact channel 1 | 4,308,672 | 53,564 |
| of which source port 0 | 746,984 | 748,521 |
| of which source port 1 | 750,816 | 751,832 |
| of which element 2 | 53,400 | 53,787 |
| of which standing 0 to 2 | 2,581 | 2,477 |
| Model wall (ns) | 797,210,130,278 | 820,376,293,829 |
| Peak host process resident set (KiB) | 427,416 | 410,780 |
| Sampled card memory (MiB) | 456 | 456 |
| Development commits correct | 20 of 50 | 19 of 50 |
| Raw reads correct | 15 of 50 | 17 of 50 |
| Releases correct | 19 | 19 |
| Released (coverage) | 47 | 41 |
| Abstentions | 3 | 9 |

The carry payload is the sum of the bit lengths of each carried rational's numerator and
denominator, without allocator or container overhead. The resident state falls by 8,481,265
logical bits, and the two contact channels' carry payload falls by 8,480,886 bits, from 8,587,892
to 107,006 (`8,587,892 = 80·107,006 + 27,412`). The payload outside the contact channels grows by
2,836 bits, from 1,553,781 to 1,556,617: the two source ports by 2,553, element 2 by 387, and the
standing loci 0 to 2 fall by 104. So the fall is the contact channels' exact rational remainders
under the October 7 law, replaced by remainders on the fine grid. The host process's peak resident
set falls by 16,636 KiB, and the model wall grows by 23,166,163,551 ns.

Here the law compresses storage; it is not a speedup. It changes the learned trajectory and the
release coverage, so both baselines are kept and no equivalence of learning is claimed.

## Tests

All tests are in `crates/holonics/src/hnn/tests/`.

**Replaced:**
- `unresolved_contact_direction_and_normalization_accumulate_without_release` becomes
  `the_contact_factors_carry_signed_tied_cancelled_and_staged_steps_by_the_lattice_law`. It
  covers ties `±u/2`, two steps staged in one deposit and released once, whole sub-fine releases,
  cancellation of a carried remainder, and releases cancelling to the exact accumulation.
- `unresolved_contact_material_is_refused_atomically_at_the_existing_budget` becomes
  `a_contact_factor_successor_past_the_budget_is_refused_atomically`. A sub-fine step is now
  released whole and accepted within the budget. A step whose successor passes the budget is
  refused, with the predecessor unchanged.

**New:**
- `an_early_tiny_factor_step_is_released_then_accumulates_across_a_founding_cell`
- `a_restored_remainder_off_its_fine_lattice_or_half_cell_is_refused`
- `the_first_reach_endpoint_is_the_signed_worst_case_at_its_exact_ceiling`
- `a_zero_update_claims_no_reach_from_an_off_grid_remainder`
- `factor_first_reach_skips_zero_updates_with_an_off_grid_carry` (inline in `constitution.rs`)

**Changed:**
- `a_carried_remainder_takes_its_lattice_and_clock_bits` loses its factor exemption.
- In `finite_decrease.rs`, the carry identity at a declared step reads the release:
  `proposal + r_prior = applied + r_next + e`. The two scan tests take a precision:
  `the_first_reach_is_read_from_the_owner_split_entry_by_entry` keeps its values at clock 2 and
  adds the clock-1 reach at `2^(−6)`, and `a_signed_remainder_moves_the_first_reach_off_the_widest_entry`
  reads at `k_m = 7`, the fine lattice its remainder `31/1024` lies on.
- `an_admission_binds_its_own_cut_by_equality` builds its different `θ′` at the first reach. A
  certified step one exponent lower no longer differs: like the certified step itself, it is
  released whole.
- `the_actual_unresolved_contact_return_survives_a_different_physical_passage` reads the factor
  remainders on their fine grid and the releases within half a fine unit, in place of "no factor
  release".
- `reached_contact_storage_reacts_together_and_reenters_on_actual_support`
  (`hnn/reference/continuation.rs`) asserted that some reached C moved at its first deposit. That
  was the October 7 law's consequence. At this deposit, at clock 1, it now reads that both
  contacts' C are unmoved named rounding refusals (`DepositReading::vanished`), and that every
  entry each C step updated is carried as unresolved contact material or released. The rest of the
  test holds unchanged: the reached motion opens at the receiving ring, and the storage statistic
  carries the early slip.

**Unchanged and re-run:** the successor positivity, storage-range and budget refusals.

The verification receipts of the commit that lands (gate 1, the library tests and the GPU suite on
a card) are in #388, one per step in its PR as the guide asks. Lean is unchanged.

## Owners and documents changed

- `carried_entry` loses its factor branch, its carrier argument and its fold of a remainder off the
  fine lattice; `Constitution::continued` refuses a restored remainder that is not one the law
  carries.
- `first_reach_scan` takes the deposit's precision and reads the composed coordinate, with the
  endpoint above; `Constitution::first_reach` passes the precision of the deposit that advances
  the channel's clock. The atlas row `hnn.first-reach-split` is rewritten and graded
  proved-derived until its endpoint is in Lean.
- The `Carry`, `BudgetedCarry`, `released`, `DepositReading` and module documentation now state
  one law.
- The atlas rows `hnn.lattice-deposit` and `hnn.unresolved-contact-material` are rewritten, the
  latter now specializing the former.
- Lean is unchanged: the law is `HNN/LatticeDeposit` and its `Rebase` history, already
  formal-checked at every carrier. One #62 obligation is added, the first reach's endpoint on the
  composed floor. `commit_chain_residual`'s `K` remains owed there.
