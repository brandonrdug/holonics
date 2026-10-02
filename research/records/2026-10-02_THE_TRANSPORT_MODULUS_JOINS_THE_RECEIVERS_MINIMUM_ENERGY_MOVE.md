# The transport modulus joins the receiver's minimum-energy move

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [derived] for the
admissible set's upper bound and the bound-active rule (§1, §4); [definition; agent-inferred] for the
joined move and its mass (§2, §3); [proved-derived; implemented-exact] for the solve's tests (§6).
No run: the main line measures it (§7).

**Occasion.** The native chain moves `E` by the receiver's minimum-energy move (`MoveMetric::Kinetic`)
and holds the source navigator's transport modulus `ρ` at its founding `ρ₀ = 102837/131072` on every
move. The exported refit stands at `ρ* = 137573/262144`, and with the refit's `E` every step of `ρ`
from `ρ₀` toward `ρ*` lowers the comparison and raises solved, right and whole sections together
([the representation](2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)).
The question put to this record: who founds `ρ`, whether its value is derived or chosen, whether the
comparison has a gradient in it, and what law moves it.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the tube**
(the passage's transport and its reach) and **faces and placement** (each datum's weight read from
its station). The helix, the pair, the cell holonomy and the tower thread stay attached: nothing here
changes a phase, a contact or a restriction.

## 0. The recorded failures this could repeat

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **Tuning a constant instead of deriving a law.** `ρ` is not chosen from a run. It moves by the
  same Gauss–Newton change of the readings that moves `E`, and the storage-change mass splits that
  change between them (§2).
- **2, an authored cut of the data.** A short reach weighs old data below the chart's grain. No
  datum's exact weight reaches zero (§1), and the reach is located by the move, not declared.
- **5, an uncertified step.** Every trial is certified whole by the same commit conditions (the
  entry bound, the first order on the joint move, the fixed mask's strict decrease, the release's
  excursion). Only the direction and `ρ`'s upper bound are new.
- **4, a located cause carried unrepaired.** The located cause (the kinetic move's declaration that
  `ρ` is held) is repaired in its owner, `hnn::executed`.

## 1. Who founds `ρ`, and what is derived

[derived; from `hnn::constitution`] `Constitution::founding_transport` founds it, with
`founding_modulus` and Lean `HNN/IndexedOpen.IsFounding`. `founded_transport` sets it as the executed
comparison's opening.

- **Derived: an upper bound.** The phase record identifies a datum's age only within one turn, so a
  datum one turn old aliases onto the present phase at weight `ρ^d` (`framed_weight_ratio`).
  Requiring that alias to be at most one unit of the weights' chart gives `ρ^d ≤ 2^(−L_ν)`. With the
  ring's period `d = 60` and the population chart `L_ν = 21`, this is `ρ^60 ≤ 2^(−21)`. Above that
  bound the record weighs a one-turn-old datum as part of the present at a weight the chart resolves,
  which places the datum at the wrong age.
- **Chosen: the opening at the top.** `ρ₀` is the greatest lattice modulus under that bound. Its doc
  calls it "least dissipative", graded agent-inferred. Every modulus below it meets the same bound:
  `ρ*` already has `ρ*^23 ≤ 2^(−21)`. The founding derives an admissible set and opens at its top;
  nothing derives that `ρ` should stay there.
- **What holds the lower side.** Only three things: every exact weight stays positive
  (`framed_weight_pos`), the source port's lattice unit is the least modulus, and a move at most
  halves `ρ`. No law of the chart bounds it below.
- **To measure, not a boundary: what a short reach costs.** The memory length `1/(1 − ρ)` is
  `4 18132/28235` ticks at `ρ₀` and `2 13002/124571` at `ρ*`. At `ρ*` a datum more than 23 ticks from
  its station weighs below `2^(−22)`, half a chart unit, while the order-2 span reaches 47 ticks. The
  [founding record](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md) asked that every
  datum of the span stay on the chart, but that described the opening, not a law. Whether those
  faint data carry decisions on another terrain is a measurement for the main line.

**The gradient exists.** The comparison's slope in `ρ` is `γ_ρ = Σ_c c⟨ĝ_c, ∂z_c/∂ρ⟩`, read exactly
through `BankPlacement::modulus_derivative`. A datum's weight `w_k = ρ^(r_k)/M` moves by
`∂w_k/∂ρ = w_k s_k`, with `s_k = (r_k − r̄)/ρ` its reach slope, so the storage's derivative is the
spread of the data's distances from the station. Under `Kinetic` the move still reads `γ_ρ` and keeps
it on its receipt (`modulus_slope`, `split`), but it sets `ρ`'s unit to zero, and the kinetic solve's
`A` has only `E`'s columns. **So the chain holds `ρ` by declaration, not by law.**

## 2. The law: `ρ` joins the minimum-energy move

[definition; agent-inferred] The move is `v = (ΔE, Δρ)`, one coordinate more than `Kinetic`'s. The law
is unchanged: minimize the readings' Gauss–Newton model `cᵀAv + ½ vᵀAᵀFAv`, and among its minimizers
take the least kinetic energy `½⟨Mv, v⟩` (Lean `Holon/Element.unique_minimum_energy`, over any finite
coordinates, the joined ones included).

- **`ρ`'s column of `A`.** Leading member `m`'s reading moves with `ρ` by `a_m = ⟨ĝ_m, ∂z_m/∂ρ⟩`.
  This is the pairing `γ_ρ` sums, without the normal law's weight.
- **The mass is the storage change's energy.** `E`'s mass `I ⊗ H′` is the energy of the storage
  change a move of `E` causes on every datum, read in `E`'s own frame: `H′ = H + Σ_t w_t f_t f_tᵀ`,
  each return's weight the sum of its data's squared transported weights. A datum `k` of feature `f_k`
  stored at weight `w_k` changes by `w_k ΔE f_k + w_k s_k Δρ E f_k` under the joined move. Summed over
  the proposal's data, the energy is `½⟨Mv, v⟩` with

  ```text
  M = [[ I ⊗ H′ , b ],
       [ bᵀ     , g ]]
  b = E · Σ_k w_k² s_k f_k f_kᵀ          (rows × columns of E)
  g = Σ_k w_k² s_k² |E f_k|²
  ```

- **The off-diagonal `b`.** Moving `E` along `E` itself, weighted by the data's distance spread,
  changes the storage the way a move of `ρ` does. So the two coordinates share storage, and the least
  energy move uses that: a `ρ` move that the readings do not ask for is turned against `E`'s storage
  change where that lowers the energy (§6's third case, `(ΔE, Δρ) = (2, −1)`).
- **The retained Gram stays in `E`'s block only.** `H` is the second moment of moments already formed,
  each at its own passage's transport when it was deposited. Retention is that quotient, not a record
  of the data, so `H` carries no datum's distance from a station, and today's `ρ` re-places no
  retained datum. A move of `ρ` changes only the weights of data now passing. So the retained part of
  the energy has no `ρ` row or column, and `b` and `g` are read on this passage alone.
- **One Schur complement.** With `y = (Y, y_ρ)`, `M⁻¹y` is `x_ρ = (y_ρ − ⟨bH′⁻¹, Y⟩)/s` and
  `X = YH′⁻¹ − x_ρ bH′⁻¹`, with `s = g − ⟨b, bH′⁻¹⟩`. `M` is positive exactly when `s > 0`, given
  `H′ ≻ 0`. Where `s ≤ 0`, `ρ` moves no storage that `E` cannot, and it is not joined.

**Why this sizes `ρ`'s move.** The earlier least-squares step `−γ_ρ/G_ρ` was a gradient step in the
storage metric. At the refit's `E` it moved `ρ` by `−9692/2^21` against a chord of `−544808/2^21`
([the modulus slope](2026-10-01_THE_MODULUS_SLOPE_MEASURED_THE_NATIVE_COMPARISON_ASKS_FOR_THE_HIGHER_TRANSPORT_UNTIL_E_READS_THE_RULE.md)).
Here the readings' change is fixed by the comparison's own curvature `AᵀFA`, and the mass only
splits it between `E` and `ρ`.

## 3. How the move realizes it

[definition; agent-inferred] `MoveMetric::KineticModulus` (`hnn::executed`):
- **The solve.** `KineticSolve` with the modulus joined (`ModulusCoupling`: the column, `bH′⁻¹` and
  `s`; `reach_moments` reads `Σ w²s ffᵀ` and `Σ w²s² ffᵀ` over the proposal's data as `returns` reads
  them; `BankPlacement::reach_slopes` gives each datum's `s_k`). Its receipt carries `Δρ`.
- **`E`'s part is a deposition.** The normal law's step with the returns at the solve's reading
  weights is `YH′⁻¹`. The coupling's part `−x_ρ bH′⁻¹` enters as one more covector on each return:
  a return of feature `f` and weight `W` carries `−Δρ (S/W) E f`, with `S = Σ w² s` over the same data
  (`returns_coupled`). It is the storage change of `ρ`'s move, returned to the port through the data
  that carry it, so `E` still changes only by covectors that reached it.
- **`ρ`'s part.** `ρ + ηΔρ` on the port's lattice, nearest, between `ρ/2` and the bound
  `max(ρ₀, ρ)`. The ladder starts at the Gauss–Newton step, at most the entry scale, and every guard
  certifies each trial whole as before.

## 4. Where the comparison asks for more reach than the alias allows

[derived; convexity] The main line read `γ_ρ` at each chain state's incumbent (lower ends, `/4096`
nats per unit of `ρ`). It is positive at `w1`..`w7` (`+540398` to `+805647`), negative at `w8`..`w11`
(`−274818`, `−699231`, `−990807`, `−155362`), and positive at `w12`..`w16` (`+262014` to `+574707`).
So the comparison mostly asks for a shorter memory, but not along the whole path of `E`.

- **What the negative slope means physically.** At `w8`..`w11`, with `ρ = ρ₀`, the comparison asks
  for a longer memory than the one-turn alias allows. There the readings would gain by weighing data
  a turn old more heavily than the chart can separate them from the present phase. In effect the
  comparison is asking to read structure that repeats with the ring's period by folding the previous
  turn into the present one. The phase record cannot carry that: past the bound, a datum's age is
  misread. The bound returns that part of the comparison's ask unmet, as a residual.
- **The bound-active rule.** The joined problem minimizes a convex energy over an affine set of moves
  (the readings' Gauss–Newton change) intersected with the half-space `ρ + Δρ ≤ ρ₀`. Where `ρ` stands
  at the bound and the unconstrained least-energy move has `Δρ > 0`, the constrained minimizer lies on
  the boundary `Δρ = 0`. There the move is `Kinetic`'s, over `E` alone. The move implements exactly
  this. Its Lean statement is owed in #62.

## 5. The other metrics' upper bound: a separate finding

`Coordinate` and `Witness` hold `ρ + ηΔρ` within `[ρ/2, 1]`, the passive bound. So they can carry `ρ`
above `ρ₀`, past the alias bound. The alias law does not depend on the metric, so those paths should
take `ρ ≤ max(ρ₀, ρ)` too. This change leaves them unchanged so that it alters only the new metric's
behaviour. The fix is the same ceiling passed to `ladder`, one line for each metric, and their
measured records were read under the old bound.

## 6. Verification

[proved-derived; implemented-exact]
- `the_joined_solve_splits_the_readings_change_at_least_storage_energy`: three exact cases of the
  joined solve.
  - `ρ` alone moves the reading: `Δρ = 1` and `E` stays.
  - Masses `1` and `3` split the change `(3/2, 1/2)`.
  - The coupled mass `[[1, ½], [½, 1]]` with `ρ` moving no reading gives `(2, −1)`.
- `the_joined_move_carries_the_modulus_and_keeps_every_guard`: on the machine's opening at
  `ρ = 3/4`, the move carries its solve's `Δρ` (or holds `ρ` at the bound), starts at the
  Gauss–Newton step or the entry scale, never carries `ρ` past `max(ρ₀, 3/4)`, and an adopted trial
  lowers the comparison. On that opening the modulus joins with `Δρ < 0`, and the adopted trial (at
  the entry scale `η = 1/128`) carries `ρ` from `3/4` to `1505367/2097152` with `E`.
- The reach slopes rebuild `BankPlacement::modulus_derivative` datum by datum, within `2^(−160)`, on
  every station and section of the placement test.

## 7. What the main line reads, and the check

The data ask for different moduli. The refit fit 8 requests to `ρ*`. A float fit on the chain's same
8 requests ends near `168127/262144` and reads 39 whole of 128 on its float held set (57 with 256
requests). The refit's `E` pays off only at its own `ρ*`: at the chain's `ρ₀` it reads `L`
`310210/4096` and 15 of 64 solved, and at `ρ*` `133292/4096` and 45 solved. So `ρ` behaves as a key
located from the passage, not a constant.

**The check this move must pass.** The main line is walking `w16` in `ρ` (`3/4`, `11/16`, `5/8`,
`9/16`, `ρ*`) with `E` fixed. The joined move from `w16` must reproduce where that walk's comparison
bottoms out: `Δρ`'s sign agrees with `γ_ρ` at `w16` (positive, so `ρ` falls), and its successors'
moduli approach the walk's minimum. Then held-out whole sections against `w16` at fixed `ρ`. That is
the acceptance; until it is read, this record claims the law and its tests only.
