# The transport modulus joins the receiver's minimum-energy move

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [derived] for the
admissible set's upper bound, the bound-active rule, the direction law and the amplitude law
(§1, §4, §4b, §4c); [measured by the main line] for the two basins (§4a); [definition; agent-inferred] for the
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
- **The mass is the storage change's squared norm.** `E`'s mass `I ⊗ H′` is the squared norm of the storage
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

- **Which energy this is.** `½⟨Mv, v⟩` is the squared norm of the storage change in `E`'s frame:
  the mass of the minimum-energy law (`Holon/Element.KineticFace`). It is the rings' stored energy
  of that change only where the rings' storage form is the identity in this chart. A ring's mode
  energy is its own form `UᵀQU`, and that identification is not shown here. So "energy" in this
  record names the law's quadratic form on storage changes, not a measured energy of the Holons.
  The comparison it splits is a code length, which is not an energy until its map to storage and
  work is derived (#62).
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

[measured by the main line; derived] The main line read `γ_ρ` at each chain state's incumbent (lower
ends, `/4096` nats per unit of `ρ`): positive at `m6`, `w1`..`w6` (`+540398` to `+805647`), negative at
`w7`..`w10` (`−274818`, `−699231`, `−990807`, `−155362`), positive at `w11`..`w15` (`+262014` to
`+574707`), and negative at `w16` (`−426589`). So the comparison mostly asks for a shorter memory, but
not along the whole path of `E`.

- **What the negative slope means physically.** Where `γ_ρ < 0` with `ρ = ρ₀`, the comparison asks for
  a longer memory than the one-turn alias allows. There the readings would gain by weighing data a
  turn old more heavily than the chart can separate them from the present phase. In effect the
  comparison is asking to read structure that repeats with the ring's period by folding the previous
  turn into the present one. The phase record cannot carry that: past the bound, a datum's age is
  misread. The bound returns that part of the comparison's ask unmet, as a residual.
- **The bound-active rule.** The joined problem minimizes a convex energy over an affine set of moves
  (the readings' Gauss–Newton change) intersected with the half-space `ρ + Δρ ≤ ρ₀`. Where `ρ` stands
  at the bound and the unconstrained least-energy move has `Δρ > 0`, the constrained minimizer lies on
  the boundary `Δρ = 0`. There the move is `Kinetic`'s, over `E` alone. The move implements exactly
  this and keeps the refused joined solve on its receipt (`ExecutedMove::modulus_held`). Its Lean
  statement is owed in #62.

## 4a. Two basins: `E` and `ρ` adapt together

[measured by the main line] On the chain's 8 requests (`L`, `/4096` nats):
- **`w16`'s `E`, `ρ` lowered from `ρ₀` with `E` held:** `195744` at `ρ₀`, `196331` at `ρ₀ − 2^(−10)`,
  `218712` at `ρ₀ − 2^(−7)`, `279406` at `3/4`, `384896` at `11/16`, `475236` at `5/8`, `547651` at
  `9/16`, `574640` at `ρ*`. Every step down raises it.
- **The refit's `E`:** `310210` at `ρ₀`, `133292` at `ρ*`.

Each `E` is fitted to readings formed at one memory length. `w16`'s `E` reads structure carried by the
long tail of `ρ₀`'s weights, and cutting the tail removes what it reads. The refit's `E` reads
near-term structure, and at `ρ₀` the older data enter readings it does not account for. So neither
coordinate alone carries the difference between the two states. On these requests the short-memory
basin is the deeper one: `133292 < 195744`.

The `w16` walk holds `E`, so it reads the comparison along one line of the joined space. It shows
that `w16` sits at the bottom of that line at the bound. It does not by itself show where the joined
move goes from `w16`, because the joined move also re-adapts `E` (§4c).

## 4b. Where the joined move starts, and what `E`'s amplitude does

[measured by the main line; derived]

**Start before `E` has committed to `ρ₀`.** Along the chain `E` moved with `ρ` held at `ρ₀`, and the
readings' ask along `ρ` turned with it:
- At `m6` and `w1`..`w6`, `γ_ρ > 0`: the readings ask for a shorter memory.
- From `w7`, `E`'s fit at `ρ₀` has begun to read structure carried by the long tail of the weights,
  and the ask turns.
- At `w16` the walk of §4a shows `E` fitted to the bound.

A joined move is local, so from `w16` it can reach the short-memory basin only if its direction law
(§4c) points down there and keeps pointing down while `E` re-adapts. The founded opening and `m6`
are states where the readings still ask for a shorter memory. So the joined move runs from there, and
the comparison with `w16` is made at the endpoint.

**What `E`'s amplitude does to `ρ`'s step** [derived; exact under its condition]. `ρ` changes a
reading only by re-weighing, by age, the storage that `E` reads. So:
- `ρ`'s column `a_m = ⟨ĝ_m, ∂z_m/∂ρ⟩` carries `∂z_m/∂ρ = Σ_k w_k s_k E f_k`, linear in `E`.
- The coupling `b` is linear in `E` and `ρ`'s mass `g` quadratic. `E`'s own mass `H′ = H + Σ w f fᵀ`
  does not depend on `E`.

Suppose a reading depends only on ratios of storage amplitudes, as the bank face's `θ_x = A(x)/Σ A`
does. Put `E ↦ λE` with `λ > 0`:
- The readings, their covector `c` and their Fisher form `F` are unchanged.
- `E`'s columns scale by `1/λ`, and `ρ`'s column `a_m` is unchanged.
- The energy of `(λΔE, Δρ)` at `λE` is `λ²` times the energy of `(ΔE, Δρ)` at `E`, and the two moves
  make the same readings' change.

So the least-energy move at `λE` is `(λΔE, Δρ)`. The memory's step and `E`'s relative step do not
depend on `E`'s amplitude: `ρ`'s mass grows with the amplitude squared exactly as fast as `E`'s
columns shrink.

The executed reading is not of that kind. A ring's growth over a pump period depends on the pump's
depth, which is the storage's absolute amplitude. So along the chain the amplitude is physical, and
the main line reads `s` and `Δρ` per move rather than inferring them from `|E|`. Its Lean statement is
owed in #62.

## 4c. The direction: what the readings ask, less what `E` already supplies

[derived] By the Schur complement (§2), `Δρ = (own − supplied)/s` with `s > 0`
(`KineticSolve::modulus_drive`):
- **`own`** is `Σ_m w_m a_m` at the solve's member weights. It is the readings' ask along `ρ`, and its
  sign is the memory they want: positive asks for a longer memory.
- **`supplied`** is `⟨bH′⁻¹, (Aᵀμ)_E⟩`. It is the part of that ask that `E`'s own move already makes
  through the coupling `b`.

The coupling is nonzero because moving `E` along `E` itself, weighted by the data's age spread,
re-weighs storage as a memory change does. So `E` can make part of a memory change, and the modulus
moves only by the part `E` cannot make.

Two things follow:
- **The sign of `γ_ρ` is not the sign of the joined move.** Where `E`'s re-adaptation supplies more
  than the readings ask, the joined move lowers `ρ` even with `γ_ρ < 0`, and the reverse.
- **At `w16` the joined direction is a reading, not an inference.** The main line reads it from the
  receipt: `kinetic.modulus` if the solve lowered `ρ`, `modulus_held` if the bound held an upward ask.

**No law in the chain decides the basin from the opening alone.** The two basins differ in `E`
across the whole passage, not near the opening, and the direction law is local. What the opening does
decide is the first move's direction, the sign of `own − supplied` there.

## 4d. When a descent's basin is decided

[derived] A descent with certified strict decrease (every adopted move lowers the comparison by
disjoint enclosures) cannot leave the connected part of the sublevel set `{L ≤ L(start)}` that holds
its start. So:

- The basin is decided at the first state whose `L` lies below the lowest pass between the two basins
  (the least, over paths joining them, of the largest `L` along the path). Below that level the two
  basins lie in different parts of the sublevel set, and no certified descent crosses.
- Above it, only the path decides, and the local direction (§4c) is the only law that acts.

**Numbers from the chain.** The founded opening reads `L = 500197/4096`, `m6` reads `338257/4096`,
`w16` `195744/4096` at `ρ₀`, and the refit's `E` `133292/4096` at `ρ*` and `310210/4096` at `ρ₀`. A
path joining the two endpoints is `E` moved straight from `w16`'s to the refit's at `ρ₀`, then `ρ`
walked from `ρ₀` to `ρ*` at the refit's `E`. Its largest `L` bounds the pass from above and is at
least `310210/4096`. The `E` segment's interior is unmeasured. If its largest `L` lies below `m6`'s
`338257/4096`, then neither the opening nor `m6` decides the basin, and the joined chain's first state
below that level does. The main line reads the segment in `L` at a few points (`executed direction`
reads a declared `E` leg).

**The direction at the opening.** `executed joined <terrain> <seed> <count> <arm> <label=source>…`
reads the joined solve's `Δρ` and its two drives at each source, before any bound and without moving.
See §6 for the founded opening's reading.

## 5. The other metrics' upper bound: now the founding bound

`Coordinate` and `Witness` held `ρ + ηΔρ` within `[ρ/2, 1]`, the passive bound, so they could carry
`ρ` above `ρ₀`, past the alias bound. The alias law does not depend on the metric. Since October 2
(the follow-up to #220) every metric is held within `[ρ/2, max(ρ₀, ρ)]`: the move computes one
ceiling, `founding_transport(field, ring).max(transport(ring))`, and the ladder reads it.

- **The defect, reproduced before the fix.** From `generic(92)` at its founded `ρ₀` the slope asks
  for a longer memory (`γ_ρ < 0`), and the coordinate move carried a trial with `ρ > ρ₀`
  (`the_founding_bound_holds_the_coordinate_and_witness_moduli` failed on main at `4c5c311d`). After
  the fix, every coordinate and witness trial holds `ρ ≤ ρ₀`.
- **Campaign 1 does not read these metrics.** Outside the tests, `executed_move` and its metrics are
  called only by the order-2 chain's harness (`research/notebook/hnn_design/hnn_executed_loop.rs`,
  `hnn_loop_1c.rs`). The text campaign's contact loop and its normal-law deposition
  (`Constitution::receiving_class_metric`) do not go through the executed move, so the fix needs no
  campaign 1 read.
- **The chain's earlier states.** Coordinate or witness states read before the fix were reached
  under the old bound; any whose `ρ` stands above `ρ₀` stays there (the ceiling is `max(ρ₀, ρ)`), and
  from such a state no move raises it further.

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
- `the_bound_holds_an_upward_ask_and_the_move_is_e_alone`: from `generic(92)` at its founded `ρ₀`,
  `γ_ρ < 0`, the joined solve asks `Δρ > 0` with `own > supplied`, the bound holds it (the refused
  solve on `modulus_held`), every trial keeps `ρ₀`, and the adopted successor keeps `ρ₀`. This is the
  sign the `w16` walk reads.
- `e_can_supply_more_than_the_readings_ask_and_turn_the_modulus`: from `generic(99)` at its founded
  `ρ₀`, `γ_ρ < 0` and `own > 0`, but `supplied > own`, so `Δρ < 0`.
- The two cases were found by reading the joined move from 8 fixture constitutions (seeds `90`..`94`,
  `98`..`100`) at two moduli each, the fixture field's founded `ρ₀ = 185363/2097152` and `3/4`, on the
  same three requests. At `ρ₀`, 4 moves shortened the memory and 4 had an upward ask held. Over the
  16, `γ_ρ`'s sign agreed with the joined direction in 7. This is a small fixture field, not the
  chain; it shows that the slope's sign does not predict the joined move.
- The reach slopes rebuild `BankPlacement::modulus_derivative` datum by datum, within `2^(−160)`, on
  every station and section of the placement test.

## 7. What the main line reads, and the check

The data ask for different moduli. The refit fit 8 requests to `ρ*`. A float fit on the chain's same
8 requests ends near `168127/262144` and reads 39 whole of 128 on its float held set (57 with 256
requests). The refit's `E` pays off only at its own `ρ*`: at the chain's `ρ₀` it reads `L`
`310210/4096` and 15 of 64 solved, and at `ρ*` `133292/4096` and 45 solved. So `ρ` behaves as a key
located from the passage, not a constant.

**The check this move must pass.** The `w16` walk (§4a) landed and corrects the earlier expectation
that `Δρ` follows `γ_ρ`'s sign at `w16`: there `γ_ρ < 0`, and `E` held at `w16` bottoms out at the
bound. The tests reproduce that sign on a fixture: where the bound holds an upward ask, `ρ` stays at
the bound, the move is `E`'s alone, and the refused ask stands on the receipt (§6).

**The measurement.** Run `KineticModulus` from the founded opening and from `m6` on the same 8
requests. Read, per move:
- `ρ`, `Δρ`, `modulus_drive` (`own`, `supplied`) and `s`;
- `modulus_held` where the bound holds.

Then read:
- whether `ρ`'s path approaches `ρ*` (or the float fit's `168127/262144`) or returns to `ρ₀`;
- the endpoint's `L` against `w16`'s `195744`;
- the held-out whole sections against `w16` at fixed `ρ`.

That is the acceptance; until it is read, this record claims the laws and their tests only.
