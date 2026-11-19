# One cell carries the pass band of a tree, a curve and a junction; a pumped carry locks past its detuning; the heat clock keeps two positivities in opposite directions; and the whole-line ear is never invertible, in Lean

November 19, 2026, 19:45 to 20:40 UTC. One bounded formal pass with its critique. An outside reader's letter of the
day (a Gemini model's, held in the private mailbox and restated here in the repository's words) made four suggestions
for the Lean lane. This record weighs each against the tree, proves the part of each that holds, says which were not
built and why, and then reads the formal objects against the engine: what each one constrains, measures or predicts
in the learner, where the zeta family joins the machine with a theorem, and where it does not join. Nothing ran on a
learner or on the card, and no line was touched. Each paragraph carries its grade: `tree` (read in this repository),
`from training` (a result of the literature, named) or `agent-inferred` (this record's join). Every Lean statement
cited names its module and theorem, and each module checks with no `sorry`, no added axiom and no `native_decide`
(§8). Refs #410.

Seven atlas rows take Lean owners (§9): `rh.frobenius-cell-junction-delay`, `wave.junction-boost-delay-turn`,
`junction.restitution-family`, `bsd.congruent-hasse-site`, `rh.spectral-operator`, `rh.sharpened-hearing-threshold`
and `rh.mellin-plancherel-ear`. Four rows enter: `parametron.pumped-step-kinds`,
`coupling.heat-arrow-two-positivities`, `rh.palette-not-exchange-positive` and `rh.whole-line-ear-never-invertible`.
Read beside them: `trace.cell-norm-algebra`, `tower.field-tick-return`, `bsd.hasse-site-rotation`,
`rh.palette-damping-no-go` and `coupling.reflected-positivity`.

## 1. The four suggestions and what became of each

| The letter's suggestion | The tree before this pass | This pass |
|---|---|---|
| One pass-band theorem for an `SL(2)` cell, joining Kesten's radius, the junction's passed power and Hasse's bound | atlas `rh.frobenius-cell-junction-delay` with a record as its only owner; the cell's quadratic and its three kinds under four Lean owners: `Compression/Landmark/SiteKind`, `Coupling/KreinForm` (the companion cell's norm form, atlas `trace.cell-norm-algebra`), `HNN/CarriedRate` (a carried rate's tuned band) and `HNN/RestitutionFamily` (the junction's return); `Landmarks/TreeWalkFloor` | proved, and joined to the engine's junction return and to a pumped carry step (§2, §3) |
| Weil positivity read as reflection positivity across the seam, kept by sharpening through the Schur product | `Coupling/ReflectedPositivity` (the round-trip form), `Zeta/PaletteLaw` (the damping no-go), `Zeta/WeilPositivity` | the sentence joins two different positivities; the statement that holds is a pair of arrows that point opposite ways, proved with both counterexamples, and the palette of `ξ` has the exchange form at no time of the clock (§4) |
| The ear `F(∂_c)` lifted to the whole line through the Cayley transform | `Zeta/Hearing` (symbol and truncations), `Zeta/MellinPlancherel` (the core) | proved as bounded multiplication operators; the whole-line ear is normal, commutes with the Cayley unitary, and is not invertible at any `τ` and `c` (§5) |
| A stress test of the sign law `Re P ≤ 0` at Lehmer pairs and at mixed foils; a product family's diagonal information metric against a mixture's | `research/notebook/zeta_tube/falsifier.py` §C and §D; atlas `rh.window-tail-falsifier` | not built: the test has no power on the seam, and the metric statement is a reading with no Lean content of its own (§6) |

## 2. One cell's pass band

`tree` and Lean (`Geometry/CellPassBand`). A cell is a stretch of ratio `b` times a turn `φ`, of determinant one:
`cell b φ = diag(√b, 1/√b) · R(φ)`, with trace `(b + 1) cos φ/√b` (`cell_det`, `cell_trace`). Four numbers of a junction
of ratio `b`:

- `edge b = 2√b/(b + 1)`, the band's edge (`sech(½ ln b)`);
- `pass b = 4b/(b + 1)²`, the power a junction passes, and `reflect b = (b − 1)/(b + 1)`, what it turns back, with
  `reflect² + pass = 1` and `edge² = pass` (`reflect_sq_add_pass`, `edge_sq`);
- `gain b = ln((b + 1)/(2√b))` nats, with `e^(−gain) = edge` and `gain = −½ ln(pass)` (`exp_neg_gain`, `gain_eq`).

The band is one inequality, `(tr cell)² ≤ 4 ⇔ |cos φ| ≤ edge b` (`trace_sq_le_four_iff`), and the cell's kind by the
tree's own classifier is a rotation strictly inside the band, null on its edge and a boost outside
(`cell_rotation_iff`, `cell_null_iff`, `cell_boost_iff`, through `SiteKind.siteKind`). The quadratic and its three
kinds were in the tree before this pass, as the companion cell with its norm form (`Coupling/KreinForm`, atlas
`trace.cell-norm-algebra`), as a carried rate and as the junction's return. What this module adds is the chart of a
stretch and a turn, in which the band's edge is the junction's own number, and the reading of that one number in
five places, each a theorem of the module and each joined to its existing owner:

1. **A prime's factor.** Scaled by `√b` the cell's factor is `det(1 − T√b·cell) = 1 − aT + bT²` with
   `a = (b + 1) cos φ` (`scaled_factor`); Hasse's bound `a² ≤ 4b` is the band (`hasse_iff`), and inside it both roots
   have modulus `√b` (`weil_root_normSq`, by `CarriedRate.root_normSq`). `Landmarks/HasseBand.congruent_site_in_band`
   places every good prime of a congruent-number curve inside the band of ratio `p`, from `HasseSite.hasse_bound`.
2. **A tree of `b + 1` branches.** The radial wave `(e^(iθ)/√b)ⁿ` solves the tree's recurrence
   `b·fₙ₊₂ + fₙ = 2√b cos θ·fₙ₊₁` and carries power `b^(−n)` (`radial_recurrence`, `radial_normSq`); a walk's mode
   `cos φ` is such a wave exactly inside the band (`tree_band`). The edge is Kesten's radius
   (`from training`: Kesten 1959), whose floor the tree proves in `Landmarks/TreeWalkFloor`.
3. **A junction of two lines.** `pass` and `reflect` are the passed power and the reflection of a junction of
   impedance ratio `b` (atlas `wave.junction-boost-delay-turn`).
4. **The junction's return.** `tree`: atlas `junction.restitution-family` and Lean `HNN/RestitutionFamily` hold the
   return `x^(k+1) = v^k + Γ(v^k − x^(k−1))` as the restitution about a junction's anchor, with its modes
   `z² − (1 + Γ)λz + Γ = 0` and their modulus `√Γ` where a mode turns (`turning_root_normSq`). This pass reads the
   turning condition in the cell's number: for `Γ > 0` a mode turns exactly for `|λ| < edge Γ` (`return_band`,
   `return_rotation_iff`, `return_root_normSq`, with one root off the circle outside it,
   `root_off_circle_outside_band`), and for `Γ < 0` never (`return_reflection_of_neg`). On the engine's chart
   `Γ = (ρ − 1)/(ρ + 1)`, `ρ = 2^ℓ` (`crates/engine/src/carry.rs`, `junction_gamma`, which is `reflect ρ`), the band is
   `λ² ≤ 1 − ρ⁻²` (`edge_chart`, `return_band_chart`), with no square root: a comparison at the engine's own grain.
5. **A predictor's level** (§2.2).

### 2.1 The return against the tree's walk, and what the engine's tick is

`tree`. The restitution family's row says that at `d` equal ports `Γ = 1/(d − 1)` leaves a port no own return and is
the walk that does not backtrack (`RestitutionFamily.ownReturn_equal_ports`; Alon, Benjamini, Lubetzky and Sodin
2007, cited there). `return_tree` writes that as the tree's recurrence, `b·x^(k+1) + x^(k−1) = (b + 1)·v^k` at
`Γ = 1/b`, beside the counts of `Landmarks/TreeWalkFloor`. On the engine's chart the branching this assumes is
`(ρ + 1)/(ρ − 1)`:

| `ℓ` | `ρ` | `Γ` | branching `1/Γ` | band `λ² ≤` | modulus `√Γ` inside the band |
|---|---|---|---|---|---|
| 1 | 2 | 1/3 | 3 | 3/4 | 0.577 |
| 2 | 4 | 3/5 | 5/3 | 15/16 | 0.775 |
| 3 | 8 | 7/9 | 9/7 | 63/64 | 0.882 |
| 4 | 16 | 15/17 | 17/15 | 255/256 | 0.939 |

Inside the band every mode decays at one rate a tick, `√Γ`, whatever its `λ`; outside it the pair is real and one
root is slower. `from training`: that is the tuned carried rate (Polyak 1964; `CarriedRate.tuned_band`, atlas
`contact.pass-reach-gap`), and on a walk without backtracking it is the tempered bulk, the incoherent modes together
on one circle and a mode that carries located structure outside it (Bordenave, Lelarge and Massoulié 2018, cited by
atlas `key.slow-modes-landmarks`). The join `agent-inferred`: on such a walk a mode's cell is a boost exactly when
local messages can locate it, and a rotation exactly when it is indistinguishable from the bulk.

The engine's tick is not that walk, and the tree read why on November 13 (atlas `tower.field-tick-return`, the
junction record's §13). The built tick adds, `F(x) = x + g(x)`, so a mode's `λ` is the tick's multiplier `1 + μ`; and
a head's contacts carry one way, a written row's round trip reading 0.00068 at the median (G151), so there is no
echo for the return to remove. In the engine the term is a site's carried rate. The band then says that a mode of
the tick turns only where the tick already contracts it under `√(1 − ρ⁻²)`, which is 0.866 at `ℓ = 1` and 0.992 at
`ℓ = 3`, and that a hold (`ℓ < 0`) never turns. The store line's declaration holds the junction's word at `0`
(THE_ENGINE §4). Limits: the band is a law of a constant `Γ`; the engine's `ℓ` is a site's read, and a run of unlike
cells is read by its product's trace, where a periodic change can leave the band from inside it, which is the pump.

### 2.2 A level's gain in nats

`from training` (Levinson 1947, Szegő 1920; the lattice form of a linear predictor). A stage of a predictor whose
reflection is `k` leaves the share `1 − k²` of the residual's power, so on a Gaussian chart it shortens the code by
`−½ ln(1 − k²)` nats a sample, and the gains of a tower of stages add. With `k = reflect b` this is `gain b`
(`gain_eq`), and `e^(−gain) = edge` (`exp_neg_gain`): a level that removes `g` nats a sample is a junction whose band
of delays has edge `e^(−g)`. A level that predicts more passes a narrower band. `agent-inferred`: this is the one
place where the engine's unit (nats a place) and the zeta family's unit (a band edge, a half) are the same number
read two ways, and it holds for the linear, stationary part of a level's news only (§7.2).

## 3. A pumped carry step

`tree` and Lean (`HNN/PumpedCarry`). The letter's engine item (the lead's to build or not) proposes a carry circle
whose step is `z ↦ αz + βz̄`: the built step is `β = 0` (`Holonics/HNN/CarryGate`). The formal side is this pass's.

- **It does not commute.** Steps compose by `(α, β)(α′, β′) = (αα′ + β·conj β′, αβ′ + β·conj α′)` (`step_comp`); the
  gauge `|α|² − |β|²` is multiplicative (`gauge_comp`); two turns commute (`scalars_commute`) and a turn against a
  pump does not (`pumped_do_not_commute`).
- **Its two readings differ.** Its norms lie between `||α| − |β||·|z|` and `(|α| + |β|)·|z|`, both attained
  (`norm_step_le`, `le_norm_step`, `exists_inPhase`, `exists_quadrature`), as the letter said. Its kind is read from
  the real matrix `mat α β`, of trace `2 Re α` and determinant `|α|² − |β|²` (`mat_trace`, `mat_det`), at the engine's
  grain and with no square root:

  | Kind | Condition | Reading |
  |---|---|---|
  | rotation | `|β|² < (Im α)²` (`kind_rotation_iff`) | the charge turns; the pump is under the detuning |
  | null | `|β|² = (Im α)²`, `|β| < |α|` (`kind_null_iff`) | the edge of the lock |
  | boost | `(Im α)² < |β|² < |α|²` (`kind_boost_iff`) | **locked**: two real axes, one held longer than the other |
  | degenerate | `|β| = |α|` (`kind_degenerate_iff`) | one quadrature is erased in a step |
  | reflection | `|β| > |α|` (`kind_reflection_iff`) | the charge is conjugated each step |

- **It is the cell of §2.** With `b` the ratio of its two singular values, the rotation condition is the cell's band
  (`edge_singular`, `rotation_iff_band`).
- **A locked step has two axes.** With a real gate `a` and pump `r·e^(2iψ)`, the axis at angle `ψ` is multiplied by
  `a + r` and the axis at `ψ + π/2` by `a − r` (`inPhase_axis`, `quadrature_axis`): the pump's phase chooses which
  quadrature the store keeps.
- **It is passive under the proposal's weights.** With `|α| + |β| + κ/N ≤ 1` the charge stays within `N·max|b|` at
  every run of sites (`charge_step_le`, `charge_le`, generalizing `CarryGate.charge_le`); the simplex weights
  `a : p : d` meet the bound with equality (`simplex_weights`).
- **At the founded gate any pump locks.** With the simplex weights the step turns exactly when `p² < a²·(Im γ)²`
  (`simplex_rotation_iff`), so at a real gate (`q = 0`, where every circle is founded) every pump `0 < p < a` is a
  boost and never a turn (`founded_gate_locks`).

What it is for, `agent-inferred`. THE_ENGINE §11 reads the theory's law "a lock binds: past its bifurcation a row
commits to its sources" against "a row is a soft mixture". The pumped step is the smallest store that can commit: a
step in the rotation kind keeps both quadratures alike and holds no choice between them, and a step in the boost
kind keeps one and sheds the other at the ratio `(a + r)/(a − r)` a step. The test `(Im α)² < |β|²` is the lock test
for one circle at one site, and the count of circles that pass it is the count the parametron's capacity law speaks
of (the lock count, atlas `parametron.ising-lock`). It is also the first step in the tree's carry that does not
commute, which §7 comes back to. What does not follow: nothing here says a pumped circle trains, or that its lock
lands on the sources a place needs. That is a learner's reading, read beside a control.

## 4. The heat clock keeps two positivities, in opposite directions

`tree` and Lean (`Coupling/HeatArrow`, `Zeta/PaletteReflection`). The letter's sentence is that Weil positivity is
reflection positivity across the seam `u = 0`, that the sharpening `e^(+τu²)` keeps it by the Schur product, and that
this is the one-way arrow of the de Bruijn–Newman clock. Two different forms are joined in it:

- the **translation** form `Σ xᵢ k(uᵢ − uⱼ) xⱼ` (positive type, Bochner's), which is the form of Weil's criterion: a
  test function convolved with its own reversal, over the whole line, read on the zeros' side (`Zeta/WeilPositivity`);
- the **exchange** form `Σ xᵢ k(uᵢ + uⱼ) xⱼ` (Hankel's; the round trip of a translation form through the reflection
  `u ↦ −u`, `roundTrip_translation`, which is `ReflectedPositivity.roundTripForm` on the line for an even kernel),
  which is reflection positivity.

The Gaussian splits both ways around one cross kernel: `e^(τ(u+v)²) = e^(τu²)·e^(2τuv)·e^(τv²)` and
`e^(−t(u−v)²) = e^(−tu²)·e^(+2tuv)·e^(−tv²)` (`seam_split`, `translation_split`). The cross kernel `e^(c·uᵢuⱼ)`,
`c ≥ 0`, keeps a positive form positive (`Pos.exp_cross`, proved from the exponential's series because Mathlib holds
no Schur product theorem at this pin). So:

- sharpening keeps the exchange form (`exchange_sharpen`, `exchangePositive_sharpen`), and damping does not
  (`exchange_damp_fails`, `exchangePositive_not_dampingClosed`: two points and the constant kernel);
- damping keeps the translation form (`translation_damp`, `translationPositive_damp`), and sharpening does not
  (`translation_sharpen_fails`, `translationPositive_not_sharpenClosed`).

Each closure has its counterexample in the other direction, so neither is a statement that could not fail. Against
the letter's sentence:

1. Weil's positivity is of the translation kind, and the translation kind is closed under **damping**. By the tree's
   no-go (`PaletteLaw.dampingClosedLaw_does_not_force_seam`) a law closed under damping cannot force the seam, and
   `PaletteReflection.translationPositive_offSeam_witness` gives the witness for this law: `e^(−u²) cos u` is of
   the translation kind and its transform vanishes at `½ + π`.
2. The exchange kind is the one sharpening keeps, and the no-go does not reach it
   (`exchangePositive_not_closed_under_palette_damp`). But the palette does not have it at any time of the clock:
   an even, exchange-positive, integrable kernel vanishes at the seam
   (`exchangePositive_even_integrable_seam_eq_zero`, from `ExchangePositive.seam_le`: such a kernel is least at the
   seam), and every flowed palette `e^(τu²)Φ` is even, integrable and positive there, so none is exchange positive,
   sharpened or damped (`Φ_flow_not_exchangePositive`, `Φ_not_exchangePositive`). There is nothing on the palette
   for sharpening to keep.
3. `from training`, not in Lean: the palette is not of the translation kind either. By Bochner's theorem it would
   need `Ξ(t) = ξ(½ + it) ≥ 0` on the line, and `Ξ` changes sign at each zero of odd order. Weil's positive form is
   a form on test functions read through the zeros, and the clock does not act on it by a Gaussian factor.

What the two arrows share, `agent-inferred` with its parts `from training`: the cross kernel `e^(2τuv)` is a
coupling between the two sides of the seam, and its sign is the clock's direction. `τ > 0` is the ferromagnetic sign,
which keeps a Lee–Yang measure's zeros on the line (Newman 1974 and 1976; the tree's finite case is
`Coupling/LeeYangCircle` and atlas `thermal.ising-lee-yang`) and keeps reflection positivity across a cut (Fröhlich,
Israel, Lieb and Simon 1978). `τ < 0` is the antiferromagnetic sign and keeps neither. The clock's arrow in the tree
is proved by another route (`Zeta/PolyaStep`, `Zeta/ForwardPreservation`); the construction that would make the
letter's sentence a theorem is a Lee–Yang statement for the measure `e^(τu²)Φ(u)du` with the coupling written as a
contact across the seam, and its positive form is the lock polynomial's, not the palette's exchange form.

What it is for in the machine, `agent-inferred`. Read across the present, with `u` the delay before it and `v` the
delay after, the exchange form of a region's autocovariance is its Hankel form: its rank is the number of modes a
memory of that region needs (Kronecker; atlas `key.finite-hankel-rank`), a relaxing mode is exchange positive
(`exchangePositive_exp`) and a turning mode is not (`cos_not_exchangePositive`, while it is translation positive,
`translationPositive_cos`). So the form's negative squares count a region's turning pairs, and its positive squares
its relaxing modes. A carry circle with a real gate is a relaxing store and one with a turn is a turning store, so
this inertia is a reading that sizes the two parts of a carry bank from the passage instead of from a trial (§7.3).

## 5. The whole-line ear

`tree` and Lean (`Zeta/CayleyEar`). On the Mellin side `∂_c` is multiplication by `c + 2πiξ`
(`MellinPlancherel.coeFn_mellinPlancherel_scaleDeriv`). The module builds the bounded multiplication operator of a
bounded continuous symbol on `L²(dξ)` (`mulOp`, with `mulOp_mul`, `mulOp_star`, `norm_mulOp`). It is normal, it is
unitary when its symbol has modulus one (`mulOp_mem_unitary`), it is invertible exactly when its symbol is bounded
away from zero (`isUnit_mulOp_iff`), its spectrum is the closure of its symbol's values (`spectrum_mulOp`), and a
continuous function of it is the multiplication by that function of the symbol (`cfc_mulOp`). The proved unitary
carries all of this to `L²(e^(−2cx)dx)` (`pull`, with `spectrum_pull`). Then:

- the Cayley symbol `(2πiξ − 1)/(2πiξ + 1)` has modulus one and never takes the value one (`norm_cayleySymbol`,
  `cayleySymbol_ne_one`). Its operator `cayleyEar c` is unitary (`cayleyEar_mem_unitary`), its spectrum is the whole
  unit circle (`spectrum_cayleyEar`), and one is in that spectrum without being an eigenvalue
  (`cayleyEar_apply_eq_self_iff`). On the Schwartz core it is the Cayley transform of `A = ∂_c − c`: it carries
  `(A + 1)f` to `(A − 1)f` (`cayleyEar_core`);
- the core determines it. `A + 1` and `A − 1` have dense range on the core (`denseRange_cayleyDomain`,
  `denseRange_cayleyRange`), so a bounded operator that carries `(A + 1)f` to `(A − 1)f` there is `cayleyEar c`
  (`eq_cayleyEar_of_core`). That is what lets the module call it the Cayley unitary of the scale derivative, and not
  only a conjugate of a multiplier;
- the ear on the whole line, `earOp τ c`, is multiplication by the bounded continuous symbol
  `ξ ↦ heatE (−τ) ξ (c + 2πiξ)` (`earSymbol`, `coeFn_mellinPlancherel_earOp`). It is normal, it commutes with the
  Cayley unitary (`earOp_comm_cayleyEar`), and it is Hearing's averaged shift wherever that average is in the space
  (`earOp_eq_average`). It is a continuous function of the Cayley unitary: with
  `earCircle τ c w = heatE (−τ) ξ (c + (1 + w)/(1 − w))` off `w = 1` and zero at `w = 1`,
  `earOp τ c = cfc (earCircle τ c) (cayleyEar c)` (`earOp_eq_cfc`), the value zero at one being the limit the next
  item gives (`continuousOn_earCircle`);
- its symbol is a Fourier transform of an integrable weight (`earSymbol_eq_fourier`), so it tends to zero along the
  line (`tendsto_earSymbol`, the Riemann–Lebesgue lemma), and **the whole-line ear is not invertible at any `τ` and
  any `c`** (`not_isUnit_earOp`), whatever the zeros are. Zero lies in its spectrum, which is the closure of the
  flowed function's values on the line (`zero_mem_spectrum_earOp`, `spectrum_earOp`).

The last statement is the one that says something the tree did not hold. Invertibility of the whole-line operator
cannot be the criterion, because it fails at every sharpening and on every line, the seam's own included. The
criterion is the family of band-limited truncations, each invertible exactly when the symbol has no zero on its
segment (`Hearing.quasiInvertible_iff_verticalZeroFree`), and the threshold is read there
(`Hearing.threshold_eq_quasiInvertibleInf`); `wholeLine_not_isUnit_and_truncations_criterion` sets the two side by
side. On the objects: an ear over all delays always has a mode it hears as faintly as one likes, so "it hears no
zero" is a statement about every finite band and never about the whole. A receiver's band is part of the statement.

`from training` and `agent-inferred`. This separates the tree's ear from the operator it was named after. Herichi
and Lapidus's spectral operator is `ζ(∂_c)`, with `ζ` itself as the symbol (atlas `rh.spectral-operator`): that
symbol does not tend to zero along a line (it is bounded below for `c > 1`, and for `c` in `(0, ½)` whether it stays
away from zero is the question itself), the operator is unbounded, and its whole-line invertibility is one of their
two criteria (invertible at every `c` in `(0, ½)`). The
tree's ear takes the completed function, flowed by the heat clock, in `ζ`'s place. The archimedean factor makes
that symbol a Fourier transform of an integrable weight, which is what makes the operator bounded and is also what
makes it die along the line. So the completion buys a bounded normal operator and Mathlib's calculus, and it costs
the second criterion: for the completed function only the truncations remain, and the letter's phrase "the global
normal operator" names an object whose own invertibility carries no information.

Of #410's box on the operator-level ear, this states the ear as a bounded normal operator on the whole space, as a
function of the scale derivative's Cayley unitary, with its spectrum, and it states that the core determines that
unitary. The construction still to write is the closed operator as an object: the closure of `∂_c − c` as a
`LinearPMap`, skew-adjoint with spectrum `iℝ`, as the inverse Cayley transform of `cayleyEar c`; a calculus stated
for that closure (Mathlib holds the calculus for bounded normal elements, and `earOp_eq_cfc` is a statement of the
bounded unitary); Young's inequality, which would drop `earOp_eq_average`'s hypothesis that the average lies in the
space; and the truncations of `Zeta/Hearing`, which stand in the model `C([−T, T], ℂ)`, as compressions of `earOp`.

## 6. The two suggestions that were not built

**The stress test.** `tree` (`research/notebook/zeta_tube/falsifier.py` §D). The sign law is `Re P ≤ 0` at every
zero, `P = 2ζ″/ζ′` the Dirichlet-series part of a zero's velocity and `arch` the archimedean part. On the seam
`Ξ(t) = ξ(½ + it)` is real, so `ξ″/ξ′` is imaginary wherever `ξ′ ≠ 0`, and `Re P = −Re arch`, which is near
`−ln(γ/2π)` at height `γ`. At every simple zero on the seam the sign is fixed by the height, a Lehmer pair's
included: a closer pair changes `Im`, never `Re`. A read at Lehmer heights therefore returns the sign it was built to
return and tests nothing, which is the failure the lessons record as a theorem that cannot fail. The mixed foil the
letter asks for is already read: §C of the falsifier takes the Davenport–Heilbronn function and finds the signs
`−, +, +, +` at its off-seam pairs. The law's global form can be refused only by a zero off the seam and confirmed
only by a cause, so no finite read at seam zeros moves it.

**The product family's metric.** `from training` and `agent-inferred`. A product of independent laws has a diagonal
Fisher information and a mixture has cross terms: a two-line computation with no Lean content of its own. Its
reading is worth keeping. A code that factors across coprime rings (an Euler product is one) is the case where a
deposit made ring by ring is the natural-gradient step, and the mutual information between ring residues measures
how far a state is from that case. The Davenport–Heilbronn function is a mixture of two products and its zeros
leave the seam; THE_ENGINE §11's "a row is a soft mixture" is the same shape on the machine's side. It is offered
as a host ruler (the mutual information between a symbol's ring residues), and nothing was built for it.

## 7. What the formal objects are for, and where the zeta family joins the engine

The question this section answers plainly: of the Lean under `Zeta/` and its neighbours, what constrains, measures
or predicts something in the learner. Counts first, `tree`: `lean/HolonicsResearch/Zeta/` holds 176 modules before
this pass, the atlas 268 rows named `rh.*` of which 206 carry a Lean owner, and no file under `crates/` names any of
them.

### 7.1 Where the join is a theorem

1. **The half is the floor of incoherence, and a mode is locatable exactly outside the band.** `tree`:
   `receiver.half-is-incoherence`, `hnn.field-residual-half-rank`, `trace.tree-walk-floor`,
   `key.slow-modes-landmarks`. A statement of the Riemann kind says that after the smooth part is removed every
   remaining mode sits at the square root of the count: nothing coherent is left for a receiver to take. Located
   structure is a mode above that floor, and the price of locating a mode of bias `ε` is about `1/ε²` readings,
   which is linear cryptanalysis's count and a deposit's (`from training`: Matsui 1993). On a walk without
   backtracking the threshold is the band's edge and the theorem is proved (§2.1). This is the sense in which the
   zeta family is about learning: it is the theory of the residual a complete code leaves, and of the threshold at
   which a residual stops being one. `cell_boost_iff` is that threshold's algebra.
2. **A level's gain is a band edge** (§2.2), for the linear, stationary part of its news.
3. **The return of the state two ticks before is the walk without backtracking wherever contacts carry both
   ways** (§2.1). The zeta of a graph counts only such walks (`trace.ihara-zeta`), and the tree holds the term in
   Lean (`HNN/RestitutionFamily`) with its band now at the engine's grain. What the built tick lacks for that
   reading is the round trip (§7.2, item 1).
4. **A memory's width is a Hankel rank, and its kinds are the exchange form's inertia** (§4). `from training`:
   Adamyan, Arov and Krein 1971, a memory of `n` modes misses the Hankel form by its `(n+1)`-th singular value and
   no `n`-mode memory does better. The boundary in "a spectral gap at a boundary" is the present, and the operator
   on it is this one.
5. **A lock is a boost of a pumped step** (§3), with its test at the engine's grain.

### 7.2 Where it does not join, and the construction that would join it

1. **The family's theorems need a reversal with a positive form, and the engine's transport carries one way.**
   Every statement of the family that puts modes on a circle has the same three parts: a positive form, an
   involution that reverses a path (a dart and its reverse, a zero and its reflection, a strand and its mate) and a
   scale `q`. The half is where the reversal's own form is positive (`tree`: the fourth record of November 18;
   `trace.regular-norm-form`). The objects state a Holon that way: ports carry flow and effort, the interconnection
   is power-neutral, and orientation exists only in the pairing. The built engine differs at exactly this point. A
   head's contacts carry one way (G151's 0.00068), the forward is a feed along the passage, and the reversal exists
   as the adjoint sweep that trains every part through all that follows it (THE_ENGINE §11, first row). So in the
   machine as built the half has three places to stand: the pair of a strand and its mate where the engine builds
   it, the present (the Hankel form of §4) and the adjoint. It has none in the tick's transport, and
   `det(1 − uB)` of a one-way transport has no functional equation to put its modes on a circle. This is the plain
   answer to where the architecture does not unify: the theory's object is reciprocal, the engine's transport is
   not, and reciprocity is the hypothesis the zeta family's theorems use. The construction is a round trip: contacts
   that carry both ways with the return removing the echo (the restitution family, in Lean since November 13), read
   first by the round trip `B` on the line's present rows (`tower.field-echo`).
2. **No path from the engine reaches the family.** The 176 modules are consumed by each other and by the atlas. The
   truth of the Riemann hypothesis changes no term the engine computes; what transfers is the finite statements
   whose hypotheses the machine meets (a cell, a junction, a lock polynomial, a finite complex's zeta). The lane
   grew faster than the engine consumed it, which is the audit of November 18's "parts are added and never removed"
   on the formal side, and this pass met it: the cell's quadratic stood under four owners, and two of them
   (`Coupling/KreinForm`, `HNN/RestitutionFamily`) were found only after the pass's own module was written, which
   then joined them instead of restating them. From here a statement enters this lane with the engine term it
   constrains or the ruler that reads it, as the five of §7.1 do.
3. **The zeta of the integers is the commutative theory, and what the line lacks is not commutative.** `ζ` is
   built from characters; a word over commuting moves reads only its counts (`key.commutator-is-and`,
   `Compression/FaithfulModes.abelian_word_counts`). The coprime rings of a symbol's word are that theory, and the
   line's readings match it: single words stand (72% in the register's lexicon at lap 41 by the lead's panel) and
   composition past two or three words does not. Binding needs moves that do not commute, and the family's theory
   of those is the zeta of a transport's own cycles (`trace.ihara-euler-product`: its primes are primitive cycles of
   words, classes under rotation, as the record of November 12 reads a text's primes) with a factor of rank two at
   each. The pumped step of §3 and the cell of §2 are that factor. The construction: the machine's own zeta,
   `det(1 − uB)` for the transport `B` a level actually applies, read by a ruler against its cycle counts; its
   bulk and its modes outside the band are then readings of the learner, where the integers' zeta is a chart of
   another object.
4. **The family's theorems are of operators at rest, and a deposit moves the operator.** The band says a cell's
   kind in the long run and nothing of its transient: a cell just inside its band is conjugate to a turn by a
   stretch that grows without bound at the edge, and `PumpedCarry` carries both readings for that reason, the kind
   by the trace and the gain by the norms. The one object of the family that is itself a motion of the operator is
   the heat clock (§4), and the tree's reading of a deposit's rate as a temperature
   (`deposition.rate-temperature-standing-spread`) is where it would meet the learner; no theorem joins them yet.
   The construction: the clock's zero dynamics stated for a finite lock polynomial under a change of coupling,
   which is the form a cooling law's reading could take.
5. **The Hodge conjecture has no term in the engine; Hodge's decomposition does.** Friction keeps the harmonic part
   (the third set of today's seventh pass), which is the retention law's shape. The conjecture says more: that a
   retained class of the right type with rational periods is carried by cycles one can name. On a finite complex
   over the integers every class is carried by a cycle and the statement has no content; where it bites is torsion
   (`from training`: Atiyah and Hirzebruch 1962), a class whose multiple is carried and which is not.
   `agent-inferred`: the machine's reading is provenance, an answer from the retained state carried by strands it
   can name, which is Athena's acceptance, and the torsion case is a carry of order `n` no single strand holds.
   That is a lens with one test and no theorem.
6. **"A spectral gap in space and time" has two operators in the tree and they are not yet one.** Across the
   present it is the Hankel form (§4); across scale it is the band of a tree's walk (§2). `from training`: a gapped
   chain forgets exponentially and holds a bounded width across any cut (Hastings 2007), a critical one holds a
   width that grows with the logarithm of the cut's length, and text is of the second kind, its mutual information
   falling as a power of the distance, which no chain of finitely many states gives and a tree's recursion does (Lin
   and Tegmark 2017). On a tree a mode survives the descent exactly when it stands outside the band, `b·λ² > 1`
   (Kesten and Stigum 1966). So the theory's statement about the tower is definite: a level joins the levels below
   by a branching greater than one, and what it can hold of them is what stands outside its band at that
   branching. THE_ENGINE §11 reads the built level as holding under a tenth of any of its symbols with no
   comparison at its own grain. With a presence `λ` near a tenth a mode needs on the order of a hundred independent
   routes to stand outside the band; the mapping of the engine's presence to the theorem's `λ` is this record's
   guess and is the first thing a ruler would check.

### 7.3 Readings this pass offers the line

Each is a host ruler on saved states or on the passage, with the planted law its null is held to. None is ordered;
the lead's lane decides.

| Reading | The law it reads | Its planted law |
|---|---|---|
| The lock test `(Im α)² < |β|²` a circle a site, and the count of locked circles | `PumpedCarry.kind_boost_iff` | a step built in each kind |
| The round trip `B` a head on the line's present rows (0.00068 at the median on November 13) | `tower.field-echo`; `RestitutionFamily.ownReturn_equal_ports` | a row made symmetric |
| A tick's multipliers `1 + μ` against the return's band `λ² ≤ 1 − ρ⁻²` | `CellPassBand.return_band_chart` | a planted multiplier on each side of the edge |
| The Hankel form of a region's news across the present: its rank at a tolerance and its negative squares | `HeatArrow.exchangePositive_exp`, `cos_not_exchangePositive`; `Foundation/HankelKey` | a sum of known decays and turns |
| A level's gain in nats against the band it passes, `|cos φ| ≤ e^(−g)` | `CellPassBand.exp_neg_gain` | an autoregression of known reflection |
| The transport's own zeta: cycle counts against `tr Bⁿ`, and the modes' radii against `√b` | `Landmarks/IharaBass`, `CellPassBand.cell_boost_iff` | a planted mode past the edge |

## 8. Lean

Six modules enter `HolonicsResearch`, each imported by the library's root.

| Module | Declarations | Section |
|---|---|---|
| `Geometry/CellPassBand` | 46 | §2 |
| `HNN/PumpedCarry` | 32 | §3 |
| `Landmarks/HasseBand` | 2 | §2 |
| `Coupling/HeatArrow` | 30 | §4 |
| `Zeta/PaletteReflection` | 7 | §4 |
| `Zeta/CayleyEar` | 85 | §5 |

- Three workers on disjoint owner paths wrote the modules from briefs that fixed the statements. The lead re-checked
  each file, removed one theorem of `Zeta/PaletteReflection` whose hypothesis fails classically (it assumed the
  palette to be of positive type, which it is not; `translationPositive_offSeam_witness` carries the claim with no
  hypothesis), added `CellPassBand.return_tree`, and rewrote the cell module's sources once `HNN/RestitutionFamily`
  and `Coupling/KreinForm` were read (§2).
- Three docstrings were repointed: `Zeta/Hearing`'s open item and `Zeta/MellinPlancherel`'s "What is not claimed"
  now name `Zeta/CayleyEar`, and one sentence of `Coupling/ReflectedPositivity` that named a Rust check as present
  now says it ran in the Rust body of its day.
- Gate 4, in a cloud container at the package's pinned toolchain and Mathlib (the guide's rule 4 of a line's lap,
  `agent-inferred` there): `bash tools/lean_check.sh` on the six modules and the three whose docstrings changed read
  `Build completed successfully (8891 jobs)`, exit 0, with no warning from a new module. The research library's
  whole root closure was not rebuilt there (163 of its 1,487 modules stood built in the container). Gate 4 asks for
  it so that a module's names are read beside the rest; here each new module's namespace is its own in the tree,
  which was read by a search (`agent-inferred` that this meets the reason).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `test_records_index.py` passes, and
  `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, no added axiom and no `native_decide`. `#print axioms`, on the closing lines of `Coupling/HeatArrow`,
  `Zeta/PaletteReflection` and `Zeta/CayleyEar` and on thirteen theorems of the other three modules read from a
  scratch file, reads `propext`, `Classical.choice` and `Quot.sound` alone.

## 9. Atlas

Four rows enter:

| Row | Shard | Grade | Lean owner |
|---|---|---|---|
| `parametron.pumped-step-kinds` | objects | `formal-checked` | `HNN/PumpedCarry` |
| `coupling.heat-arrow-two-positivities` | targets | `formal-checked` | `Coupling/HeatArrow` |
| `rh.palette-not-exchange-positive` | targets | `counterexample` | `Zeta/PaletteReflection` |
| `rh.whole-line-ear-never-invertible` | targets | `formal-checked` | `Zeta/CayleyEar` |

Seven rows take Lean owners and have their limits rewritten to what is now stated:
`rh.frobenius-cell-junction-delay` (its only owner had been a record; `Geometry/CellPassBand` and
`Landmarks/HasseBand`), `wave.junction-boost-delay-turn` and `junction.restitution-family`
(`Geometry/CellPassBand`), `bsd.congruent-hasse-site` (`Landmarks/HasseBand`), and `rh.spectral-operator`,
`rh.sharpened-hearing-threshold` and `rh.mellin-plancherel-ear` (`Zeta/CayleyEar`).
