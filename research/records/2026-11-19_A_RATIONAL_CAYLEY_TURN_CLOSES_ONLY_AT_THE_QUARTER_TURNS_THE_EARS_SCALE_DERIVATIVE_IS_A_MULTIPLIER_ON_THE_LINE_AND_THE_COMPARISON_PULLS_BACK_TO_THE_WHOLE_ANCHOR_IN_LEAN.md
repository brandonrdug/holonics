# A rational Cayley turn closes only at the quarter turns, the ear's scale derivative is a multiplier on the line, and the comparison pulls back to the whole anchor, in Lean

November 19, 13:01 UTC. The twenty-second formalization pass over #410, its twenty-third set, after [the
twenty-second](2026-11-19_THE_RING_IS_THE_SAMPLED_OSCILLATOR_AN_EXPANDING_METRIC_MEETS_A_FLUID_AND_ITS_BATH_AND_THE_CANTOR_STRINGS_HOLES_ARE_PLACED_AND_HEARD_IN_LEAN.md)
(#1034). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Geometry/CayleyTurnClock` | The Cayley point `z(q) = (1 + iq)/(1 − iq)` is `exp(iθ)` with the turn `θ = 2 arctan q ∈ (−π, π)`, its parts the owner's `cayleyCos`, `cayleySin` at rational `q`, and half-angle addition holds on the plane (`cayleyPoint_eq_exp`, `arg_cayleyPoint`, `cayleyPoint_mul`); `dθ/dq = 2/(1 + q²)`, so a uniform parameter clock turns at `2v/(1 + q²)`, not uniformly (`hasDerivAt_turnAngle_clock`, `clockRate_ne`, `turnAngle_two_ne`); the powers' clock map is completed turns plus an open phase, which alone the circle reads, the completed turns adding with a carry of `0` or `1` (`cayleyPoint_zpow_fract`, `completedTurns_add`, `turnCarry_mem`); a rational `q` closes at a positive period iff `q ∈ {0, ±1}`, with periods `1` and `4`, through Niven's values, and the 3-4-5 point `z(½)` never closes (`ratCast_closes_iff`, `ratCast_pow_eq_one_iff`, `cayleyPoint_half_never_closes`); the lifted winding `polygon + n·e = n(θ + 2πe)/2π` is an integer exactly at a closure and separates the extra turns the circle cannot see, and the Rust `lifted_winding` and `closes_after` are `checkedWinding` and `closesAfter`, with the Rust controls by `decide` (`liftedWinding_eq`, `liftedWinding_extra_injective`, `checkedWinding_eq_some_iff`, `checkedWinding_quarter_extra`); a rational turn's passages read `PhaseCarry`'s phase and winding, and the quarter turn is its odometer on four steps (`rationalTurn_pow`, `quarterTurn_clock`); phases close together iff the least common multiple of their orders divides the count, through `RingClosure` (`joint_closure_iff`, `rationalTurn_joint_iff`, `quarter_sixth_refused`) | #410's box "Phase, action and clock binding" (ticked); the retired Rust `RationalPhase` (`13f8c734`), the winding guide §1 and `Transport/SerialChainJacobian`'s "What is not claimed" | `chain.cayley-turn-clock` (new); `phase.rational-phase-winding` (owners, now `formal-checked`) |
| `Zeta/MellinPlancherel` | With `x` the log scale and `μ_c = e^{−2cx}dx`, the weight `W_c = e^{−cx}` is a unitary `L²(μ_c) ≃ L²(dx)`, and with Mathlib's `L²` Fourier transform it composes to the Mellin–Plancherel unitary `U_c : L²(μ_c) ≃ L²(dξ)`, which is the line transform `∫ f e^{−(c+2πiξ)x} dx`, Mathlib's `mellin` at `c + iy`, wherever `W_c f` is integrable, with Plancherel `∫ |∫ f e^{−(c+iy)x} dx|² dy = 2π ∫ |f|² dμ_c` (`weightEquiv`, `mellinPlancherel`, `coeFn_fourier_toLp`, `lineTransform_eq_mellin`, `plancherel_line`); on the Schwartz core `∂_c` is carried to multiplication by `c + 2πiξ` and `2c − ∂_c` to its conjugate (`coeFn_mellinPlancherel_scaleDeriv`, `coeFn_mellinPlancherel_scaleDerivAdj`); `2c − ∂_c` is a formal adjoint of `∂_c` on the dense core, `∂_c − c` is skew, the two commute and `‖∂_c f‖ = ‖(2c − ∂_c)f‖` (`inner_scaleDeriv`, `inner_scaleDeriv_sub`, `scaleDeriv_comm`, `dense_coreDomain`, `scaleDerivAdjOp_le_adjoint`, `norm_scaleDerivOp_eq`); a scale shift is `e^{u∂_c}`, multiplication by `e^{(c+2πiξ)u}`, and an averaged shift is multiplication by `F(c + 2πiξ)`, `F(s) = ∫ w(u)e^{su} du` (`fourier_weight_shift`, `fourier_weight_average`, `coeFn_mellinPlancherel_average`); Hearing's weight gives `F = heatE(−τ)ξ`, so `F(∂_c)` is the flowed `ξ` as a multiplier, nowhere zero exactly when the ear hears no zero on the line (`integral_hearingWeight`, `fourier_weight_hearingAverage`, `verticalZeroFree_iff_multiplier_ne_zero`) | #410's box "The operator-level ear" (part done); `Zeta/Hearing`'s `[open; #62]` item | `rh.mellin-plancherel-ear` (new); `rh.sharpened-hearing-threshold`, `rh.spectral-operator` (owners, scope) |
| `HNN/AnchorGradient` | A face with gradient `w` on the logits pulls back to the receiving ring's anchor with derivative `δ ↦ ⟨w, R P^τ δ⟩` and gradient `(P^τ)⁻¹ R† w`, the closing ring's power `P^((d−1)τ) R† w` in place of the inverse (`hasFDerivAt_pullback`, `hasGradientAt_pullback`); the phase cost `½ Σ_c q_c Δ_c²` of the imaginary logits has the whole derivative and gradient `(P^τ)⁻¹ Rim†(−½ q Δ)` at every anchor (`hasFDerivAt_anchorCost`, `hasGradientAt_anchorCost`), and the code-length excess, the real part of the owner's lifted excess, the gradient `(P^τ)⁻¹ Rre†(p̂ − q)/ln 2` (`codeExcess_eq_re`, `hasGradientAt_anchorCode`); both move along any curve at the pairing of the gradient with its velocity, the owner's line results being the value at `δ` (`anchorCost_along_curve`, `phase_line_is_value`, `magnitude_line_is_value`); the phase cost is a quadratic along every line, a gradient step lowers it iff `ηC₂(g) < ‖g‖²`, with the sufficient range `η(Q/8)‖Rim‖² < 1` and the line's least point at `η* = ‖g‖²/(2C₂(g))` (`anchorCost_line`, `gradient_step_descends_iff`, `gradient_step_descends`, `minimizing_step`); the quarter-turn witness reaches cost `0` in one step (`quarterTurn_witness`); a continuous nonvanishing ratio on a convex domain of the anchor space has a continuous lift, unique up to `2πin`, carrying `R⁻¹DR` in every direction (`exists_continuous_lift_convex`, `continuous_lift_unique_convex`, `continuous_lift_hasFDerivAt`, `continuous_lift_anchor_space`) | #410's box "The phase pullback beyond the anchor line" (ticked; its reading `agent-inferred`); `HNN/Ratio` item 2 and `Objects/RatioPhase`'s `[open]` paragraph | `hnn.anchor-gradient-step` (new); `hnn.receiving-phase-pullback`, `ratio.continuous-lift` (owners and the whole-space clauses) |

The boxes these answer, by their opening words: "Phase, action and clock binding" (ticked); "The operator-level ear"
(part done); and "The phase pullback beyond the anchor line" (ticked).

## 2. What the pass corrected

1. The winding guide, `docs/HELICAL_GEOMETRY.md` and the atlas row `phase.rational-phase-winding` said that a rational
   Cayley point "need not close at any finite period". Over the rationals it closes at a positive period only at `q ∈
   {0, ±1}` and never otherwise (`ratCast_closes_iff`); the three texts now say so. The box placed the joint closure in
   `Geometry/PhaseCarry`, which holds the carry and the odometer; the least-common-multiple law is
   `Geometry/RingClosure`'s, and the module reads it there. The lifted winding's additivity holds at every count, not
   only at closures: only its being an integer needs a closure.
2. Hearing's open item spoke of a unitary carrying `∂_c` "to multiplication by `c + iy` on `L²(ℝ, dy)`": the line
   transform multiplies norms by `√(2π)` on `L²(dy)` (`plancherel_line`), so the unitary lands on `L²(dξ)` with
   multiplier `c + 2πiξ`, or on `L²(dy/2π)`; the item now says so. The brief named "essential self-adjointness of `i∂`"
   among what is not asked: in `L²(μ_c)` the adjoint of `∂` is `2c − ∂`, so `i∂` is not symmetric when `c ≠ 0`, and the
   symmetric operator is `i(∂ − c)` (`inner_scaleDeriv_sub`). The module's chart `x = −log t` matches Mathlib's
   `mellin_eq_fourier` and is the mirror of `rh.mellin-half-density`'s `u = log r`, which a join of the two rows must
   read.
3. The box carries no text beyond its title; the reading (the whole derivative on the anchor space, its gradient as the
   adjoint pullback, every curve, the line's quadratic and the descent it gives, and the lift over the anchor space) is
   `agent-inferred` and the module says so. `HNN/Ratio` states its adjoint identity for a continuous read into an inner
   product space but its line results for a linear read into the sup-norm chart `Index → ℝ`, which has no adjoint, and
   the atlas row `hnn.receiving-phase-pullback` writes both with one `R`; the module joins the two (`ownerRead`,
   `ownerRead_surjective`), and the row's scope now names the continuous read. `Objects/RatioPhase`'s `[open]` paragraph
   now points to the convex lift and keeps the rest open.

## 3. What each statement stands on, and what is left

- `Geometry/CayleyTurnClock` states the Cayley chart's turn, its rate against a uniform parameter clock, the clock map
  of its powers, its closure over `ℚ`, the lifted winding with its checked refusal and the joint closure. Cayley points
  over other number fields, the three-dimensional rotation's lifted winding and its join to
  `Transport/HelicalPairInteraction.phaseTransport` (obligation 3 of the September 21 record, trivial on the commutative
  circle), the endpoint discrepancy of a nonclosing orbit and the screw advance are not stated. The box is ticked.
- `Zeta/MellinPlancherel` builds the operator-level ear on the Schwartz core: the unitary, the intertwining, the formal
  adjoint with the norm identity and the Bochner identity for Hearing's symbol. The closure of `∂_c` and the normality
  of the closed operator, its spectrum `c + iℝ`, essential self-adjointness of `i(∂_c − c)`, the unbounded functional
  calculus, the truncations identified with Hearing's coordinate model as a `⋆`-algebra map (only the coordinate is
  matched) and the `L²` membership of an averaged shift (Young's inequality, here a hypothesis) are not stated. The box
  is part done; Hearing's open item names what remains.
- `HNN/AnchorGradient` carries the receiver's comparison back to the whole anchor space and gives the descent of its
  phase part along a gradient step. The moving-weight term's gradient, the grain-quantized score and the odometer chart,
  the excess's second-order terms (bounded by `Resolution.codeLength_quadratic_upper`), lifts over simply connected
  domains that are not convex, the monodromy off them, the integral formula `L(t) = L(a) + ∫ R′/R` and a deposition law
  using the step are not stated; the machine's deposit certifies its own step (`holon.certified-step`). The box is
  ticked.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as unstated or open (the winding guide's and `docs/HELICAL_GEOMETRY.md`'s "need not close", `Transport/SerialChainJacobian`'s "What is not claimed" on the lifted winding, `Zeta/Hearing`'s `[open; #62]` item and `Objects/RatioPhase`'s `[open]` paragraph on higher-dimensional lifts; the `Holonics` module and its importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (8988 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10635 jobs)`, exit 0; `Holonics`, with `Objects/RatioPhase` and its importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
