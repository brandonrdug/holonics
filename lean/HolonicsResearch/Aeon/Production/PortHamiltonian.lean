import Holonics.Aeon.Production.PathReversal
import Holonics.Holon.Element
import Holonics.Holon.Conformance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Production beyond Markov chains: the port-Hamiltonian aeon, the pair contact and the generator

[definition] The aeon record's A5 reads production as the positive, non-closed clock `dS = δQ/T + σ`,
`σ ≥ 0`, and places it in the Holon: `σ` is the resistive term `⟨Jv, D Jv⟩/T`, while the
power-neutral Dirac interconnection and the Cayley reaction contribute zero. `PathReversal` owns the
Markov form (A6: `σ = D(P_γ ‖ P_(Rγ))`, additive over epochs, zero under detailed balance) and leaves
the port-Hamiltonian and continuous-time forms aside. This module states them.

* **The port-Hamiltonian aeon.** An aeon of `n` implicit-midpoint steps
  `q_(k+1) − q_k = h((J − R) Q q̄_k + B u_k)`, `q̄_k = ½(q_k + q_(k+1))`, with effort `e_k = Q q̄_k`
  (`effort`, `IsMidpointAeon`). Its **production** at the bath temperature `T` is
  `Σ_k h ⟨e_k, R e_k⟩ / T` (`stepProduction`, `production`); its supplied work is
  `Σ_k h ⟨e_k, B u_k⟩` (`suppliedWork`); its storage is `Holon/Element.storageEnergy`.
* **The pair contact.** With slip `v ↦ J v` and material `D`, `σ = ⟨Jv, D Jv⟩/T`
  (`contactProduction`).
* **The generator.** A continuous-time chain with generator `L` and law `π` (positive law,
  nonnegative off-diagonal rates with symmetric support: `RateAdmissible`) has the production rate
  `σ_rate = Σ_(x≠y) π_x L_xy log(π_x L_xy / (π_y L_yx))` (`productionRate`); its uniformized chain
  at step `h` is `P_h = I + hL` (`uniformized`), and its detailed balance is
  `π_x L_xy = π_y L_yx` (`RateDetailedBalance`).

[proved-derived; formal-checked] What is proved, the port-Hamiltonian part over any ordered field
(the rationals among them), the Markov part over `ℝ` with the logarithm.

1. **Quadratic forms.** For a symmetric `M` with `⟨s, M s⟩ ≥ 0` everywhere, `⟨s, M s⟩ = 0` forces
   `M s = 0` (`mulVec_eq_zero_of_quad_eq_zero`); without symmetry the form reads only the symmetric
   part: `⟨s, M s⟩ = 0 ⇔ (M + Mᵀ) s = 0` (`quad_eq_zero_iff`, `quad_transpose`), and for symmetric
   `M`, `⇔ M s = 0` (`quad_eq_zero_iff_of_symm`).
2. **Production of the port-Hamiltonian aeon.** For `h ≥ 0`, `T > 0`, `⟨e, R e⟩ ≥ 0`:
   `production ≥ 0` (`stepProduction_nonneg`, `production_nonneg`). It is **additive over epochs**:
   an aeon of `n + m` steps produces the first `n` steps' production plus the shifted aeon's
   (`production_add`, `IsMidpointAeon.shift`, `IsMidpointAeon.mono`), and two aeons that meet at a
   shared state concatenate into an aeon (`concat`, `concatSupply`, `IsMidpointAeon.concat`) whose
   production and supplied work are the sums (`production_concat`, `suppliedWork_concat`). It is
   **the first law's remainder**: `T · production = Σ_k h⟨e_k, B u_k⟩ − (H(q_n) − H(q_0))`
   (`first_law`, telescoping `Holon/Element.midpoint_balance`). It is **zero iff the resistive part
   annihilates every effort**: for `h > 0`, `production = 0 ⇔ (R + Rᵀ) e_k = 0` at every step
   (`production_eq_zero_iff`), and `⇔ R e_k = 0` for symmetric `R`
   (`production_eq_zero_iff_of_symm`).
3. **The skew part contributes nothing.** The graph of a skew `J` is a Dirac structure
   (`Holon/Dirac.skewGraph_isDirac`), so its bond `(J e, e)` carries zero power, `⟨e, J e⟩ = 0`
   (`interconnection_power_zero`); each step's storage change `⟨e_k, q_(k+1) − q_k⟩` is
   `−T σ_k + h⟨e_k, B u_k⟩`, with no `J` term (`step_power`); the production reads the efforts
   alone (`production_congr`), so two aeons with the same efforts produce the same whatever their
   skew parts and supplies; and an aeon with `R = 0` (the Dirac and Cayley parts alone) produces
   nothing and stores every supplied work (`lossless`).
4. **Cycles (Clausius).** On a cycle of the state (`q_n = q_0`) with no supply the production is
   zero, every step dissipates nothing (`h⟨e_k, R e_k⟩ = 0`) and holds its storage
   (`cycle_unsupplied`); with supply, `Σ supplied work = T · production ≥ 0` (`clausius`): a cycle
   cannot return work to its ports.
5. **The pair contact's production.** `σ = ⟨Jv, D Jv⟩/T ≥ 0` for `D ⪰ 0`
   (`contactProduction_nonneg`), zero iff `D J v = 0` for symmetric `D`
   (`contactProduction_eq_zero_iff`); over `ℚ` it is the contact's dissipated power over `T`,
   `T σ = −power(Jv, −D Jv)`, read through `Holon/Conformance.pairContact_resistive`
   (`contactProduction_eq_power`). An aeon whose resistance is the contact material
   `R = Jᵀ D J` produces the sum of the contact productions at its efforts
   (`quad_contactMaterial`, `production_contactMaterial`).
6. **The generator (uniformization).** For every `h ≠ 0`,
   `PathReversal.RealChart.epochProduction π (I + hL) = h · σ_rate`
   (`epochProduction_uniformized`): the diagonal terms read `log 1 = 0` (`log_div_self`) and `h`
   cancels inside each logarithm. With `h > 0` and `h |L_xx| ≤ 1` the uniformized chain is
   admissible for `PathReversal` (`uniformized_admissible`), such an `h` exists
   (`exists_uniformization_step`), and the discrete owner gives `σ_rate ≥ 0`
   (`productionRate_nonneg`) and `σ_rate = 0 ⇔ π_x L_xy = π_y L_yx`
   (`productionRate_eq_zero_iff`, `detailedBalance_uniformized_iff`). With rows of `L` summing to
   `0` and `π L = 0` the uniformized chain is stochastic and stationary (`uniformized_rows`,
   `uniformized_stationary`), and an aeon of `n` epochs of length `h` produces
   `n h σ_rate` (`production_uniformized`): elapsed time times the rate.
7. **Production dominates a quadratic dissipation** [proved-standard; formal-checked]. For
   `a, b > 0`, `(a − b) log(a/b) ≥ 2(a − b)²/(a + b)` (`onsager_le`, from the series of
   `log(1 + x) − log(1 − x)` at `x = (a − b)/(a + b)`), with equality at `a = b`
   (`onsager_eq_of_eq`). Every flow production is half its antisymmetrized form
   (`sum_mul_log_eq_half`, `log_div_swap`), a symmetric sum with zero diagonal is twice its strict
   upper half (`sum_sum_eq_two_mul_lt`), and so the Markov production dominates the dissipation
   `Σ_(x<y) j_xy² / R_xy` of the net currents `j_xy = J_xy − J_yx` through the edge coefficients
   `R_xy = (J_xy + J_yx)/2` (`netCurrent`, `onsagerCoefficient`, `quadraticDissipation`,
   `quadraticDissipation_eq`, `sum_mul_log_ge_quadraticDissipation`,
   `epochProduction_ge_quadraticDissipation`). In the port-Hamiltonian chart `j²/R = ⟨e, R e⟩` at
   the effort `e = R⁻¹ j` (`dissipation_effort_form`).
8. **Witnesses** [counterexample; formal-checked]. The biased three-state rotation's generator
   (`2/3` forward, `1/3` back, `−1` on the diagonal) is admissible, conservative and stationary
   for the uniform law (`Rotation.admissible`, `Rotation.rows`, `Rotation.stationary`), its
   uniformization at `h = 1` is `PathReversal.Rotation.P` (`Rotation.diag`,
   `Rotation.uniformized_one`, `Rotation.law_eq`), and
   `σ_rate = (1/3) log 2 > 0` per unit time, so it is not in detailed balance
   (`Rotation.rotation_productionRate`, through `PathReversal.Rotation.rotation_production_pos`).
   A one-resistor midpoint aeon (`Q = 1`, `J = 0`, `R = r · 1`, `r > 0`, `h > 0`) from a nonzero
   state with no supply produces `(H(q_0) − H(q_n))/T > 0` (`oneResistor_production_pos`); the
   aeon `q_k = 3^(−k)` at `r = h = 1` is one (`thirdAeon_isMidpointAeon`), producing
   `(1 − 9^(−n))/(2T)` (`thirdAeon_production`).

Sources: the box of #410, "Production beyond Markov chains: `production(aeon)` for
port-Hamiltonian instances"; the record
`research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md`, §A5
(`dS = δQ/T + σ`, Clausius, the Holon reading of `σ`), §A6 (irreversibility is a relative entropy)
and its Rust obligation "`production(aeon)` for Markov and port-Hamiltonian instances"; the closing
note of `Aeon/Production/PathReversal`, which left the continuous-time and port-Hamiltonian forms of
production (`⟨Jv, DJv⟩/T`) aside and now points here; the Holon's open paragraph in `CLAUDE.md`
("Passivity is proved, never assumed") and its paragraph "Cross-entropy is physical". The owners
read: `Aeon/Production/PathReversal` (`flow`, `DetailedBalance`, `Admissible`, `flow_nonneg`,
`flow_support`, `flow_zero_of_zero`, `RealChart.epochProduction`, `RealChart.production`,
`RealChart.epochProduction_nonneg`, `RealChart.epochProduction_eq_zero_iff`,
`RealChart.production_eq_mul`, `epochProduction_eq_real`, `Rotation`), `Aeon/Production/Kac`
(`Stationary`), `Holon/Element` (`storageEnergy`, `symm_dot`, `midpoint_balance`), `Holon/Dirac`
(`skewGraph_isDirac`, `IsDirac.power_eq_zero`, `power`, `Bond`) and `Holon/Conformance`
(`pairContact_resistive`); read and not imported, `Holon/Cayley` (`midpoint_reaction_balance` is
`first_law` at one step with `Q = 1`, `B = 0`; `cayley_isometry_real` is `lossless` with `Q = 1`,
`u = 0`) and `Physics/Thermal/ViscousPort` (a port's production `W/T`, a sibling instance).
Atlas rows served: `aeon.a5-production-clock` (its Holon reading of `σ`),
`aeon.a6-irreversibility-kl` and `aeon.production-additive` (their continuous-time and
port-Hamiltonian instances), `code.edge-production` (item 7 is its quadratic lower bound, in nats).
Rows read: `contact.power`, `holon.midpoint-balance-exact`, `holon.power-neutral`,
`holon.dirac-form-step`, `gr.two-way-flow-parts` (with `S = (F_ab + F_ba)/2`, `β = J/S`,
`a = ½ log(F_ab/F_ba) = artanh β`, item 7 reads `β artanh β ≥ β²`), `thermal.partition-de-bruijn`,
`heat.viscous-port`, `heat.cut-production`.

What is not claimed. Stochastic port-Hamiltonian systems with noise and their path-measure
production (`D(P_γ ‖ P_(Rγ))` for a Langevin process); the continuum limit `h → 0` of the midpoint
aeon (the production here is the discrete scheme's, whose balance has zero residual; no convergence
to `∫⟨e, R e⟩ dt / T` is stated); the Kolmogorov–Sinai entropy of either flow; the first-order
equality of item 7 near detailed balance (only the inequality and the equality at `a = b` are
proved); a temperature that varies along the aeon (one bath temperature `T` reads every step); and
the reading of `T · production` as heat delivered to a bath, which is the canonical chart's word
for the first law's remainder, not derived here.

The computational object is the helical pair interaction read on its dissipation: production
enters only at the pair contact, the slip `J v` against the contact material `D` (the boost of a
swing, the self-adjoint part of a rate), while the skew interconnection (the turn, whose implicit
midpoint is the Cayley isometry) carries no power; in the Markov chart the same pair is the two
one-way flows `(J_xy, J_yx)` of an edge, whose odd part is the net current and whose even part is the
edge coefficient. Of the winding guide's six general objects this touches the pair (the contact's
slip and material, and the edge's two-way flow), the tube (the aeon of midpoint steps as a clocked
span, cut into epochs and concatenated) and cell holonomy (a cycle of the state, on which the
supplied work is the production: Clausius); the helix, faces and placement and the tower thread
stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.PortHamiltonian

open Finset Matrix
open Holonics.HolonCore

/-! ## 0. Quadratic forms -/

section Quad

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {σ : Type*} [Fintype σ]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-standard; formal-checked] `⟨s, Mᵀ s⟩ = ⟨s, M s⟩`. -/
theorem quad_transpose (M : Matrix σ σ 𝕜) (s : σ → 𝕜) : s ⬝ᵥ (Mᵀ *ᵥ s) = s ⬝ᵥ (M *ᵥ s) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- [proved-standard; formal-checked] **A symmetric nonnegative form vanishes only on its kernel**:
`⟨s, M s⟩ = 0 ⇒ M s = 0`. -/
theorem mulVec_eq_zero_of_quad_eq_zero {M : Matrix σ σ 𝕜} (hM : Mᵀ = M)
    (hpos : ∀ s, 0 ≤ s ⬝ᵥ (M *ᵥ s)) {s : σ → 𝕜} (h0 : s ⬝ᵥ (M *ᵥ s) = 0) : M *ᵥ s = 0 := by
  have hexp : ∀ t : 𝕜, (s + t • (M *ᵥ s)) ⬝ᵥ (M *ᵥ (s + t • (M *ᵥ s))) =
      2 * t * ((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) + t ^ 2 * ((M *ᵥ s) ⬝ᵥ (M *ᵥ (M *ᵥ s))) := by
    intro t
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [h0, symm_dot hM s (M *ᵥ s)]
    ring
  have ha : 0 ≤ (M *ᵥ s) ⬝ᵥ (M *ᵥ s) := by
    simp only [dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _
  have hb : 0 ≤ (M *ᵥ s) ⬝ᵥ (M *ᵥ (M *ᵥ s)) := hpos _
  obtain ⟨a, rfl⟩ : ∃ a, a = (M *ᵥ s) ⬝ᵥ (M *ᵥ s) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = (M *ᵥ s) ⬝ᵥ (M *ᵥ (M *ᵥ s)) := ⟨_, rfl⟩
  rw [← hbdef] at hb hexp
  have hb1 : 0 < b + 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = -((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) / (b + 1) := ⟨_, rfl⟩
  have htb : t * (b + 1) = -((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) := by rw [ht, div_mul_cancel₀ _ hb1.ne']
  have key : 0 ≤ 2 * t * ((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) + t ^ 2 * b := by rw [← hexp]; exact hpos _
  have hprod := mul_nonneg key (sq_nonneg (b + 1))
  have hid : (2 * t * ((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) + t ^ 2 * b) * (b + 1) ^ 2 =
      -(((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) ^ 2 * (b + 2)) := by
    linear_combination (2 * ((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) * (b + 1) +
      b * (t * (b + 1) - (M *ᵥ s) ⬝ᵥ (M *ᵥ s))) * htb
  have hsq : ((M *ᵥ s) ⬝ᵥ (M *ᵥ s)) ^ 2 = 0 :=
    le_antisymm (by nlinarith) (sq_nonneg _)
  exact dotProduct_self_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- [proved-standard; formal-checked] **The form reads only the symmetric part**: for a
nonnegative form, `⟨s, M s⟩ = 0 ⇔ (M + Mᵀ) s = 0`. -/
theorem quad_eq_zero_iff {M : Matrix σ σ 𝕜} (hpos : ∀ s, 0 ≤ s ⬝ᵥ (M *ᵥ s)) (s : σ → 𝕜) :
    s ⬝ᵥ (M *ᵥ s) = 0 ↔ (M + Mᵀ) *ᵥ s = 0 := by
  have hsum : ∀ v, v ⬝ᵥ ((M + Mᵀ) *ᵥ v) = 2 * (v ⬝ᵥ (M *ᵥ v)) := by
    intro v; rw [add_mulVec, dotProduct_add, quad_transpose]; ring
  have hsym : (M + Mᵀ)ᵀ = M + Mᵀ := by rw [transpose_add, transpose_transpose, add_comm]
  constructor
  · intro h0
    exact mulVec_eq_zero_of_quad_eq_zero hsym
      (fun v => by rw [hsum]; exact mul_nonneg zero_le_two (hpos v)) (by rw [hsum, h0, mul_zero])
  · intro h
    have := hsum s
    rw [h, dotProduct_zero] at this
    linarith

/-- [proved-standard; formal-checked] For a symmetric nonnegative form, `⟨s, M s⟩ = 0 ⇔ M s = 0`. -/
theorem quad_eq_zero_iff_of_symm {M : Matrix σ σ 𝕜} (hM : Mᵀ = M)
    (hpos : ∀ s, 0 ≤ s ⬝ᵥ (M *ᵥ s)) (s : σ → 𝕜) : s ⬝ᵥ (M *ᵥ s) = 0 ↔ M *ᵥ s = 0 := by
  rw [quad_eq_zero_iff hpos, hM, add_mulVec, ← two_smul 𝕜 (M *ᵥ s), smul_eq_zero,
    or_iff_right two_ne_zero]

end Quad

/-! ## 1. The port-Hamiltonian aeon -/

section Aeon

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {σ μ : Type*} [Fintype σ] [Fintype μ]

/-- [definition] The midpoint effort of step `k`: `e_k = Q q̄_k`, `q̄_k = ½(q_k + q_(k+1))`. -/
def effort (Q : Matrix σ σ 𝕜) (q : ℕ → σ → 𝕜) (k : ℕ) : σ → 𝕜 :=
  Q *ᵥ ((1 / 2 : 𝕜) • (q k + q (k + 1)))

/-- [definition] **A midpoint aeon of `n` steps**: `q_(k+1) − q_k = h((J − R) e_k + B u_k)` for
every `k < n`. -/
def IsMidpointAeon (Q J R : Matrix σ σ 𝕜) (B : Matrix σ μ 𝕜) (h : 𝕜) (q : ℕ → σ → 𝕜)
    (u : ℕ → μ → 𝕜) (n : ℕ) : Prop :=
  ∀ k < n, q (k + 1) - q k = h • ((J - R) *ᵥ effort Q q k + B *ᵥ u k)

/-- [definition] The production of step `k` at the bath temperature `T`: `h ⟨e_k, R e_k⟩ / T`. -/
def stepProduction (Q R : Matrix σ σ 𝕜) (h T : 𝕜) (q : ℕ → σ → 𝕜) (k : ℕ) : 𝕜 :=
  h * (effort Q q k ⬝ᵥ (R *ᵥ effort Q q k)) / T

/-- [definition] **The production of an aeon of `n` steps**: `Σ_(k<n) h ⟨e_k, R e_k⟩ / T`. -/
def production (Q R : Matrix σ σ 𝕜) (h T : 𝕜) (q : ℕ → σ → 𝕜) (n : ℕ) : 𝕜 :=
  ∑ k ∈ range n, stepProduction Q R h T q k

/-- [definition] The work supplied through the ports along `n` steps: `Σ_(k<n) h ⟨e_k, B u_k⟩`. -/
def suppliedWork (Q : Matrix σ σ 𝕜) (B : Matrix σ μ 𝕜) (h : 𝕜) (q : ℕ → σ → 𝕜) (u : ℕ → μ → 𝕜)
    (n : ℕ) : 𝕜 :=
  ∑ k ∈ range n, h * (effort Q q k ⬝ᵥ (B *ᵥ u k))

variable {Q J R : Matrix σ σ 𝕜} {B : Matrix σ μ 𝕜} {h T : 𝕜} {q : ℕ → σ → 𝕜} {u : ℕ → μ → 𝕜}

/-! ### Sign -/

/-- [proved-derived; formal-checked] Each step produces `h⟨e_k, R e_k⟩/T ≥ 0`. -/
theorem stepProduction_nonneg (hh : 0 ≤ h) (hT : 0 < T) (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) (k : ℕ) :
    0 ≤ stepProduction Q R h T q k :=
  div_nonneg (mul_nonneg hh (hR _)) hT.le

/-- [proved-derived; formal-checked] **The production of an aeon is nonnegative.** -/
theorem production_nonneg (hh : 0 ≤ h) (hT : 0 < T) (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) (n : ℕ) :
    0 ≤ production Q R h T q n :=
  sum_nonneg fun k _ => stepProduction_nonneg hh hT hR k

/-! ### Additivity over epochs -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The efforts of a shifted aeon are the shifted efforts. -/
theorem effort_shift (Q : Matrix σ σ 𝕜) (q : ℕ → σ → 𝕜) (n k : ℕ) :
    effort Q (fun j => q (n + j)) k = effort Q q (n + k) := rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **Production is additive over epochs**: an aeon of `n + m`
steps produces its first `n` steps' production plus that of the aeon that starts at `q_n`. -/
theorem production_add (Q R : Matrix σ σ 𝕜) (h T : 𝕜) (q : ℕ → σ → 𝕜) (n m : ℕ) :
    production Q R h T q (n + m) =
      production Q R h T q n + production Q R h T (fun j => q (n + j)) m := by
  unfold production
  rw [sum_range_add]
  rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] An aeon of `n` steps restricts to its first `m ≤ n` steps. -/
theorem IsMidpointAeon.mono {n m : ℕ} (ha : IsMidpointAeon Q J R B h q u n) (hmn : m ≤ n) :
    IsMidpointAeon Q J R B h q u m :=
  fun k hk => ha k (lt_of_lt_of_le hk hmn)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] An aeon of `n + m` steps, read from `q_n`, is an aeon of `m`
steps. -/
theorem IsMidpointAeon.shift {n m : ℕ} (ha : IsMidpointAeon Q J R B h q u (n + m)) :
    IsMidpointAeon Q J R B h (fun j => q (n + j)) (fun j => u (n + j)) m :=
  fun k hk => ha (n + k) (by omega)

/-- [definition] **Concatenation of two aeons** at step `n`: the first up to `q₁ n`, then the
second. -/
def concat {X : Type*} (n : ℕ) (q₁ q₂ : ℕ → X) : ℕ → X := fun k => if k ≤ n then q₁ k else q₂ (k - n)

/-- [definition] Concatenation of two supplies at step `n`. -/
def concatSupply {X : Type*} (n : ℕ) (u₁ u₂ : ℕ → X) : ℕ → X :=
  fun k => if k < n then u₁ k else u₂ (k - n)

section Concat

variable {X : Type*} {n : ℕ} {q₁ q₂ : ℕ → X}

/-- [proved-derived; formal-checked] Up to step `n` the concatenation is the first aeon. -/
theorem concat_of_le {k : ℕ} (hk : k ≤ n) : concat n q₁ q₂ k = q₁ k := if_pos hk

/-- [proved-derived; formal-checked] From step `n` on the concatenation is the second aeon, when
the two meet at `q₁ n = q₂ 0`. -/
theorem concat_add (hj : q₁ n = q₂ 0) (j : ℕ) : concat n q₁ q₂ (n + j) = q₂ j := by
  unfold concat
  split_ifs with hle
  · have hj0 : j = 0 := by omega
    subst hj0
    simpa using hj
  · congr 1; omega

/-- [proved-derived; formal-checked] The concatenation read from step `n` is the second aeon. -/
theorem concat_shift (hj : q₁ n = q₂ 0) : (fun j => concat n q₁ q₂ (n + j)) = q₂ :=
  funext (concat_add hj)

end Concat

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] Before step `n` the concatenation has the first aeon's
efforts. -/
theorem effort_concat_of_lt {n k : ℕ} {q₁ q₂ : ℕ → σ → 𝕜} (hk : k < n) :
    effort Q (concat n q₁ q₂) k = effort Q q₁ k := by
  simp only [effort, concat_of_le hk.le, concat_of_le (Nat.succ_le_of_lt hk)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] From step `n` on the concatenation has the second aeon's
efforts. -/
theorem effort_concat_add {n : ℕ} {q₁ q₂ : ℕ → σ → 𝕜} (hj : q₁ n = q₂ 0) (j : ℕ) :
    effort Q (concat n q₁ q₂) (n + j) = effort Q q₂ j := by
  simp only [effort]
  rw [show n + j + 1 = n + (j + 1) by omega, concat_add hj, concat_add hj]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **Two aeons that meet at a shared state concatenate into an
aeon.** -/
theorem IsMidpointAeon.concat {n m : ℕ} {q₁ q₂ : ℕ → σ → 𝕜} {u₁ u₂ : ℕ → μ → 𝕜}
    (h₁ : IsMidpointAeon Q J R B h q₁ u₁ n) (h₂ : IsMidpointAeon Q J R B h q₂ u₂ m)
    (hj : q₁ n = q₂ 0) :
    IsMidpointAeon Q J R B h (concat n q₁ q₂) (concatSupply n u₁ u₂) (n + m) := by
  intro k hk
  by_cases hkn : k < n
  · rw [effort_concat_of_lt hkn, concat_of_le hkn.le, concat_of_le (Nat.succ_le_of_lt hkn)]
    simp only [concatSupply, if_pos hkn]
    exact h₁ k hkn
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    have hjm : j < m := by omega
    rw [effort_concat_add hj, show n + j + 1 = n + (j + 1) by omega, concat_add hj,
      concat_add hj]
    simp only [concatSupply, if_neg (show ¬ n + j < n by omega), Nat.add_sub_cancel_left]
    exact h₂ j hjm

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **Concatenating aeons adds their productions.** -/
theorem production_concat {n m : ℕ} {q₁ q₂ : ℕ → σ → 𝕜} (hj : q₁ n = q₂ 0) :
    production Q R h T (concat n q₁ q₂) (n + m) =
      production Q R h T q₁ n + production Q R h T q₂ m := by
  rw [production_add, concat_shift hj]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  simp only [stepProduction, effort_concat_of_lt (mem_range.mp hk)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] Concatenating aeons adds their supplied works. -/
theorem suppliedWork_concat {n m : ℕ} {q₁ q₂ : ℕ → σ → 𝕜} {u₁ u₂ : ℕ → μ → 𝕜}
    (hj : q₁ n = q₂ 0) :
    suppliedWork Q B h (concat n q₁ q₂) (concatSupply n u₁ u₂) (n + m) =
      suppliedWork Q B h q₁ u₁ n + suppliedWork Q B h q₂ u₂ m := by
  unfold suppliedWork
  rw [sum_range_add]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have hkn := mem_range.mp hk
    simp only [effort_concat_of_lt hkn, concatSupply, if_pos hkn]
  · refine sum_congr rfl fun j _ => ?_
    simp only [effort_concat_add hj, concatSupply, if_neg (show ¬ n + j < n by omega),
      Nat.add_sub_cancel_left]

/-! ### The first law -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **Production is the first law's remainder**: along a midpoint
aeon, `T · production = Σ_k h⟨e_k, B u_k⟩ − (H(q_n) − H(q_0))`, the supplied work less the stored
energy, from `midpoint_balance` at each step. -/
theorem first_law [CharZero 𝕜] (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (hT : T ≠ 0) {n : ℕ}
    (ha : IsMidpointAeon Q J R B h q u n) :
    T * production Q R h T q n =
      suppliedWork Q B h q u n - (storageEnergy Q (q n) - storageEnergy Q (q 0)) := by
  rw [← sum_range_sub (fun k => storageEnergy Q (q k)) n]
  unfold production suppliedWork stepProduction
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hb := midpoint_balance hQ hJ B h (q k) (q (k + 1)) (u k) (ha k (mem_range.mp hk))
  rw [mul_div_cancel₀ _ hT]
  simp only [effort]
  rw [hb]
  ring

/-! ### The zero set -/

/-- [proved-derived; formal-checked] **Production is zero iff the resistive part annihilates every
effort**: for `h > 0`, `T > 0` and `⟨e, R e⟩ ≥ 0`, `production = 0 ⇔ (R + Rᵀ) e_k = 0` for every
`k < n`. -/
theorem production_eq_zero_iff (hh : 0 < h) (hT : 0 < T) (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) (n : ℕ) :
    production Q R h T q n = 0 ↔ ∀ k < n, (R + Rᵀ) *ᵥ effort Q q k = 0 := by
  unfold production
  rw [sum_eq_zero_iff_of_nonneg fun k _ => stepProduction_nonneg hh.le hT hR k]
  refine forall_congr' fun k => ?_
  rw [mem_range]
  refine imp_congr_right fun _ => ?_
  rw [stepProduction, div_eq_zero_iff, or_iff_left hT.ne', mul_eq_zero, or_iff_right hh.ne',
    quad_eq_zero_iff hR]

/-- [proved-derived; formal-checked] For symmetric `R ⪰ 0` and `h > 0`:
`production = 0 ⇔ R e_k = 0` at every step. -/
theorem production_eq_zero_iff_of_symm (hh : 0 < h) (hT : 0 < T) (hRs : Rᵀ = R)
    (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) (n : ℕ) :
    production Q R h T q n = 0 ↔ ∀ k < n, R *ᵥ effort Q q k = 0 := by
  rw [production_eq_zero_iff hh hT hR]
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [hRs, add_mulVec, ← two_smul 𝕜 (R *ᵥ effort Q q k), smul_eq_zero, or_iff_right two_ne_zero]

/-! ### The skew part contributes nothing -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The interconnection carries no power**: the graph of a skew
`J` is a Dirac structure, so its bond `(J e, e)` carries `⟨e, J e⟩ = 0`. -/
theorem interconnection_power_zero [CharZero 𝕜] [DecidableEq σ] (hJ : Jᵀ = -J) (e : σ → 𝕜) :
    e ⬝ᵥ (J *ᵥ e) = 0 :=
  (skewGraph_isDirac hJ).power_eq_zero (b := (J *ᵥ e, e)) rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The step's balance has no skew term**: on a midpoint aeon
the storage change of step `k` is `⟨e_k, q_(k+1) − q_k⟩ = −T σ_k + h⟨e_k, B u_k⟩`. -/
theorem step_power [CharZero 𝕜] [DecidableEq σ] (hJ : Jᵀ = -J) (hT : T ≠ 0) {n k : ℕ}
    (ha : IsMidpointAeon Q J R B h q u n) (hk : k < n) :
    effort Q q k ⬝ᵥ (q (k + 1) - q k) =
      -(T * stepProduction Q R h T q k) + h * (effort Q q k ⬝ᵥ (B *ᵥ u k)) := by
  rw [ha k hk, dotProduct_smul, dotProduct_add, sub_mulVec, dotProduct_sub,
    interconnection_power_zero hJ, stepProduction, mul_div_cancel₀ _ hT, smul_eq_mul]
  ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The production reads the efforts alone**: two aeons with the
same efforts at every step produce the same, whatever their skew parts and supplies. -/
theorem production_congr {q q' : ℕ → σ → 𝕜} {n : ℕ} (he : ∀ k < n, effort Q q k = effort Q q' k) :
    production Q R h T q n = production Q R h T q' n :=
  sum_congr rfl fun k hk => by simp only [stepProduction, he k (mem_range.mp hk)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The Dirac and Cayley parts alone produce nothing**: an aeon
with `R = 0` has zero production and stores every supplied work,
`H(q_n) − H(q_0) = Σ h⟨e_k, B u_k⟩`. -/
theorem lossless [CharZero 𝕜] (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (hT : T ≠ 0) {n : ℕ}
    (ha : IsMidpointAeon Q J 0 B h q u n) :
    production Q 0 h T q n = 0 ∧
      storageEnergy Q (q n) - storageEnergy Q (q 0) = suppliedWork Q B h q u n := by
  have h0 : production Q 0 h T q n = 0 := by
    simp [production, stepProduction]
  have hfl := first_law hQ hJ hT ha
  rw [h0, mul_zero] at hfl
  exact ⟨h0, by linear_combination hfl⟩

/-! ### Cycles: Clausius -/

/-- [proved-derived; formal-checked] **An unsupplied cycle produces nothing**: if `q_n = q_0` and
`u_k = 0`, the production is zero, every step dissipates `h⟨e_k, R e_k⟩ = 0` and holds its
storage. -/
theorem cycle_unsupplied (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (hh : 0 ≤ h) (hT : 0 < T)
    (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) {n : ℕ} (ha : IsMidpointAeon Q J R B h q u n)
    (hc : q n = q 0) (hu : ∀ k < n, u k = 0) :
    production Q R h T q n = 0 ∧ ∀ k < n, h * (effort Q q k ⬝ᵥ (R *ᵥ effort Q q k)) = 0 ∧
      storageEnergy Q (q (k + 1)) = storageEnergy Q (q k) := by
  have hW : suppliedWork Q B h q u n = 0 :=
    sum_eq_zero fun k hk => by rw [hu k (mem_range.mp hk), mulVec_zero, dotProduct_zero, mul_zero]
  have hP : production Q R h T q n = 0 := by
    have hfl := first_law hQ hJ hT.ne' ha
    simp only [hW, hc, sub_self] at hfl
    exact (mul_eq_zero.mp hfl).resolve_left hT.ne'
  refine ⟨hP, fun k hk => ?_⟩
  have hterm : stepProduction Q R h T q k = 0 :=
    (sum_eq_zero_iff_of_nonneg fun i _ => stepProduction_nonneg hh hT hR i).mp hP k
      (mem_range.mpr hk)
  have hd : h * (effort Q q k ⬝ᵥ (R *ᵥ effort Q q k)) = 0 := by
    rw [stepProduction, div_eq_zero_iff] at hterm
    exact hterm.resolve_right hT.ne'
  refine ⟨hd, ?_⟩
  have hb := midpoint_balance hQ hJ B h (q k) (q (k + 1)) (u k) (ha k hk)
  rw [hu k hk, mulVec_zero, dotProduct_zero, mul_zero, add_zero] at hb
  simp only [effort] at hd
  rw [hd, neg_zero] at hb
  exact sub_eq_zero.mp hb

/-- [proved-derived; formal-checked] **Clausius: a cycle cannot return work.** On a cycle of the
state (`q_n = q_0`) the supplied work is `T · production`, hence `≥ 0`. -/
theorem clausius (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (hh : 0 ≤ h) (hT : 0 < T)
    (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) {n : ℕ} (ha : IsMidpointAeon Q J R B h q u n)
    (hc : q n = q 0) :
    suppliedWork Q B h q u n = T * production Q R h T q n ∧ 0 ≤ suppliedWork Q B h q u n := by
  have hfl := first_law hQ hJ hT.ne' ha
  rw [hc, sub_self, sub_zero] at hfl
  refine ⟨hfl.symm, ?_⟩
  rw [← hfl]
  exact mul_nonneg hT.le (production_nonneg hh hT hR n)

end Aeon

/-! ## 2. The pair contact's production -/

section Contact

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ρ ν σ : Type*} [Fintype ρ] [Fintype ν] [Fintype σ]

/-- [definition] **The pair contact's production** `σ = ⟨Jv, D Jv⟩ / T`: the slip `J v` through the
contact material `D`, at the bath temperature `T`. -/
def contactProduction (Jc : Matrix ρ ν 𝕜) (D : Matrix ρ ρ 𝕜) (T : 𝕜) (v : ν → 𝕜) : 𝕜 :=
  (Jc *ᵥ v) ⬝ᵥ (D *ᵥ (Jc *ᵥ v)) / T

/-- [proved-derived; formal-checked] `σ ≥ 0` for `D ⪰ 0` and `T > 0`. -/
theorem contactProduction_nonneg {Jc : Matrix ρ ν 𝕜} {D : Matrix ρ ρ 𝕜} {T : 𝕜} (hT : 0 < T)
    (hD : ∀ s, 0 ≤ s ⬝ᵥ (D *ᵥ s)) (v : ν → 𝕜) : 0 ≤ contactProduction Jc D T v :=
  div_nonneg (hD _) hT.le

/-- [proved-derived; formal-checked] **The contact produces nothing precisely where its material
holds no traction**: `σ = 0 ⇔ D J v = 0`, for symmetric `D ⪰ 0`. -/
theorem contactProduction_eq_zero_iff {Jc : Matrix ρ ν 𝕜} {D : Matrix ρ ρ 𝕜} {T : 𝕜} (hT : 0 < T)
    (hDs : Dᵀ = D) (hD : ∀ s, 0 ≤ s ⬝ᵥ (D *ᵥ s)) (v : ν → 𝕜) :
    contactProduction Jc D T v = 0 ↔ D *ᵥ (Jc *ᵥ v) = 0 := by
  rw [contactProduction, div_eq_zero_iff, or_iff_left hT.ne']
  exact quad_eq_zero_iff_of_symm hDs hD _

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-standard; formal-checked] The contact material's form: `⟨e, Jᵀ D J e⟩ = ⟨J e, D J e⟩`. -/
theorem quad_contactMaterial (Jc : Matrix ρ σ 𝕜) (D : Matrix ρ ρ 𝕜) (e : σ → 𝕜) :
    e ⬝ᵥ ((Jcᵀ * D * Jc) *ᵥ e) = (Jc *ᵥ e) ⬝ᵥ (D *ᵥ (Jc *ᵥ e)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **An aeon through a contact produces its contact's
production**: with resistance `R = Jᵀ D J`, `production = Σ_k h σ_contact(e_k)`. -/
theorem production_contactMaterial (Q : Matrix σ σ 𝕜) (Jc : Matrix ρ σ 𝕜) (D : Matrix ρ ρ 𝕜)
    (h T : 𝕜) (q : ℕ → σ → 𝕜) (n : ℕ) :
    production Q (Jcᵀ * D * Jc) h T q n =
      ∑ k ∈ range n, h * contactProduction Jc D T (effort Q q k) := by
  unfold production stepProduction contactProduction
  refine sum_congr rfl fun k _ => ?_
  rw [quad_contactMaterial, mul_div_assoc]

/-- [proved-derived; formal-checked] **The contact's production is its dissipated power over `T`**
(over `ℚ`, through `pairContact_resistive`): `T σ = −power(Jv, −D Jv)`, and `σ ≥ 0` from the
element's passivity. -/
theorem contactProduction_eq_power {r n : ℕ} (Jc : Matrix (Fin r) (Fin n) ℚ)
    (D : Matrix (Fin r) (Fin r) ℚ) (hD : ∀ s, 0 ≤ s ⬝ᵥ (D *ᵥ s)) {T : ℚ} (hT : 0 < T)
    (v : Fin n → ℚ) :
    T * contactProduction Jc D T v = -power ((Jc *ᵥ v, -(D *ᵥ (Jc *ᵥ v))) : Bond ℚ (Fin r)) ∧
      0 ≤ contactProduction Jc D T v := by
  have h1 := (pairContact_resistive Jc D hD v).1
  have h2 := (pairContact_resistive Jc D hD v).2
  rw [Transport.HolonicInteraction.quad_faceForm, one_mul] at h1
  have hx : T * contactProduction Jc D T v = (Jc *ᵥ v) ⬝ᵥ (D *ᵥ (Jc *ᵥ v)) := by
    rw [contactProduction, mul_div_cancel₀ _ hT.ne']
  refine ⟨by rw [hx, h1, neg_neg], ?_⟩
  rw [h1] at h2
  exact div_nonneg (by linarith) hT.le

end Contact

/-! ## 3. Continuous-time chains: the generator and its uniformization -/

section Rate

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- [definition] **The uniformized chain** `P_h = I + hL` of a generator `L` at step `h`. -/
def uniformized (L : S → S → ℝ) (h : ℝ) : S → S → ℝ :=
  fun x y => (if x = y then 1 else 0) + h * L x y

/-- [definition] **The production rate** of a generator `L` at the law `π`:
`σ_rate = Σ_(x≠y) π_x L_xy log(π_x L_xy / (π_y L_yx))`. -/
def productionRate (π : S → ℝ) (L : S → S → ℝ) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else π x * L x y * Real.log (π x * L x y / (π y * L y x))

/-- [definition] The hypotheses on a generator and its law: `π > 0`, off-diagonal rates `≥ 0`, and
symmetric support off the diagonal. -/
structure RateAdmissible (π : S → ℝ) (L : S → S → ℝ) : Prop where
  pos : ∀ x, 0 < π x
  offDiag_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y
  support : ∀ x y, x ≠ y → 0 < L x y → 0 < L y x

/-- [definition] **Detailed balance of a generator**: `π_x L_xy = π_y L_yx` for all `x`, `y`. -/
def RateDetailedBalance (π : S → ℝ) (L : S → S → ℝ) : Prop := ∀ x y, π x * L x y = π y * L y x

omit [Fintype S] [DecidableEq S] in
/-- [proved-standard; formal-checked] `log(a/a) = 0`, at `a = 0` too (`log 0 = 0`). -/
theorem log_div_self (a : ℝ) : Real.log (a / a) = 0 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  · rw [div_self h, Real.log_one]

/-- [proved-derived; formal-checked] **Uniformization reads the rate**: for every `h ≠ 0`,
`epochProduction π (I + hL) = h · σ_rate`. The diagonal terms read `log 1 = 0` and `h` cancels
inside each logarithm. -/
theorem epochProduction_uniformized (π : S → ℝ) (L : S → S → ℝ) {h : ℝ} (hh : h ≠ 0) :
    PathReversal.RealChart.epochProduction π (uniformized L h) = h * productionRate π L := by
  unfold PathReversal.RealChart.epochProduction productionRate
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [PathReversal.flow]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, log_div_self, mul_zero, mul_zero]
  · have hyx : y ≠ x := Ne.symm hxy
    simp only [uniformized, if_neg hxy, if_neg hyx, zero_add]
    have e1 : π x * (h * L x y) = h * (π x * L x y) := by ring
    have e2 : π y * (h * L y x) = h * (π y * L y x) := by ring
    rw [e1, e2, mul_div_mul_left _ _ hh]
    ring

omit [Fintype S] in
/-- [proved-derived; formal-checked] With `h > 0` and `h |L_xx| ≤ 1` the uniformized chain is
admissible for `PathReversal`: positive law, nonnegative entries, symmetric support. -/
theorem uniformized_admissible {π : S → ℝ} {L : S → S → ℝ} (hA : RateAdmissible π L) {h : ℝ}
    (hh : 0 < h) (hdiag : ∀ x, h * |L x x| ≤ 1) : PathReversal.Admissible π (uniformized L h) where
  pos := hA.pos
  nonneg x y := by
    by_cases hxy : x = y
    · subst hxy
      show 0 ≤ (if x = x then (1 : ℝ) else 0) + h * L x x
      rw [if_pos rfl]
      have := mul_le_mul_of_nonneg_left (neg_abs_le (L x x)) hh.le
      linarith [hdiag x]
    · simp only [uniformized, if_neg hxy, zero_add]
      exact mul_nonneg hh.le (hA.offDiag_nonneg x y hxy)
  support x y hp := by
    by_cases hxy : x = y
    · subst hxy; exact hp
    · simp only [uniformized, if_neg hxy, if_neg (Ne.symm hxy), zero_add] at hp ⊢
      exact mul_pos hh (hA.support x y hxy (pos_of_mul_pos_right hp hh.le))

omit [DecidableEq S] in
/-- [proved-derived; formal-checked] A uniformization step exists:
`h = 1/(1 + Σ_x |L_xx|)` has `h > 0` and `h |L_xx| ≤ 1`. -/
theorem exists_uniformization_step (L : S → S → ℝ) : ∃ h : ℝ, 0 < h ∧ ∀ x, h * |L x x| ≤ 1 := by
  have hpos : 0 < 1 + ∑ z, |L z z| := by positivity
  refine ⟨1 / (1 + ∑ z, |L z z|), by positivity, fun x => ?_⟩
  have hs : |L x x| ≤ ∑ z, |L z z| :=
    single_le_sum (f := fun z => |L z z|) (fun z _ => abs_nonneg _) (mem_univ x)
  rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
  linarith

omit [Fintype S] in
/-- [proved-derived; formal-checked] Detailed balance of the uniformized chain is detailed balance
of the generator, for every `h ≠ 0`. -/
theorem detailedBalance_uniformized_iff (π : S → ℝ) (L : S → S → ℝ) {h : ℝ} (hh : h ≠ 0) :
    PathReversal.DetailedBalance π (uniformized L h) ↔ RateDetailedBalance π L := by
  unfold PathReversal.DetailedBalance RateDetailedBalance
  refine forall₂_congr fun x y => ?_
  simp only [PathReversal.flow]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp only [uniformized, if_neg hxy, if_neg (Ne.symm hxy), zero_add]
    constructor
    · intro h1
      apply mul_left_cancel₀ hh
      linear_combination h1
    · intro h1
      linear_combination h * h1

/-- [proved-derived; formal-checked] **`σ_rate ≥ 0`**, from the discrete owner's
`epochProduction_nonneg` at a uniformization step. -/
theorem productionRate_nonneg {π : S → ℝ} {L : S → S → ℝ} (hA : RateAdmissible π L) :
    0 ≤ productionRate π L := by
  obtain ⟨h, hh, hdiag⟩ := exists_uniformization_step L
  have := PathReversal.RealChart.epochProduction_nonneg (uniformized_admissible hA hh hdiag)
  rw [epochProduction_uniformized π L hh.ne'] at this
  exact (mul_nonneg_iff_of_pos_left hh).mp this

/-- [proved-derived; formal-checked] **`σ_rate = 0` precisely under detailed balance**
`π_x L_xy = π_y L_yx`, from the discrete owner's `epochProduction_eq_zero_iff`. -/
theorem productionRate_eq_zero_iff {π : S → ℝ} {L : S → S → ℝ} (hA : RateAdmissible π L) :
    productionRate π L = 0 ↔ RateDetailedBalance π L := by
  obtain ⟨h, hh, hdiag⟩ := exists_uniformization_step L
  have hz := PathReversal.RealChart.epochProduction_eq_zero_iff
    (uniformized_admissible hA hh hdiag)
  rw [epochProduction_uniformized π L hh.ne', mul_eq_zero, or_iff_right hh.ne',
    detailedBalance_uniformized_iff π L hh.ne'] at hz
  exact hz

omit [DecidableEq S] in
/-- [proved-derived; formal-checked] Rows of `L` summing to `0` make `P_h` stochastic. -/
theorem uniformized_rows [DecidableEq S] {L : S → S → ℝ} (hrow : ∀ x, ∑ y, L x y = 0) (h : ℝ) :
    ∀ x, ∑ y, uniformized L h x y = 1 := by
  intro x
  simp [uniformized, sum_add_distrib, ← mul_sum, hrow]

/-- [proved-derived; formal-checked] A law with `π L = 0` is stationary for `P_h`. -/
theorem uniformized_stationary {π : S → ℝ} {L : S → S → ℝ} (hstat : ∀ y, ∑ x, π x * L x y = 0)
    (h : ℝ) : Kac.Stationary (uniformized L h) π := by
  intro y
  have hs : ∑ x, π x * (h * L x y) = h * ∑ x, π x * L x y := by
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  simp only [uniformized, mul_add, sum_add_distrib, hs, hstat, mul_zero, add_zero, mul_ite,
    mul_one, sum_ite_eq', mem_univ, if_true]

/-- [proved-derived; formal-checked] **Production of a continuous-time aeon**: for a conservative
generator with a stationary law, an aeon of `n` epochs of the uniformized chain at step `h`
produces `n h σ_rate`, elapsed time times the rate. -/
theorem production_uniformized {π : S → ℝ} {L : S → S → ℝ} (hA : RateAdmissible π L) {h : ℝ}
    (hh : 0 < h) (hdiag : ∀ x, h * |L x x| ≤ 1) (hrow : ∀ x, ∑ y, L x y = 0)
    (hstat : ∀ y, ∑ x, π x * L x y = 0) (n : ℕ) :
    PathReversal.RealChart.production π (uniformized L h) n = n * h * productionRate π L := by
  rw [PathReversal.RealChart.production_eq_mul (uniformized_admissible hA hh hdiag)
    (uniformized_stationary hstat h) (uniformized_rows hrow h), epochProduction_uniformized π L hh.ne']
  ring

end Rate

/-! ## 4. Production dominates a quadratic dissipation -/

section Onsager

/-- [proved-standard; formal-checked] **The logarithmic mean is at most the arithmetic mean**, in
production form: `(a − b) log(a/b) ≥ 2(a − b)²/(a + b)` for `a, b > 0`. -/
theorem onsager_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * (a - b) ^ 2 / (a + b) ≤ (a - b) * Real.log (a / b) := by
  have hab : 0 < a + b := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = (a - b) / (a + b) := ⟨_, rfl⟩
  have hxab : a - b = x * (a + b) := by rw [hx, div_mul_cancel₀ _ hab.ne']
  have hx1 : |x| < 1 := by
    rw [hx, abs_div, abs_of_pos hab, div_lt_one hab, abs_sub_lt_iff]
    constructor <;> linarith
  have h1 : 0 < 1 + x := by linarith [neg_abs_le x]
  have h2 : 0 < 1 - x := by linarith [le_abs_self x]
  have hratio : a / b = (1 + x) / (1 - x) := by
    rw [div_eq_div_iff hb.ne' h2.ne']
    linear_combination hxab
  have hlog : Real.log (a / b) = Real.log (1 + x) - Real.log (1 - x) := by
    rw [hratio, Real.log_div h1.ne' h2.ne']
  have hs := (Real.hasSum_log_sub_log_of_abs_lt_one hx1).mul_left ((a + b) * x)
  have hfirst := le_hasSum hs 0 fun j _ => by
    show 0 ≤ (a + b) * x * (2 * (1 / (2 * (j : ℝ) + 1)) * x ^ (2 * j + 1))
    have hre : (a + b) * x * (2 * (1 / (2 * (j : ℝ) + 1)) * x ^ (2 * j + 1)) =
        (a + b) * (2 * (1 / (2 * (j : ℝ) + 1))) * (x ^ (j + 1)) ^ 2 := by ring
    rw [hre]
    positivity
  calc 2 * (a - b) ^ 2 / (a + b)
      = (a + b) * x * (2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * x ^ (2 * 0 + 1)) := by
        rw [hxab]
        field_simp
        ring
    _ ≤ (a + b) * x * (Real.log (1 + x) - Real.log (1 - x)) := hfirst
    _ = (a - b) * Real.log (a / b) := by rw [hlog, hxab]; ring

/-- [proved-standard; formal-checked] Equality at `a = b`: both sides are `0`. -/
theorem onsager_eq_of_eq (a : ℝ) : 2 * (a - a) ^ 2 / (a + a) = (a - a) * Real.log (a / a) := by
  simp

/-- [proved-standard; formal-checked] `log(b/a) = −log(a/b)`. -/
theorem log_div_swap (a b : ℝ) : Real.log (b / a) = -Real.log (a / b) := by
  rw [← Real.log_inv, inv_div]

/-- [proved-standard; formal-checked] In the port-Hamiltonian chart the dissipation of a current
`j` through the coefficient `R ≠ 0` is the production `⟨e, R e⟩` of the effort `e = R⁻¹ j`. -/
theorem dissipation_effort_form {j R : ℝ} (hR : R ≠ 0) : j ^ 2 / R = (j / R) * (R * (j / R)) := by
  field_simp

variable {S : Type*} [Fintype S]

/-- [proved-derived; formal-checked] **A flow production is half its antisymmetrized form**:
`Σ J_xy log(J_xy/J_yx) = ½ Σ (J_xy − J_yx) log(J_xy/J_yx)`, for any real flows. -/
theorem sum_mul_log_eq_half (J : S → S → ℝ) :
    ∑ x, ∑ y, J x y * Real.log (J x y / J y x) =
      (1 / 2) * ∑ x, ∑ y, (J x y - J y x) * Real.log (J x y / J y x) := by
  have hswap : ∑ x, ∑ y, J y x * Real.log (J x y / J y x) =
      -∑ x, ∑ y, J x y * Real.log (J x y / J y x) := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [log_div_swap]
    ring
  have hsplit : ∑ x, ∑ y, (J x y - J y x) * Real.log (J x y / J y x) =
      ∑ x, ∑ y, J x y * Real.log (J x y / J y x) -
        ∑ x, ∑ y, J y x * Real.log (J x y / J y x) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun y _ => by ring
  rw [hsplit, hswap]
  ring

/-- [proved-standard; formal-checked] A symmetric sum with zero diagonal is twice its strict upper
half. -/
theorem sum_sum_eq_two_mul_lt [LinearOrder S] (g : S → S → ℝ) (hg : ∀ x y, g x y = g y x)
    (hd : ∀ x, g x x = 0) : ∑ x, ∑ y, g x y = 2 * ∑ x, ∑ y, if x < y then g x y else 0 := by
  have hsplit : ∀ x y, g x y = (if x < y then g x y else 0) + (if y < x then g y x else 0) := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · simp [hxy, not_lt.mpr hxy.le]
    · subst hxy; simp [hd]
    · simp [hxy, not_lt.mpr hxy.le, hg x y]
  have hswap : ∑ x, ∑ y, (if y < x then g y x else 0) =
      ∑ x, ∑ y, (if x < y then g x y else 0) := sum_comm
  calc ∑ x, ∑ y, g x y
      = ∑ x, ∑ y, ((if x < y then g x y else 0) + (if y < x then g y x else 0)) :=
        sum_congr rfl fun x _ => sum_congr rfl fun y _ => hsplit x y
    _ = 2 * ∑ x, ∑ y, if x < y then g x y else 0 := by
        simp only [sum_add_distrib]
        rw [hswap]
        ring

/-- [definition] The net current of an edge, `j_xy = J_xy − J_yx`. -/
def netCurrent (J : S → S → ℝ) (x y : S) : ℝ := J x y - J y x

/-- [definition] The edge's coefficient `R_xy = (J_xy + J_yx)/2`, its mean traffic: the entry of the
dissipation form in the port-Hamiltonian chart. -/
def onsagerCoefficient (J : S → S → ℝ) (x y : S) : ℝ := (J x y + J y x) / 2

/-- [definition] **The quadratic dissipation** `Σ_(x<y) j_xy² / R_xy` of the net currents through
the edge coefficients. -/
def quadraticDissipation [LinearOrder S] (J : S → S → ℝ) : ℝ :=
  ∑ x, ∑ y, if x < y then netCurrent J x y ^ 2 / onsagerCoefficient J x y else 0

/-- [proved-derived; formal-checked] `Σ_(x<y) j²/R = Σ_(x<y) 2(J_xy − J_yx)²/(J_xy + J_yx)`. -/
theorem quadraticDissipation_eq [LinearOrder S] (J : S → S → ℝ) :
    quadraticDissipation J =
      ∑ x, ∑ y, if x < y then 2 * (J x y - J y x) ^ 2 / (J x y + J y x) else 0 := by
  unfold quadraticDissipation netCurrent onsagerCoefficient
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  split_ifs
  · rw [div_div_eq_mul_div]; ring
  · rfl

/-- [proved-derived; formal-checked] **Flow production dominates the quadratic dissipation**, for
nonnegative flows with symmetric support. -/
theorem sum_mul_log_ge_quadraticDissipation [LinearOrder S] {J : S → S → ℝ}
    (hnn : ∀ x y, 0 ≤ J x y) (hsupp : ∀ x y, 0 < J x y → 0 < J y x) :
    quadraticDissipation J ≤ ∑ x, ∑ y, J x y * Real.log (J x y / J y x) := by
  have hg : ∀ x y, (J x y - J y x) * Real.log (J x y / J y x) =
      (J y x - J x y) * Real.log (J y x / J x y) := by
    intro x y; rw [log_div_swap (J x y) (J y x)]; ring
  rw [sum_mul_log_eq_half, sum_sum_eq_two_mul_lt _ hg (fun x => by simp), quadraticDissipation_eq]
  rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  split_ifs
  · rcases (hnn x y).eq_or_lt with h0 | hpos
    · have h0' : J y x = 0 := by
        by_contra hne
        exact (hsupp y x (lt_of_le_of_ne (hnn y x) (Ne.symm hne))).ne' h0.symm
      rw [← h0, h0']; simp
    · exact onsager_le hpos (hsupp x y hpos)
  · exact le_rfl

/-- [proved-derived; formal-checked] **The Markov production dominates the dissipation of its net
currents**: `epochProduction ≥ Σ_(x<y) 2(J_xy − J_yx)²/(J_xy + J_yx)` for an admissible chain. -/
theorem epochProduction_ge_quadraticDissipation [LinearOrder S] {π : S → ℝ} {P : S → S → ℝ}
    (hA : PathReversal.Admissible π P) :
    quadraticDissipation (PathReversal.flow π P) ≤ PathReversal.RealChart.epochProduction π P :=
  sum_mul_log_ge_quadraticDissipation (PathReversal.flow_nonneg hA)
    (fun _ _ hp => PathReversal.flow_support hA hp)

end Onsager

/-! ## 5. Witnesses -/

namespace Rotation

/-- [definition] The biased rotation's generator: `2/3` forward, `1/3` back, `−1` on the
diagonal. -/
def generator : Fin 3 → Fin 3 → ℝ :=
  fun x y => !![-1, 2 / 3, 1 / 3; 1 / 3, -1, 2 / 3; 2 / 3, 1 / 3, -1] x y

/-- [definition] The uniform law. -/
def law : Fin 3 → ℝ := fun _ => 1 / 3

/-- [counterexample; formal-checked] The rotation's generator is admissible at the uniform law. -/
theorem admissible : RateAdmissible law generator where
  pos := fun _ => by norm_num [law]
  offDiag_nonneg := fun x y hxy => by
    fin_cases x <;> fin_cases y <;> simp_all [generator] <;> norm_num
  support := fun x y hxy _ => by
    fin_cases x <;> fin_cases y <;> simp_all [generator]

/-- [counterexample; formal-checked] Its rows sum to `0`: it is conservative. -/
theorem rows : ∀ x, ∑ y, generator x y = 0 := by
  intro x; fin_cases x <;> simp [generator, Fin.sum_univ_three] <;> norm_num

/-- [counterexample; formal-checked] The uniform law is stationary: `π L = 0`. -/
theorem stationary : ∀ y, ∑ x, law x * generator x y = 0 := by
  intro y; fin_cases y <;> simp [law, generator, Fin.sum_univ_three] <;> norm_num

/-- [counterexample; formal-checked] The step `h = 1` uniformizes it: `|L_xx| ≤ 1`. -/
theorem diag : ∀ x, (1 : ℝ) * |generator x x| ≤ 1 := by
  intro x; fin_cases x <;> simp [generator]

/-- [counterexample; formal-checked] Its uniformization at `h = 1` is `PathReversal.Rotation.P`. -/
theorem uniformized_one : uniformized generator 1 = PathReversal.chainR PathReversal.Rotation.P := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [uniformized, generator, PathReversal.chainR, PathReversal.Rotation.P]

/-- [counterexample; formal-checked] The uniform law is `PathReversal.Rotation.π` read in `ℝ`. -/
theorem law_eq : law = PathReversal.lawR PathReversal.Rotation.π := by
  funext x; simp [law, PathReversal.lawR, PathReversal.Rotation.π]

/-- [counterexample; formal-checked] **The biased rotation produces `(1/3) log 2` per unit time.**
Its generator's uniformization at `h = 1` is `PathReversal.Rotation.P`, so
`σ_rate = (1/3) log 2 > 0` (`PathReversal.Rotation.rotation_production_pos`), and the generator is
not in detailed balance. -/
theorem rotation_productionRate :
    productionRate law generator = Real.log 2 / 3 ∧ 0 < productionRate law generator ∧
      ¬ RateDetailedBalance law generator := by
  have h2 : PathReversal.RealChart.epochProduction law (uniformized generator 1) =
      Real.log 2 / 3 := by
    rw [uniformized_one, law_eq, ← PathReversal.epochProduction_eq_real]
    exact PathReversal.Rotation.rotation_production_pos.1
  have hσ : productionRate law generator = Real.log 2 / 3 := by
    rw [← h2, epochProduction_uniformized law generator one_ne_zero, one_mul]
  have hpos : 0 < productionRate law generator := by
    rw [hσ]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨hσ, hpos, fun hdb => ?_⟩
  rw [(productionRate_eq_zero_iff admissible).mpr hdb] at hpos
  exact lt_irrefl 0 hpos

end Rotation

section OneResistor

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {σ μ : Type*} [Fintype σ] [Fintype μ] [DecidableEq σ]

/-- [counterexample; formal-checked] **A resistor's aeon produces its lost storage.** A midpoint
aeon with `Q = 1`, `J = 0`, `R = r · 1` (`r > 0`), `h > 0`, no supply and a nonzero start produces
`(H(q_0) − H(q_n))/T > 0` over `n ≥ 1` steps. -/
theorem oneResistor_production_pos {r h T : 𝕜} (hr : 0 < r) (hh : 0 < h) (hT : 0 < T)
    {B : Matrix σ μ 𝕜} {q : ℕ → σ → 𝕜} {n : ℕ}
    (ha : IsMidpointAeon 1 0 (r • 1) B h q (fun _ => 0) n) (hq : q 0 ≠ 0) (hn : 0 < n) :
    production 1 (r • 1) h T q n = (storageEnergy 1 (q 0) - storageEnergy 1 (q n)) / T ∧
      0 < production 1 (r • 1) h T q n := by
  have hJ : (0 : Matrix σ σ 𝕜)ᵀ = -0 := by simp
  have hRs : (r • (1 : Matrix σ σ 𝕜))ᵀ = r • 1 := by rw [transpose_smul, transpose_one]
  have hR : ∀ e : σ → 𝕜, 0 ≤ e ⬝ᵥ ((r • (1 : Matrix σ σ 𝕜)) *ᵥ e) := by
    intro e
    rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hr.le (by simp only [dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _)
  have hW : suppliedWork 1 B h q (fun _ => 0) n = 0 := by simp [suppliedWork]
  have hfl := first_law transpose_one hJ hT.ne' ha
  rw [hW] at hfl
  refine ⟨by rw [eq_div_iff hT.ne']; linear_combination hfl, ?_⟩
  refine lt_of_le_of_ne (production_nonneg hh.le hT hR n) (fun h0 => hq ?_)
  have he0 := (production_eq_zero_iff_of_symm hh hT hRs hR n).mp h0.symm 0 hn
  rw [smul_mulVec, one_mulVec, smul_eq_zero, or_iff_right hr.ne'] at he0
  have hstep := ha 0 hn
  rw [he0, mulVec_zero, mulVec_zero, add_zero, smul_zero, sub_eq_zero] at hstep
  simp only [effort, one_mulVec, hstep] at he0
  rw [← two_smul 𝕜 (q 0), smul_smul] at he0
  norm_num at he0
  exact he0

/-- [definition] The aeon `q_k = 3^(−k)` of one storage coordinate. -/
def thirdAeon : ℕ → Fin 1 → ℚ := fun k => ![(1 / 3 : ℚ) ^ k]

/-- [counterexample; formal-checked] `q_k = 3^(−k)` is a midpoint aeon of the unit resistor at
`h = 1`, for every length. -/
theorem thirdAeon_isMidpointAeon (n : ℕ) :
    IsMidpointAeon (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 ((1 : ℚ) • 1) (0 : Matrix (Fin 1) (Fin 1) ℚ) 1
      thirdAeon (fun _ => 0) n := by
  intro k _
  funext i
  fin_cases i
  simp [thirdAeon, effort, pow_succ, neg_mulVec]
  ring

/-- [counterexample; formal-checked] The aeon `q_k = 3^(−k)` produces `(1 − 9^(−n))/(2T) > 0`
over `n ≥ 1` steps. -/
theorem thirdAeon_production {T : ℚ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    production 1 ((1 : ℚ) • 1) 1 T thirdAeon n = (1 - (1 / 9 : ℚ) ^ n) / (2 * T) ∧
      0 < production 1 ((1 : ℚ) • 1) 1 T thirdAeon n := by
  have hq : thirdAeon 0 ≠ 0 := by
    intro h; have := congrFun h 0; simp [thirdAeon] at this
  obtain ⟨hval, hpos⟩ := oneResistor_production_pos (B := (0 : Matrix (Fin 1) (Fin 1) ℚ))
    one_pos one_pos hT (thirdAeon_isMidpointAeon n) hq hn
  refine ⟨?_, hpos⟩
  have hE : ∀ k, storageEnergy (1 : Matrix (Fin 1) (Fin 1) ℚ) (thirdAeon k) = (1 / 9) ^ k / 2 := by
    intro k
    have h9 : ((1 / 3 : ℚ) ^ k) * (1 / 3) ^ k = (1 / 9) ^ k := by rw [← mul_pow]; norm_num
    simp only [storageEnergy, one_mulVec, thirdAeon, dotProduct, Fin.sum_univ_one,
      Matrix.cons_val_zero, h9]
    ring
  rw [hval, hE, hE, pow_zero]
  field_simp

end OneResistor

end Holonics.Aeon.Production.PortHamiltonian
