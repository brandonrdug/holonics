import Holonics.Compression.Landmark.SiteKind
import HolonicsResearch.Geometry.CellPassBand
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A pumped carry step `z ↦ αz + βz̄` turns where `|β|² < (Im α)²` and locks above it

The carry along the strand composes the scalar move `z ↦ γz + κb` on one circle's charge
(`Holonics/HNN/CarryGate.lean`, atlas `contact.carried-product`; the engine's owner
`crates/engine/src/carry.rs`, `carry_gate`: `γ = γ̂(q)/(1 + d)`). The pumped step proposed for the
carry circles adds the conjugate term: `z ↦ αz + βz̄`, a real-linear map of the plane whose `2 × 2`
real matrix is `mat α β`. The built carry is `β = 0`. Its site kind (`SiteKind.siteKind` on the
trace and determinant faces) is read from `|α|²`, `|β|²` and `(Im α)²` alone, with no square root,
and the band of a turning step is the cell's band of `Geometry/CellPassBand.lean` at the ratio of
the step's two singular values.

Sources. Atlas rows `rh.frobenius-cell-junction-delay` (`docs/atlas/targets.tsv`),
`wave.junction-boost-delay-turn` (`docs/atlas/physics.tsv`) and `contact.pass-reach-gap`; record
`research/records/2026-11-13_THE_TICK_HOLDS_THE_JUNCTIONS_ANCHOR_*.md` §6 item 4.

[proved-derived; formal-checked] What is proved.

1. **The steps compose as a pair** (`step_zero_right`, `step_comp`): the built carry is
   `step α 0`, and `step α β ∘ step α' β' = step (αα' + ββ̄') (αβ' + βᾱ')`. The gauge
   `|α|² − |β|²` is multiplicative under that composition (`gauge_comp`). Scalar steps commute
   (`scalars_commute`); a turn and a pump do not (`pumped_do_not_commute`).
2. **The two singular values** are `‖α‖ + ‖β‖` and `|‖α‖ − ‖β‖|`: the step's gain lies between
   them (`norm_step_le`, `le_norm_step`) and each is attained on a unit charge
   (`exists_inPhase`, `exists_quadrature`, from one common axis, `exists_common_axis`).
3. **The matrix** (`mat_mulVec`, `mat_trace`, `mat_det`): `mat α β` acts on `(Re z, Im z)` as the
   step, with trace `2 Re α` and determinant `|α|² − |β|²`.
4. **The kinds at the engine's grain** (`kind_reflection_iff`, `kind_degenerate_iff`,
   `kind_rotation_iff`, `kind_null_iff`, `kind_boost_iff`): reflection `|α|² < |β|²`, degenerate
   `|α|² = |β|²`, rotation `|β|² < (Im α)²`, null `|β|² < |α|²` and `|β|² = (Im α)²`, boost
   `(Im α)² < |β|² < |α|²`. The discriminant face is `4(|β|² − (Im α)²)`.
5. **The same band as the cell's** (`edge_singular`, `rotation_iff_band`): for `‖β‖ < ‖α‖` and
   `b = (‖α‖ + ‖β‖)/(‖α‖ − ‖β‖)`, `edge b = √(|α|² − |β|²)/‖α‖`, and the step is a rotation if
   and only if `|Re α|/‖α‖ < edge b`.
6. **The two axes of a step with a real gate** (`inPhase_axis`, `quadrature_axis`): with gate
   `a` and pump `r e^{2iψ}`, the axis `e^{iψ}` is scaled by `a + r` and the axis `i e^{iψ}` by
   `a − r`.
7. **Passivity with a drive** (`charge_step_le`, `charge_le`): if `‖α‖ + ‖β‖ + κ/N ≤ 1`, one step
   `z ↦ step α β z + κb` keeps a charge within `M` when `N‖b‖ ≤ M`, and the charge along a strand
   stays within `N·B` for drives `‖b n‖ ≤ B`. At `β = 0` this is the pattern of
   `CarryGate.charge_step_le` and `CarryGate.charge_le`. The condition is on the sum of the
   moduli and not on the gauge: `z ↦ z + z̄` has gauge `0` and doubles a unit charge
   (`gauge_zero_step_doubles`).
8. **The simplex weights** `α = a/(a+p+d)·γ`, `β = p/(a+p+d)·ρ`, `κ = N d/(a+p+d)` with
   `|γ| = |ρ| = 1` sum to one (`simplex_weights`), so item 7 applies; the step is a rotation
   if and only if `p² < a² (Im γ)²` (`simplex_rotation_iff`); and at the founded turn (`γ = 1`)
   every pump `0 < p < a` is a boost, never a rotation (`founded_gate_locks`).

Limits. `siteKind` is a class function of the trace and the determinant; it does not say which
axis a boost's charge settles on beyond item 6's real gate, and for a general gate the two
eigen-axes are not constructed. `exists_inPhase` and `exists_quadrature` give the two singular
values on one step; the gain of a composition of steps along a strand is bounded only by item 7.
`charge_le` is a bound under the simplex condition, not a statement that the charge converges.
Nothing here models the engine's declared widths, its releases or the adjoint of a pumped step,
and no claim is made that a pumped step improves a line: that is a lap's reading.

Computational object: the helical pair interaction. Of the winding guide's six general objects
this module touches the helix (the gate's turn) and the pair (the step and its conjugate); faces
and placement, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the pumped carry step proposed for the engine's carry circles (the lock test
`(Im α)² < |β|²` is a comparison at the engine's own grain), and
`HolonicsResearch/Geometry/CellPassBand.lean` as the band it shares.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.PumpedCarry

open Complex ComplexConjugate
open Holonics.Compression.Landmark.SiteKind
open Holonics.Geometry.CellPassBand (edge pass edge_pos edge_sq)

/-! ## 1. The step and its composition -/

/-- [definition] The pumped carry step on one circle's charge: `z ↦ αz + βz̄`. -/
def step (α β z : ℂ) : ℂ := α * z + β * conj z

/-- [proved-derived; formal-checked] The built carry is the step without a pump. -/
theorem step_zero_right (α z : ℂ) : step α 0 z = α * z := by
  simp [step]

/-- [proved-derived; formal-checked] **Two steps compose into a step:**
`step α β ∘ step α' β' = step (αα' + ββ̄') (αβ' + βᾱ')`. -/
theorem step_comp (α β α' β' z : ℂ) :
    step α β (step α' β' z) = step (α * α' + β * conj β') (α * β' + β * conj α') z := by
  simp only [step, map_add, map_mul, Complex.conj_conj]
  ring

/-- [definition] The gauge of a step, `|α|² − |β|²`: the determinant of its matrix. -/
def gauge (α β : ℂ) : ℝ := Complex.normSq α - Complex.normSq β

/-- [proved-derived; formal-checked] **The gauge is multiplicative under composition.** -/
theorem gauge_comp (α β α' β' : ℂ) :
    gauge (α * α' + β * conj β') (α * β' + β * conj α') = gauge α β * gauge α' β' := by
  simp only [gauge, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- [proved-derived; formal-checked] Scalar steps (the built carry's) commute. -/
theorem scalars_commute (α α' z : ℂ) : step α 0 (step α' 0 z) = step α' 0 (step α 0 z) := by
  simp only [step_zero_right]
  ring

/-- [counterexample; formal-checked] **A turn and a pump do not commute:** the quarter turn after
the unit pump sends `1` to `i`, and the pump after the quarter turn sends it to `−i`. -/
theorem pumped_do_not_commute : step Complex.I 0 (step 0 1 1) ≠ step 0 1 (step Complex.I 0 1) := by
  intro h
  have h2 := congrArg Complex.im h
  norm_num [step] at h2

/-! ## 2. The two singular values -/

/-- [proved-derived; formal-checked] **The step's gain is at most `‖α‖ + ‖β‖`.** -/
theorem norm_step_le (α β z : ℂ) : ‖step α β z‖ ≤ (‖α‖ + ‖β‖) * ‖z‖ := by
  calc ‖step α β z‖ ≤ ‖α * z‖ + ‖β * conj z‖ := norm_add_le _ _
    _ = (‖α‖ + ‖β‖) * ‖z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      ring

/-- [proved-derived; formal-checked] **The step's gain is at least `|‖α‖ − ‖β‖|`.** -/
theorem le_norm_step (α β z : ℂ) : |‖α‖ - ‖β‖| * ‖z‖ ≤ ‖step α β z‖ := by
  have h := abs_norm_sub_norm_le (α * z) (-(β * conj z))
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj, sub_neg_eq_add, ← sub_mul, abs_mul,
    abs_norm] at h
  exact h

/-- [proved-derived; formal-checked] **One axis carries both terms:** there are unit `z` and `u`
with `αz = ‖α‖u` and `βz̄ = ‖β‖u`; `z = e^{i(arg β − arg α)/2}`, `u = e^{i(arg α + arg β)/2}`. -/
theorem exists_common_axis (α β : ℂ) :
    ∃ z u : ℂ, ‖z‖ = 1 ∧ ‖u‖ = 1 ∧ α * z = ‖α‖ * u ∧ β * conj z = ‖β‖ * u := by
  refine ⟨exp (((arg β - arg α) / 2 : ℝ) * I), exp (((arg α + arg β) / 2 : ℝ) * I),
    norm_exp_ofReal_mul_I _, norm_exp_ofReal_mul_I _, ?_, ?_⟩
  · have hα := norm_mul_exp_arg_mul_I α
    calc α * exp (((arg β - arg α) / 2 : ℝ) * I)
        = ‖α‖ * (exp (arg α * I) * exp (((arg β - arg α) / 2 : ℝ) * I)) := by
          rw [← mul_assoc, hα]
      _ = ‖α‖ * exp (((arg α + arg β) / 2 : ℝ) * I) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring
  · have hβ := norm_mul_exp_arg_mul_I β
    have hc : conj (exp (((arg β - arg α) / 2 : ℝ) * I)) =
        exp (-(((arg β - arg α) / 2 : ℝ) * I)) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    rw [hc]
    calc β * exp (-(((arg β - arg α) / 2 : ℝ) * I))
        = ‖β‖ * (exp (arg β * I) * exp (-(((arg β - arg α) / 2 : ℝ) * I))) := by
          rw [← mul_assoc, hβ]
      _ = ‖β‖ * exp (((arg α + arg β) / 2 : ℝ) * I) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring

/-- [proved-derived; formal-checked] **The in-phase axis attains the larger singular value:** a
unit charge whose step has norm `‖α‖ + ‖β‖`. -/
theorem exists_inPhase (α β : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ ‖step α β z‖ = ‖α‖ + ‖β‖ := by
  obtain ⟨z, u, hz, hu, h1, h2⟩ := exists_common_axis α β
  refine ⟨z, hz, ?_⟩
  rw [step, h1, h2, ← add_mul, norm_mul, hu, mul_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg α) (norm_nonneg β))]

/-- [proved-derived; formal-checked] **The quadrature axis attains the smaller singular value:** a
unit charge whose step has norm `|‖α‖ − ‖β‖|`. -/
theorem exists_quadrature (α β : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ ‖step α β z‖ = |‖α‖ - ‖β‖| := by
  obtain ⟨z, u, hz, hu, h1, h2⟩ := exists_common_axis α β
  refine ⟨I * z, by rw [norm_mul, Complex.norm_I, one_mul, hz], ?_⟩
  have e : step α β (I * z) = ((‖α‖ - ‖β‖ : ℝ) : ℂ) * (I * u) := by
    rw [step, map_mul, Complex.conj_I]
    push_cast
    linear_combination I * h1 - I * h2
  rw [e, norm_mul, norm_mul, Complex.norm_I, hu, one_mul, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-! ## 3. The step's matrix -/

/-- [definition] The step as a real `2 × 2` matrix on `(Re z, Im z)`. -/
def mat (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![α.re + β.re, β.im - α.im; α.im + β.im, α.re - β.re]

/-- [proved-derived; formal-checked] The matrix acts on `(Re z, Im z)` as the step acts on `z`. -/
theorem mat_mulVec (α β z : ℂ) :
    Matrix.mulVec (mat α β) ![z.re, z.im] = ![(step α β z).re, (step α β z).im] := by
  ext i
  fin_cases i <;> simp [mat, step, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- [proved-derived; formal-checked] The matrix's trace is `2 Re α`: the pump carries none. -/
theorem mat_trace (α β : ℂ) : (mat α β).trace = 2 * α.re := by
  rw [mat, Matrix.trace_fin_two_of]
  ring

/-- [proved-derived; formal-checked] The matrix's determinant is the gauge `|α|² − |β|²`. -/
theorem mat_det (α β : ℂ) : (mat α β).det = Complex.normSq α - Complex.normSq β := by
  rw [mat, Matrix.det_fin_two_of, Complex.normSq_apply, Complex.normSq_apply]
  ring

/-! ## 4. The kinds of a pumped step, read without a square root -/

/-- [proved-derived; formal-checked] **Reflection ⇔ the pump exceeds the gate:** `|α|² < |β|²`. -/
theorem kind_reflection_iff (α β : ℂ) :
    siteKind (mat α β).trace (mat α β).det = Kind.reflection ↔ normSq α < normSq β := by
  rw [siteKind_eq_reflection_iff, mat_det, sub_neg]

/-- [proved-derived; formal-checked] **Degenerate ⇔ the pump equals the gate:** `|α|² = |β|²`. -/
theorem kind_degenerate_iff (α β : ℂ) :
    siteKind (mat α β).trace (mat α β).det = Kind.degenerate ↔ normSq α = normSq β := by
  rw [siteKind_eq_degenerate_iff, mat_det, sub_eq_zero]

/-- [proved-derived; formal-checked] **Rotation ⇔ the pump is below the gate's turning part:**
`|β|² < (Im α)²`. -/
theorem kind_rotation_iff (α β : ℂ) :
    siteKind (mat α β).trace (mat α β).det = Kind.rotation ↔ normSq β < α.im ^ 2 := by
  rw [siteKind_eq_rotation_iff, mat_trace, mat_det, Complex.normSq_apply α]
  constructor <;> intro h <;> nlinarith

/-- [proved-derived; formal-checked] **Null ⇔ the pump equals the gate's turning part** below the
gate: `|β|² < |α|²` and `|β|² = (Im α)²`. -/
theorem kind_null_iff (α β : ℂ) :
    siteKind (mat α β).trace (mat α β).det = Kind.null ↔
      normSq β < normSq α ∧ normSq β = α.im ^ 2 := by
  have e : (2 * α.re) ^ 2 = 4 * (normSq α - normSq β) ↔ normSq β = α.im ^ 2 := by
    rw [Complex.normSq_apply α]
    constructor <;> intro h <;> nlinarith
  rw [siteKind_eq_null_iff, mat_trace, mat_det, sub_pos, e]

/-- [proved-derived; formal-checked] **Boost (the lock) ⇔ the pump lies between the gate's turning
part and the gate:** `(Im α)² < |β|² < |α|²`. -/
theorem kind_boost_iff (α β : ℂ) :
    siteKind (mat α β).trace (mat α β).det = Kind.boost ↔
      α.im ^ 2 < normSq β ∧ normSq β < normSq α := by
  have e : 4 * (normSq α - normSq β) < (2 * α.re) ^ 2 ↔ α.im ^ 2 < normSq β := by
    rw [Complex.normSq_apply α]
    constructor <;> intro h <;> nlinarith
  rw [siteKind_eq_boost_iff, mat_trace, mat_det, sub_pos, e, and_comm]

/-! ## 5. The same band as the cell's -/

/-- [proved-derived; formal-checked] **The cell's edge at the ratio of the two singular values:**
for `‖β‖ < ‖α‖`, `edge ((‖α‖ + ‖β‖)/(‖α‖ − ‖β‖)) = √(|α|² − |β|²)/‖α‖`. -/
theorem edge_singular {α β : ℂ} (h : ‖β‖ < ‖α‖) :
    edge ((‖α‖ + ‖β‖) / (‖α‖ - ‖β‖)) = Real.sqrt (normSq α - normSq β) / ‖α‖ := by
  have hB : 0 ≤ ‖β‖ := norm_nonneg β
  have hA : 0 < ‖α‖ := lt_of_le_of_lt hB h
  have hd : 0 < ‖α‖ - ‖β‖ := sub_pos.mpr h
  have hA' : ‖α‖ ≠ 0 := hA.ne'
  have hd' : ‖α‖ - ‖β‖ ≠ 0 := hd.ne'
  have hb : 0 < (‖α‖ + ‖β‖) / (‖α‖ - ‖β‖) := div_pos (add_pos_of_pos_of_nonneg hA hB) hd
  have hpos : 0 ≤ normSq α - normSq β := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith
  have h3 : (‖α‖ + ‖β‖) / (‖α‖ - ‖β‖) + 1 ≠ 0 := (add_pos hb one_pos).ne'
  apply (sq_eq_sq₀ (edge_pos hb).le (by positivity)).mp
  rw [edge_sq hb, pass, div_pow, Real.sq_sqrt hpos, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  field_simp
  ring

/-- [proved-derived; formal-checked] **A pumped step below its gate is a rotation if and only if
it is inside the cell's band:** `|Re α|/‖α‖ < edge b` at `b = (‖α‖ + ‖β‖)/(‖α‖ − ‖β‖)`. -/
theorem rotation_iff_band {α β : ℂ} (h : ‖β‖ < ‖α‖) :
    siteKind (mat α β).trace (mat α β).det = Kind.rotation ↔
      |α.re| / ‖α‖ < edge ((‖α‖ + ‖β‖) / (‖α‖ - ‖β‖)) := by
  have hA : 0 < ‖α‖ := lt_of_le_of_lt (norm_nonneg β) h
  rw [kind_rotation_iff, edge_singular h, div_lt_div_iff_of_pos_right hA,
    Real.lt_sqrt (abs_nonneg _), sq_abs, Complex.normSq_apply α]
  constructor <;> intro h' <;> nlinarith

/-! ## 6. The two axes of a step with a real gate -/

/-- [proved-derived; formal-checked] **The in-phase axis:** with a real gate `a` and pump
`r e^{2iψ}`, the axis `e^{iψ}` is scaled by `a + r`. -/
theorem inPhase_axis (a r t ψ : ℝ) :
    step a (r * exp (2 * ψ * I)) (t * exp (ψ * I)) = (a + r) * (t * exp (ψ * I)) := by
  have hE : exp (ψ * I) * exp (-(ψ * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : exp (2 * ψ * I) = exp (ψ * I) * exp (ψ * I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hc : conj (exp ((ψ : ℂ) * I)) = exp (-(ψ * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [step, map_mul, Complex.conj_ofReal, hc, h2]
  linear_combination ((r : ℂ) * t * exp (ψ * I)) * hE

/-- [proved-derived; formal-checked] **The quadrature axis:** with a real gate `a` and pump
`r e^{2iψ}`, the axis `i e^{iψ}` is scaled by `a − r`. -/
theorem quadrature_axis (a r t ψ : ℝ) :
    step a (r * exp (2 * ψ * I)) (I * t * exp (ψ * I)) = (a - r) * (I * t * exp (ψ * I)) := by
  have hE : exp (ψ * I) * exp (-(ψ * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : exp (2 * ψ * I) = exp (ψ * I) * exp (ψ * I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hc : conj (exp ((ψ : ℂ) * I)) = exp (-(ψ * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [step, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, hc, h2]
  linear_combination (-((r : ℂ) * I * t * exp (ψ * I))) * hE

/-! ## 7. Passivity with a drive -/

/-- [proved-derived; formal-checked] **One driven step keeps the charge within the level:** if
`‖α‖ + ‖β‖ + κ/N ≤ 1`, `‖z‖ ≤ M` and `N‖b‖ ≤ M`, then `‖step α β z + κb‖ ≤ M`. At `β = 0` this is
the pattern of `CarryGate.charge_step_le`. -/
theorem charge_step_le (α β : ℂ) (κ N M : ℝ) (z b : ℂ) (hκ : 0 ≤ κ) (hN : 0 < N)
    (hsum : ‖α‖ + ‖β‖ + κ / N ≤ 1) (hz : ‖z‖ ≤ M) (hb : N * ‖b‖ ≤ M) :
    ‖step α β z + (κ : ℂ) * b‖ ≤ M := by
  have hM : 0 ≤ M := le_trans (mul_nonneg hN.le (norm_nonneg b)) hb
  have hs : 0 ≤ ‖α‖ + ‖β‖ := add_nonneg (norm_nonneg α) (norm_nonneg β)
  have hk : ‖(κ : ℂ) * b‖ = κ / N * (N * ‖b‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ, ← mul_assoc,
      div_mul_cancel₀ _ hN.ne']
  have h1 : ‖step α β z‖ ≤ (‖α‖ + ‖β‖) * M :=
    (norm_step_le α β z).trans (mul_le_mul_of_nonneg_left hz hs)
  have h2 : ‖(κ : ℂ) * b‖ ≤ κ / N * M := by
    rw [hk]
    exact mul_le_mul_of_nonneg_left hb (div_nonneg hκ hN.le)
  calc ‖step α β z + (κ : ℂ) * b‖ ≤ ‖step α β z‖ + ‖(κ : ℂ) * b‖ := norm_add_le _ _
    _ ≤ (‖α‖ + ‖β‖) * M + κ / N * M := add_le_add h1 h2
    _ = (‖α‖ + ‖β‖ + κ / N) * M := by ring
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hsum hM
    _ = M := one_mul M

/-- [counterexample; formal-checked] **The gauge does not bound the gain:** the step `z ↦ z + z̄`
has gauge `0` and doubles the unit charge. Passivity is read from the sum `‖α‖ + ‖β‖` of
`charge_step_le`, which is `2` here, and not from the determinant face. -/
theorem gauge_zero_step_doubles : gauge 1 1 = 0 ∧ ‖step 1 1 1‖ = 2 := by
  have e : step 1 1 1 = ((2 : ℝ) : ℂ) := by
    norm_num [step]
  refine ⟨by simp [gauge], ?_⟩
  rw [e, Complex.norm_real]
  norm_num

/-- [definition] A circle's charge along its strand under pumped steps: `Q 0 = 0` and
`Q (n + 1) = step (α n) (β n) (Q n) + κ n · b n`. -/
def charge (α β : ℕ → ℂ) (κ : ℕ → ℝ) (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => step (α n) (β n) (charge α β κ b n) + (κ n : ℂ) * b n

/-- [proved-derived; formal-checked] **The charge stays within `N` places' drive:** with
`‖α n‖ + ‖β n‖ + κ n/N ≤ 1` at every site and every drive `‖b n‖ ≤ B`, `‖Q n‖ ≤ N·B` at every
site, whatever the turns and the pumps' phases. -/
theorem charge_le (α β : ℕ → ℂ) (κ : ℕ → ℝ) (b : ℕ → ℂ) (N B : ℝ) (hκ : ∀ n, 0 ≤ κ n)
    (hN : 0 < N) (hsum : ∀ n, ‖α n‖ + ‖β n‖ + κ n / N ≤ 1) (hb : ∀ n, ‖b n‖ ≤ B) :
    ∀ n, ‖charge α β κ b n‖ ≤ N * B := by
  have hB : 0 ≤ B := (norm_nonneg (b 0)).trans (hb 0)
  intro n
  induction n with
  | zero =>
    simp only [charge, norm_zero]
    exact mul_nonneg hN.le hB
  | succ n ih =>
    simp only [charge]
    exact charge_step_le (α n) (β n) (κ n) N (N * B) _ (b n) (hκ n) hN (hsum n) ih
      (mul_le_mul_of_nonneg_left (hb n) hN.le)

/-! ## 8. The simplex weights of the proposal -/

/-- [proved-derived; formal-checked] **The simplex weights sum to one:** with
`α = a/(a+p+d)·γ`, `β = p/(a+p+d)·ρ`, `κ = N d/(a+p+d)` and `|γ| = |ρ| = 1`,
`‖α‖ + ‖β‖ + κ/N = 1`, so `charge_step_le` and `charge_le` apply. -/
theorem simplex_weights (a p d N : ℝ) (ha : 0 < a) (hp : 0 ≤ p) (hd : 0 < d) (hN : 0 < N)
    (γ ρ : ℂ) (hγ : ‖γ‖ = 1) (hρ : ‖ρ‖ = 1) :
    ‖((a / (a + p + d) : ℝ) : ℂ) * γ‖ + ‖((p / (a + p + d) : ℝ) : ℂ) * ρ‖ +
      (N * d / (a + p + d)) / N = 1 := by
  have hS : 0 < a + p + d := add_pos (add_pos_of_pos_of_nonneg ha hp) hd
  have hS' : a + p + d ≠ 0 := hS.ne'
  have hN' : N ≠ 0 := hN.ne'
  rw [norm_mul, norm_mul, hγ, hρ, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg ha.le hS.le), Real.norm_of_nonneg (div_nonneg hp hS.le)]
  field_simp

/-- [proved-derived; formal-checked] **The simplex step turns if and only if the pump's weight
is below the gate's turning part:** `p² < a² (Im γ)²`. -/
theorem simplex_rotation_iff (a p d : ℝ) (ha : 0 < a) (hp : 0 ≤ p) (hd : 0 < d) (γ ρ : ℂ)
    (hρ : ‖ρ‖ = 1) :
    siteKind (mat (((a / (a + p + d) : ℝ) : ℂ) * γ) (((p / (a + p + d) : ℝ) : ℂ) * ρ)).trace
        (mat (((a / (a + p + d) : ℝ) : ℂ) * γ) (((p / (a + p + d) : ℝ) : ℂ) * ρ)).det =
        Kind.rotation ↔ p ^ 2 < a ^ 2 * γ.im ^ 2 := by
  have hS : 0 < a + p + d := add_pos (add_pos_of_pos_of_nonneg ha hp) hd
  have hρ2 : normSq ρ = 1 := by rw [Complex.normSq_eq_norm_sq, hρ, one_pow]
  have e1 : p / (a + p + d) * (p / (a + p + d)) = p ^ 2 / (a + p + d) ^ 2 := by
    rw [← sq, div_pow]
  have e2 : (a / (a + p + d) * γ.im) ^ 2 = a ^ 2 * γ.im ^ 2 / (a + p + d) ^ 2 := by
    rw [mul_pow, div_pow, div_mul_eq_mul_div]
  rw [kind_rotation_iff, map_mul, hρ2, mul_one, Complex.normSq_ofReal, Complex.im_ofReal_mul,
    e1, e2, div_lt_div_iff_of_pos_right (pow_pos hS 2)]

/-- [proved-derived; formal-checked] **At the founded turn every pump below the gate is a lock:**
with a real gate (`γ = 1`, the carry's founding at `q = 0`) and `0 < p < a`, the simplex step is a
boost, never a rotation. -/
theorem founded_gate_locks (a p d : ℝ) (hp : 0 < p) (hpa : p < a) (hd : 0 < d) (ρ : ℂ)
    (hρ : ‖ρ‖ = 1) :
    siteKind (mat (((a / (a + p + d) : ℝ) : ℂ) * 1) (((p / (a + p + d) : ℝ) : ℂ) * ρ)).trace
        (mat (((a / (a + p + d) : ℝ) : ℂ) * 1) (((p / (a + p + d) : ℝ) : ℂ) * ρ)).det =
        Kind.boost := by
  have ha : 0 < a := hp.trans hpa
  have hS : 0 < a + p + d := add_pos (add_pos ha hp) hd
  have hρ2 : normSq ρ = 1 := by rw [Complex.normSq_eq_norm_sq, hρ, one_pow]
  have hP : 0 < p / (a + p + d) := div_pos hp hS
  have hPA : p / (a + p + d) < a / (a + p + d) := div_lt_div_of_pos_right hpa hS
  rw [kind_boost_iff, mul_one, map_mul, hρ2, mul_one, Complex.normSq_ofReal,
    Complex.normSq_ofReal, Complex.ofReal_im]
  constructor
  · nlinarith
  · nlinarith

end Holonics.HNN.PumpedCarry
