import Holonics.Fluid.NavierStokesCurvedTransport
import Holonics.Physics.Fluid.Cells
import Holonics.Holarchy.View

/-!
# The Einstein residual, the conservation return, and the discrete Bianchi identity

[definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`; null-cone record
(2026-09-24) §2. In `G + Λg = κT` the **Einstein residual** is `𝓡 = G + Λg − κT`; the field
equation is `𝓡 = 0`. The one owner of the residual and its **conservation return**
`κ ∇·T = −∇·𝓡` over any linear divergence with the contracted Bianchi port `∇·G = 0` and metric
compatibility `∇·g = 0` is `Fluid/NavierStokesCurvedTransport` (`einsteinResidual`,
`conservation_return`, `conservation_return_eq`, `conserved_of_residual_zero`); its interface
`EinsteinFluidDynamics` has zero residual (`residual_eq_zero`) and derives `∇·T = 0` through the
return (`stressEnergy_conserved`). This module consumes that owner.

[proved-derived; formal-checked]

* **The discrete Bianchi identity is `∂∂ = 0`** (Regge; Misner–Thorne–Wheeler §15). When the
  Einstein side is the boundary of a field, the Bianchi port is not supplied but *derived*:
  - on the cubical grid chart (`Physics/Fluid/Cells`), a current with `κ j = ∂F` has `∂j = 0`
    (`grid_field_conserves`, from `Cells.boundary_boundary_apply`); the unit square's field gives a
    nonzero conserved loop current (`square_field_current`);
  - on a Holarchy's complex (`Holarchy/Join.CellComplex`), `∂₁∂₂ = 0` is the Bianchi identity of
    the discrete Einstein side `G = ∂₂F` (`discrete_bianchi`); every field equation
    `G + Λg = κj` with a metric cycle `∂₁g = 0` conserves its source (`cell_field_conserves`), an
    instance of `conservation_return`;
  - in the dual, flux, reading, a current that is `κ⁻¹` times the coboundary of a potential has zero
    flux through every block of every grain (`potential_field_block_flux_zero`, through
    `Holarchy/View.blockFlux_exact`: each shared face cancels once), and the whole's flux vanishes
    by `∂₁∂₂ = 0` alone (`potential_field_total_flux_zero`); over a partition the block fluxes sum to
    it (`Holarchy/View.sum_blockFlux`).

[counterexample; formal-checked]

* **The Bianchi port is load-bearing.** Metric compatibility and the field equation do not imply
  conservation: over `ℚ` the divergence `id` with `G = T = 1`, `g = Λ = 0`, `κ = 1` satisfies both
  and has `∇·T = 1` (`field_equation_without_bianchi`).
* **The field form is load-bearing.** A current that is not a boundary, one unit segment, is not
  conserved (`segment_current_not_conserved`).

[open] A nontrivial continuum realization (a Lorentzian metric, its connection and curvature,
and a fluid-plus-thermal constitution solving `G + Λg = κT`) is owed (#62); the flat vacuum of
`Geometry/HolonicCurvedArcEinstein` and the discrete field here do not supply it. The Regge
construction of the discrete Einstein side, that `G` is the boundary of the moment of rotation
`F` of a simplicial metric's deficit angles (Misner–Thorne–Wheeler §15.4), is owed (#62): here the
field `F` is supplied, not built from a metric.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.Einstein

open Holonics.Fluid.NavierStokesCurvedTransport

/-! ## 1. The Bianchi port is load-bearing -/

/-- [counterexample; formal-checked] **Metric compatibility and the field equation do not force
conservation.** Over `ℚ` the divergence `id` with `G = T = 1`, `g = Λ = 0`, `κ = 1` has a zero
residual and a compatible metric, yet `∇·T = 1`: without the Bianchi port the implication fails. -/
theorem field_equation_without_bianchi :
    ¬ ∀ (d : ℚ →ₗ[ℚ] ℚ) (G g T Λ κ : ℚ), κ ≠ 0 → d g = 0 →
      einsteinResidual G g T Λ κ = 0 → d T = 0 := by
  intro h
  have := h LinearMap.id 1 0 1 0 1 one_ne_zero (by simp) (by simp [einsteinResidual])
  simp at this

/-! ## 2. The discrete Bianchi identity on the grid chart -/

section Grid

open Holonics.Physics.Fluid.Cells

variable {n : ℕ}

/-- [proved-derived; formal-checked] **A field-sourced current is conserved on the grid chart**:
`κ j = ∂F` with `κ ≠ 0` forces `∂j = 0`, because `∂∂F = 0` (`boundary_boundary_apply`). -/
theorem grid_field_conserves (F j : Chain n) {κ : ℤ} (hκ : κ ≠ 0) (field : κ • j = boundary F) :
    boundary j = 0 := by
  have h : κ • boundary j = 0 := by
    rw [← map_zsmul, field, boundary_boundary_apply]
  exact (smul_eq_zero.mp h).resolve_left hκ

/-- [definition] The unit square of the plane chart as a field. -/
def unitSquare : Chain 2 := cell ((0 : Point 2), Finset.univ)

/-- [proved-derived; formal-checked] **A nontrivial conserved current**: the unit square's field
sources its boundary loop, which is nonzero (the edge `(0, {1})` enters with coefficient `−1`) and
conserved. -/
theorem square_field_current :
    (boundary unitSquare) ((0 : Point 2), {1}) = -1 ∧ boundary (boundary unitSquare) = 0 := by
  refine ⟨?_, boundary_boundary_apply _⟩
  have h01 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h10 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hs0 : sgn (Finset.univ : Finset (Fin 2)) 0 = 1 := by decide
  have hs1 : sgn (Finset.univ : Finset (Fin 2)) 1 = -1 := by decide
  have hne : ∀ i : Fin 2, ((0 : Point 2) + unit i, ({1} : Finset (Fin 2))) ≠ ((0 : Point 2), {1}) :=
    fun i h => unit_ne_zero i (by simpa using congrArg Prod.fst h)
  have h01ne : ({0} : Finset (Fin 2)) ≠ {1} := by decide
  have hne' : ∀ v : Point 2, (v, ({0} : Finset (Fin 2))) ≠ ((0 : Point 2), {1}) :=
    fun v h => h01ne (congrArg Prod.snd h)
  rw [unitSquare, boundary_cell, faces, Fin.sum_univ_two, h01, h10, hs0, hs1]
  simp only [one_smul, neg_smul, Finsupp.coe_add, Finsupp.coe_neg, Finsupp.coe_sub, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, cell, Finsupp.single_apply, if_neg (hne 0), if_neg (hne' _)]
  norm_num

/-- [counterexample; formal-checked] **A current that is not a boundary is not conserved**: one unit
segment of the line has boundary `[e₀] − [0] ≠ 0`. -/
theorem segment_current_not_conserved :
    boundary (cell ((0 : Point 1), Finset.univ)) ≠ 0 := by
  rw [boundary_cell]
  intro h
  have hv := congrArg (fun c : Chain 1 => c ((0 : Point 1), ∅)) h
  have huniv : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  have hs : sgn (Finset.univ : Finset (Fin 1)) 0 = 1 := by decide
  have hne : ((0 : Point 1) + unit 0, (∅ : Finset (Fin 1))) ≠ ((0 : Point 1), ∅) :=
    fun e => unit_ne_zero 0 (by simpa using congrArg Prod.fst e)
  simp only [faces, Fin.sum_univ_one, huniv, hs, one_smul] at hv
  simp only [cell, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, if_neg hne,
    Finsupp.coe_zero, Pi.zero_apply] at hv
  norm_num at hv

end Grid

/-! ## 3. The discrete Bianchi identity on a Holarchy's complex -/

section Holarchy

open Matrix
open Holonics.HolarchyCore

variable {𝕜 : Type*} [Field 𝕜] (K : CellComplex 𝕜)

/-- [proved-derived; formal-checked] **The discrete contracted Bianchi identity**: the boundary of
the Einstein side `G = ∂₂F` has no boundary, `∂₁∂₂F = 0` (`CellComplex.dd`). -/
theorem discrete_bianchi (F : K.C₂ → 𝕜) : Matrix.mulVecLin K.d₁ (K.d₂ *ᵥ F) = 0 := by
  simp [Matrix.mulVec_mulVec, K.dd]

/-- [proved-derived; formal-checked] **The discrete field equation conserves its source.** With
`G = ∂₂F`, a metric cycle `∂₁g = 0` and `κ ≠ 0`, the residual form of `G + Λg = κj` forces
`∂₁j = 0`: `conservation_return` with the derived Bianchi identity. -/
theorem cell_field_conserves (F : K.C₂ → 𝕜) {metric j : K.C₁ → 𝕜} (cosmological : 𝕜) {κ : 𝕜}
    (hκ : κ ≠ 0) (metricCycle : K.d₁ *ᵥ metric = 0)
    (field : K.d₂ *ᵥ F + cosmological • metric = κ • j) : K.d₁ *ᵥ j = 0 :=
  conserved_of_residual_zero (Matrix.mulVecLin K.d₁) cosmological hκ (discrete_bianchi K F)
    (by simpa [Matrix.mulVecLin_apply] using metricCycle)
    ((einsteinResidual_eq_zero_iff _ _ _ _ _).mpr field)

variable {Block : Type*}

/-- [proved-derived; formal-checked] **A potential-sourced current has no flux through any block**:
if `κ j = ∂₁ᵀΦ` with `κ ≠ 0`, then `j = ∂₁ᵀ(κ⁻¹Φ)` is exact and every block of every grain reads zero
flux: `⟨j, ∂b⟩ = ⟨κ⁻¹Φ, ∂∂b⟩ = 0` (`blockFlux_exact`). -/
theorem potential_field_block_flux_zero (Φ : K.C₀ → 𝕜) {j : K.C₁ → 𝕜} {κ : 𝕜} (hκ : κ ≠ 0)
    (field : κ • j = K.d₁ᵀ *ᵥ Φ) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) :
    blockFlux K orient g j b = 0 := by
  have hj : j = K.d₁ᵀ *ᵥ (κ⁻¹ • Φ) := by
    rw [Matrix.mulVec_smul, ← field, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  rw [hj]
  exact blockFlux_exact orient g _ b

/-- [proved-derived; formal-checked] **The whole's flux vanishes**: `⟨j, ∂₂o⟩ = ⟨κ⁻¹Φ, ∂₁∂₂o⟩ = 0`
by `∂₁∂₂ = 0` alone, for every orientation `o` of the two-cells. -/
theorem potential_field_total_flux_zero (Φ : K.C₀ → 𝕜) {j : K.C₁ → 𝕜} {κ : 𝕜} (hκ : κ ≠ 0)
    (field : κ • j = K.d₁ᵀ *ᵥ Φ) (orient : K.C₂ → 𝕜) :
    j ⬝ᵥ (K.d₂ *ᵥ orient) = 0 := by
  have hj : j = K.d₁ᵀ *ᵥ (κ⁻¹ • Φ) := by
    rw [Matrix.mulVec_smul, ← field, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  rw [hj, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, K.dd,
    Matrix.zero_mulVec, dotProduct_zero]

end Holarchy

section Audit

#print axioms field_equation_without_bianchi
#print axioms grid_field_conserves
#print axioms square_field_current
#print axioms segment_current_not_conserved
#print axioms discrete_bianchi
#print axioms cell_field_conserves
#print axioms potential_field_block_flux_zero
#print axioms potential_field_total_flux_zero

end Audit

end Holonics.Physics.Spacetime.Einstein
