import Holonics.Geometry.ExteriorBoundary
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Mul

/-!
# Holon.Port: bonds, power and the bond pairing

[definition] The port facet `Π` of the Holon (`docs/ELEMENTARY_OBJECTS.md` §"The Holon as one
object"; refinement record 2026-09-22). Over any field `𝕜` a **bond** on ports `ι` is a flow and
an effort per port, `Bond 𝕜 ι = (ι → 𝕜) × (ι → 𝕜)`; its **power** is `⟨e, f⟩`; the symmetric
**bond pairing** is `⟨⟨(f₁,e₁),(f₂,e₂)⟩⟩ = ⟨e₁,f₂⟩ + ⟨e₂,f₁⟩`.

[proved-derived; formal-checked] The pairing is symmetric, reflexive and nondegenerate
(`bondForm_symm`, `bondForm_isRefl`, `bondForm_nondegenerate`), and `⟨⟨b,b⟩⟩ = 2·power b`
(`bondForm_self`). Every functional on a coordinate space is a dot product and the Fredholm
alternative holds over any field (`dual_eq_dotProduct`, `mem_range_iff_annihilators_vanish`, the
field forms of `Transport/EditRigidity`'s rational statements).
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix LinearMap

/-! ## 1. The bond space: flows and efforts -/

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι]

/-- [definition] The **bond space** `F × F*` in coordinates: a flow and an effort per port. -/
abbrev Bond (𝕜 ι : Type*) := (ι → 𝕜) × (ι → 𝕜)

/-- [definition] The flow of a bond. -/
abbrev flow (b : Bond 𝕜 ι) : ι → 𝕜 := b.1
/-- [definition] The effort of a bond. -/
abbrev effort (b : Bond 𝕜 ι) : ι → 𝕜 := b.2

/-- [definition] The **power** `⟨e, f⟩` of a bond. -/
def power (b : Bond 𝕜 ι) : 𝕜 := b.2 ⬝ᵥ b.1

/-- [definition] The symmetric bond pairing `⟨⟨(f₁,e₁),(f₂,e₂)⟩⟩ = ⟨e₁,f₂⟩ + ⟨e₂,f₁⟩`. -/
def bondForm (𝕜 ι : Type*) [Field 𝕜] [Fintype ι] : LinearMap.BilinForm 𝕜 (Bond 𝕜 ι) :=
  LinearMap.mk₂ 𝕜 (fun b c => b.2 ⬝ᵥ c.1 + c.2 ⬝ᵥ b.1)
    (fun b b' c => by simp [add_dotProduct, dotProduct_add]; ring)
    (fun a b c => by simp [smul_dotProduct, dotProduct_smul]; ring)
    (fun b c c' => by simp [add_dotProduct, dotProduct_add]; ring)
    (fun a b c => by simp [smul_dotProduct, dotProduct_smul]; ring)

@[simp] theorem bondForm_apply (b c : Bond 𝕜 ι) :
    bondForm 𝕜 ι b c = b.2 ⬝ᵥ c.1 + c.2 ⬝ᵥ b.1 := rfl

theorem bondForm_symm (b c : Bond 𝕜 ι) : bondForm 𝕜 ι b c = bondForm 𝕜 ι c b := by
  simp; ring

theorem bondForm_isRefl : (bondForm 𝕜 ι).IsRefl := fun b c h => by rw [bondForm_symm]; exact h

theorem bondForm_self (b : Bond 𝕜 ι) : bondForm 𝕜 ι b b = 2 * power b := by
  simp [power]; ring

/-- [proved-derived; formal-checked] The bond pairing is nondegenerate. -/
theorem bondForm_separating [DecidableEq ι] (b : Bond 𝕜 ι)
    (h : ∀ c, bondForm 𝕜 ι b c = 0) : b = 0 := by
  ext i
  · have := h (0, Pi.single i 1)
    simpa [bondForm_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [bondForm_apply] using this

theorem bondForm_nondegenerate [DecidableEq ι] : (bondForm 𝕜 ι).Nondegenerate :=
  ⟨bondForm_separating, fun b h => bondForm_separating b fun c => by
    rw [bondForm_symm]; exact h c⟩


section Fredholm

variable {ν : Type*} [Fintype ν]

/-- [proved-derived; formal-checked] Every functional on a finite coordinate space is a dot
product (the field form of `EditRigidity.dual_is_dotProduct`). -/
theorem dual_eq_dotProduct [DecidableEq ι] (φ : Module.Dual 𝕜 (ι → 𝕜)) (u : ι → 𝕜) :
    φ u = u ⬝ᵥ (fun i => φ (Pi.single i 1)) := by
  have hu : u = ∑ i, u i • (Pi.single i (1 : 𝕜)) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  conv_lhs => rw [hu]
  simp [map_sum, dotProduct]

/-- [proved-derived; formal-checked] **Fredholm over a field** (the field form of
`EditRigidity.mem_range_iff_annihilators_vanish`): `y ∈ range M` iff every left-null covector
annihilates `y`. -/
theorem mem_range_iff_annihilators_vanish [DecidableEq ι] (M : Matrix ι ν 𝕜) (y : ι → 𝕜) :
    (∃ x : ν → 𝕜, M *ᵥ x = y) ↔ ∀ w : ι → 𝕜, Mᵀ *ᵥ w = 0 → w ⬝ᵥ y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ w hw
    rw [dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
  · intro h
    set W : Submodule 𝕜 (ι → 𝕜) := LinearMap.range (Matrix.mulVecLin M) with hW
    have hy : y ∈ W.dualAnnihilator.dualCoannihilator := by
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      set w : ι → 𝕜 := fun i => φ (Pi.single i 1) with hwdef
      have hann : Mᵀ *ᵥ w = 0 := by
        funext j
        have hall : ∀ x : ν → 𝕜, (M *ᵥ x) ⬝ᵥ w = 0 := by
          intro x
          have hmem := (Submodule.mem_dualAnnihilator φ).mp hφ (M *ᵥ x) ⟨x, rfl⟩
          rw [dual_eq_dotProduct φ (M *ᵥ x)] at hmem
          exact hmem
        classical
        have hx := hall (Pi.single j 1)
        rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at hx
        rw [mulVec_transpose]
        simpa using hx
      have hzero := h w hann
      rw [dual_eq_dotProduct φ y]
      simpa [dotProduct_comm] using hzero
    rw [Subspace.dualAnnihilator_dualCoannihilator_eq] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hx⟩

end Fredholm

end Holonics.HolonCore
