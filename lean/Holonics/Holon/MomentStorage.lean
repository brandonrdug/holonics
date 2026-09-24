import Holonics.Holon.Element
import Holonics.Holon.QuadraticMoment

/-!
# Holon.MomentStorage: the quadratic moment is one storage element

[proved-derived; formal-checked] The weighted second moment `C = Σ_s w_s f_s f_sᵀ`
(`Millennium/HolonicQuadraticMomentCondensation.lean::quadraticMoment`) is a symmetric storage
form, and its storage energy is the energy of the rank-one family itself:

`storageEnergy C x = ½ Σ_s w_s ⟨f_s, x⟩²`.

With nonnegative weights the storage is passive (`0 ≤ storageEnergy C x`). This is the law behind
plan phase 13: the compact image chart `Bᵀ H B`, the rooted spine and the fixed pair carrier of
`holonic-engine::factored_moment` (and the resident card that realizes them) are one
`ElementRelation::Storage`, `QuadraticMomentStorage` in Rust.

| Lean | Rust |
|---|---|
| `quadraticMoment_symm` | `QuadraticMomentStorage::storage_form` (refuses an asymmetric chart) |
| `storageEnergy_quadraticMoment` | `QuadraticMomentStorage::stored_energy` |
| `storageEnergy_quadraticMoment_nonneg` | `QuadraticMomentStorage::is_passive` |
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix
open scoped BigOperators
open Holonics.Millennium.HolonicQuadraticMomentCondensation

variable {𝕜 : Type*} [Field 𝕜] {Support σ : Type*} [Fintype Support] [Fintype σ]

omit [Fintype σ] in
/-- The weighted second moment is symmetric. -/
theorem quadraticMoment_symm (w : Support → 𝕜) (f : Support → σ → 𝕜) :
    (quadraticMoment w f)ᵀ = quadraticMoment w f := by
  ext i j
  simp only [transpose_apply, quadraticMoment]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `⟨x, C x⟩ = Σ_s w_s ⟨f_s, x⟩²`: the quadratic form of the moment is the family's. -/
theorem dotProduct_mulVec_quadraticMoment (w : Support → 𝕜) (f : Support → σ → 𝕜)
    (x : σ → 𝕜) :
    x ⬝ᵥ (quadraticMoment w f *ᵥ x) = ∑ s, w s * (f s ⬝ᵥ x) ^ 2 := by
  have hcontract :
      x ⬝ᵥ (quadraticMoment w f *ᵥ x) =
        contractMoment (Matrix.of fun i j => x i * x j) (quadraticMoment w f) := by
    simp only [dotProduct, mulVec, contractMoment, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hcontract, contract_quadraticMoment_eq_enumerateQuadraticReceiver]
  simp only [enumerateQuadraticReceiver, Matrix.of_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [sq, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The storage energy of the moment is `½ Σ_s w_s ⟨f_s, x⟩²`. -/
theorem storageEnergy_quadraticMoment (w : Support → 𝕜) (f : Support → σ → 𝕜) (x : σ → 𝕜) :
    storageEnergy (quadraticMoment w f) x = (1 / 2 : 𝕜) * ∑ s, w s * (f s ⬝ᵥ x) ^ 2 := by
  rw [storageEnergy, dotProduct_mulVec_quadraticMoment]

/-- A nonnegative-weight moment is passive storage. -/
theorem storageEnergy_quadraticMoment_nonneg [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (w : Support → 𝕜) (hw : ∀ s, 0 ≤ w s) (f : Support → σ → 𝕜) (x : σ → 𝕜) :
    0 ≤ storageEnergy (quadraticMoment w f) x := by
  rw [storageEnergy_quadraticMoment]
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (sq_nonneg _))

end Holonics.HolonCore
