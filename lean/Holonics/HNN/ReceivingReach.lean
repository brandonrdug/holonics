import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# HNN.ReceivingReach: the receiving map opens at zero, the source map reaches the contact as motion

[proved-derived; formal-checked] Three answers about the receiving map `R` and the source map `E`
(`hnn::constitution::Constitution::initial`, `hnn::moment::SourceMoment::open_storage`,
`hnn::word::continuation::compare_contact_storage`, `hnn::reference::compose_contact`). The record
`research/records/2026-10-02_THE_RECEIVING_MAP_OPENS_AT_ZERO_AND_THE_SOURCE_MAP_REACHES_THE_CONTACT_ONLY_AS_MOTION.md`
reads them on the code.

```text
first deposit    R₀ = 0 ,  ΔR = η Σ_t w_t g_t (X̂ f_t)ᵀ   ⇒   R₁ f = Σ_t η w_t ⟨X̂ f_t, f⟩ g_t
source reach     ΔC = 0 :  m ζ = b ,  m ζ′ = b′           ⇒   ⟨λ, ζ′ − ζ⟩ = ⟨r, b′ − b⟩ ,  rᵀm = λ
storage dual     m′(ζ′ − ζ) = ΔC j ,  rᵀm′ = λ           ⇒   ⟨λ, ζ′ − ζ⟩ = Σ_ik ΔC_ik r_i j_k
```

1. **The first deposit is a kernel read** (`first_deposit_read`). The receiving map's normal law
   moves `R` by its unit step `D = Σ_t w_t g_t (X̂ f_t)ᵀ` at the certified `η`. From `R₀ = 0` the
   formed map reads a later feature `f` as the comparison covectors `g_t` weighted by their
   features' overlap `⟨X̂ f_t, f⟩` with it. At `R₀ = 0` the face is the tree's, which reads no wave,
   so the first covectors `g_t = q_t − p_t` do not depend on `E`: two receivers formed on the same
   requests from two source maps differ only through their features `f = P_R^(τ_R) v_R` and the
   charts `X̂` those features carry.
2. **A source-map change reaches the next contact only as motion** (`passage_reach_of_unmoved_material`).
   `E` is not in the power form; it enters the passage at the open (`open_storage`). With the
   material unmoved the contact operator `m` is the same, and the change of the transit's solve
   is `m⁻¹` of the change of its right side `h(α_g − α_h) + 2Cw − hKu`, the arrivals and the state.
   A comparison covector `λ` on the solve reads that change through the adjoint solve `r`,
   `rᵀm = λ`, paired with the right side's change. Nothing is deposited at the contact: by the
   storage response `m′(ζ′ − ζ) = ΔC(w − w⁺)` (`HNN/StorageResolution`), `ΔC = 0` is no response.
3. **The storage covector is dual to the storage response** (`adjoint_read_of_response`,
   `pairing_eq_frobenius`). At the deposited operator `m′`, the read `⟨λ, ζ′ − ζ⟩` of the response
   `m′(ζ′ − ζ) = ΔC j` is exactly the Frobenius pairing of `ΔC` with `r jᵀ`, `r` the adjoint solve
   at `m′`. With `j = w − w⁺ = 2(w − ω)` this is `compose_contact`'s storage pull
   `C̄ = Σ 2 r̄ (w − ω)ᵀ`: the covector `C` learns from is the rate's jump, the one thing a storage
   change acts on. It is exact, not first-order, when `r` is read at `m′`; the executed pull reads
   `r̄` at the producing `m`, and the two differ by `ΔC`'s own term.

A covector reaches the contact only through `Rᵀ g`: at `R = 0` the read is zero, every adjoint
solve `r̄` is zero, and the storage pull is zero. The first comparison on an opening constitution
moves `R` alone, and `C` receives a covector from the second on.
-/

namespace Holonics.HNN.ReceivingReach

open Matrix

variable {m n T : Type*} [Fintype m] [Fintype n] [Fintype T]

omit [Fintype m] in
/-- [proved-derived; formal-checked] **The first deposit reads features by their overlap.** A map
formed from zero by the unit step `Σ_t (η w_t) g_t (X f_t)ᵀ` reads a feature `f` as the covectors
`g_t`, each weighted by `η w_t ⟨X f_t, f⟩`. -/
theorem first_deposit_read (η : ℚ) (w : T → ℚ) (g : T → m → ℚ) (X : Matrix n n ℚ)
    (f : T → n → ℚ) (x : n → ℚ) :
    (0 + ∑ t, (η * w t) • vecMulVec (g t) (X *ᵥ f t)) *ᵥ x =
      ∑ t, (η * w t * ((X *ᵥ f t) ⬝ᵥ x)) • g t := by
  rw [zero_add, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

omit [Fintype m] [Fintype T] in
/-- [proved-derived; formal-checked] **A zero map reads nothing**, whatever the feature: at
`R₀ = 0` no feature, so no source map, moves a logit. -/
theorem zero_map_reads_nothing (x : n → ℚ) : (0 : Matrix m n ℚ) *ᵥ x = 0 := zero_mulVec x

/-- [proved-derived; formal-checked] **The adjoint reads a response.** If `M v = b` and
`rᵀM = λ`, then `⟨λ, v⟩ = ⟨r, b⟩`. -/
theorem adjoint_read_of_response (M : Matrix n n ℚ) (r lam v b : n → ℚ)
    (hr : r ᵥ* M = lam) (hv : M *ᵥ v = b) : lam ⬝ᵥ v = r ⬝ᵥ b := by
  rw [← hr, ← dotProduct_mulVec, hv]

/-- [proved-derived; formal-checked] **A source-map change reaches the solve only as motion.** With
the contact operator unchanged (`m ζ = b`, `m ζ′ = b′`), the read of the solve's change through
the adjoint solve `rᵀm = λ` is the right side's change paired with `r`. -/
theorem passage_reach_of_unmoved_material (M : Matrix n n ℚ) (r lam ζ ζ' b b' : n → ℚ)
    (hr : r ᵥ* M = lam) (hζ : M *ᵥ ζ = b) (hζ' : M *ᵥ ζ' = b') :
    lam ⬝ᵥ (ζ' - ζ) = r ⬝ᵥ (b' - b) :=
  adjoint_read_of_response M r lam (ζ' - ζ) (b' - b) hr (by rw [mulVec_sub, hζ, hζ'])

/-- [proved-derived; formal-checked] **The pairing with `ΔC j` is the Frobenius pairing of `ΔC` with
`r jᵀ`.** -/
theorem pairing_eq_frobenius (ΔC : Matrix n n ℚ) (r j : n → ℚ) :
    r ⬝ᵥ (ΔC *ᵥ j) = ∑ i, ∑ k, ΔC i k * (r i * j k) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- [proved-derived; formal-checked] **The storage covector is dual to the storage response.** If the
deposited operator `M′` carries the response `M′(ζ′ − ζ) = ΔC j` and `r` is its adjoint solve
`rᵀM′ = λ`, then `⟨λ, ζ′ − ζ⟩ = Σ_ik ΔC_ik r_i j_k`: the read moves by `ΔC` paired with `r jᵀ`, and
with `j = w − w⁺` that outer product is the storage pull. -/
theorem storage_covector_dual (M' ΔC : Matrix n n ℚ) (r lam ζ ζ' j : n → ℚ)
    (hr : r ᵥ* M' = lam) (hresp : M' *ᵥ (ζ' - ζ) = ΔC *ᵥ j) :
    lam ⬝ᵥ (ζ' - ζ) = ∑ i, ∑ k, ΔC i k * (r i * j k) := by
  rw [adjoint_read_of_response M' r lam (ζ' - ζ) (ΔC *ᵥ j) hr hresp, pairing_eq_frobenius]

/-- [proved-derived; formal-checked] **The midpoint's slip is half the rate's jump**: with
`w⁺ = 2ω − w`, `2(w − ω) = w − w⁺`, so `compose_contact`'s `Σ 2 r̄ (w − ω)ᵀ` is `Σ r̄ (w − w⁺)ᵀ`. -/
theorem slip_is_half_jump {E : Type*} (w ω : E → ℚ) : (2 : ℚ) • (w - ω) = w - ((2 : ℚ) • ω - w) := by
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end Holonics.HNN.ReceivingReach
