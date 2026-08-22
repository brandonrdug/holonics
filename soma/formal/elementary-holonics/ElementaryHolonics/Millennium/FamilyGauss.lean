import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# FamilyGauss: the split-chart rotation at every modulus

**The family engine of the congruent-number campaign.**  The eigenidentity that carried
the sign-`−1` theta functional equation at five —

```text
∑_{r,s} χ(r² − s²) ζ^{ξr + ηs} = χ(ξ² − η²) · g(χ)²
```

— was never about five.  Its proof is one rotation of the split chart
`(r, s) ↦ (r+s, r−s)`, factoring the double sum into two twisted Gauss sums, and it
holds at **every** odd modulus for **every** quadratic character and **every**
primitive additive character:

* **`theSplitChartRotationAtEveryModulus`** — the identity over any finite field of
  odd characteristic, coefficients in any domain;
* **`theFamilyEigenIdentityOnTheSplitResidues`** — the specialization at `ZMod p`
  with `p ≡ 1 (mod 4)`, where `g(χ)² = p` and the identity reads exactly as the
  five-instance did, with `p` a parameter.

The modulus is a chart parameter, not an instance wall.  Every `theorem` is
discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilyGauss

open AddChar MulChar

/-! ## 1. The twisted-sum law -/

/-- A multiplicative character squares to one on every nonzero argument once it is
quadratic. -/
private lemma quad_sq_one {F : Type} [Field F] [Fintype F] {R' : Type} [CommRing R']
    [IsDomain R'] {χ : MulChar F R'} (hχ₂ : χ.IsQuadratic) {a : F} (ha : a ≠ 0) :
    χ a * χ a = 1 := by
  rcases hχ₂ a with h | h | h
  · exfalso
    have hone : χ a * χ a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    rw [h, zero_mul] at hone
    exact zero_ne_one hone
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- **The twisted Gauss sum**: shifting the additive character by `a` costs exactly
`χ(a)` when `χ` is quadratic — and the shift by zero annihilates the sum. -/
private lemma twisted_sum {F : Type} [Field F] [Fintype F] {R' : Type} [CommRing R']
    [IsDomain R'] {χ : MulChar F R'} (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    (ψ : AddChar F R') (a : F) :
    (∑ u : F, χ u * ψ (a * u)) = χ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst ha
    have h1 : ∀ u : F, χ u * ψ (0 * u) = χ u := by
      intro u
      rw [zero_mul, map_zero_eq_one, mul_one]
    rw [Finset.sum_congr rfl fun u _ => h1 u, MulChar.sum_eq_zero_of_ne_one hχ₁,
      MulChar.map_zero, zero_mul]
  · set ua : Fˣ := Units.mk0 a ha with hua
    have h1 := gaussSum_mulShift χ ψ ua
    have h2 : (∑ u : F, χ u * ψ (a * u)) = gaussSum χ (mulShift ψ (ua : F)) := by
      simp only [gaussSum, mulShift_apply]
      rfl
    have hquad : χ a * χ a = 1 := quad_sq_one hχ₂ ha
    calc (∑ u : F, χ u * ψ (a * u))
        = gaussSum χ (mulShift ψ (ua : F)) := h2
      _ = (χ a * χ a) * gaussSum χ (mulShift ψ (ua : F)) := by rw [hquad, one_mul]
      _ = χ a * (χ (ua : F) * gaussSum χ (mulShift ψ ua)) := by
          rw [mul_assoc]
          rfl
      _ = χ a * gaussSum χ ψ := by rw [h1]

/-! ## 2. The rotation at every modulus -/

set_option maxHeartbeats 1000000 in
/-- **THE SPLIT-CHART ROTATION AT EVERY MODULUS**: over any finite field of odd
characteristic, for any nontrivial quadratic character and any primitive additive
character,

`∑_{r,s} χ(r² − s²)·ψ(ξr + ηs) = χ(ξ² − η²)·g(χ)²`.

The rotation `(r, s) ↦ (r+s, r−s)` splits the difference of squares into a product
and factors the double sum into two twisted Gauss sums — the mechanism that returned
the theta functional equation at five, with the modulus now a parameter. -/
theorem theSplitChartRotationAtEveryModulus
    {F : Type} [Field F] [Fintype F] {R' : Type} [CommRing R'] [IsDomain R']
    (h2 : (2 : F) ≠ 0)
    {χ : MulChar F R'} (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    (ψ : AddChar F R') (ξ η : F) :
    ∑ r : F, ∑ s : F, χ (r ^ 2 - s ^ 2) * ψ (ξ * r + η * s)
      = χ (ξ ^ 2 - η ^ 2) * gaussSum χ ψ ^ 2 := by
  set α : F := (ξ + η) / 2 with hα
  set β : F := (ξ - η) / 2 with hβ
  -- the rotation of the split chart
  set e : F × F ≃ F × F :=
    { toFun := fun p => ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
      invFun := fun q => (q.1 + q.2, q.1 - q.2)
      left_inv := by
        intro p
        ext
        · show (p.1 + p.2) / 2 + (p.1 - p.2) / 2 = p.1
          field_simp
          ring
        · show (p.1 + p.2) / 2 - (p.1 - p.2) / 2 = p.2
          field_simp
          ring
      right_inv := by
        intro q
        ext
        · show (q.1 + q.2 + (q.1 - q.2)) / 2 = q.1
          field_simp
          ring
        · show (q.1 + q.2 - (q.1 - q.2)) / 2 = q.2
          field_simp
          ring } with he
  have hrot : ∑ r : F, ∑ s : F, χ (r ^ 2 - s ^ 2) * ψ (ξ * r + η * s)
      = ∑ u : F, ∑ v : F, (χ u * ψ (α * u)) * (χ v * ψ (β * v)) := by
    rw [← Finset.sum_product', ← Finset.sum_product']
    refine (Fintype.sum_equiv e
      (fun q => (χ q.1 * ψ (α * q.1)) * (χ q.2 * ψ (β * q.2)))
      (fun p => χ (p.1 ^ 2 - p.2 ^ 2) * ψ (ξ * p.1 + η * p.2)) ?_).symm
    intro q
    show (χ q.1 * ψ (α * q.1)) * (χ q.2 * ψ (β * q.2))
      = χ (((q.1 + q.2) / 2) ^ 2 - ((q.1 - q.2) / 2) ^ 2)
        * ψ (ξ * ((q.1 + q.2) / 2) + η * ((q.1 - q.2) / 2))
    have hsq : ((q.1 + q.2) / 2) ^ 2 - ((q.1 - q.2) / 2) ^ 2 = q.1 * q.2 := by
      field_simp
      ring
    have harg : ξ * ((q.1 + q.2) / 2) + η * ((q.1 - q.2) / 2)
        = α * q.1 + β * q.2 := by
      rw [hα, hβ]
      field_simp
      ring
    rw [hsq, harg, show χ (q.1 * q.2) = χ q.1 * χ q.2 from map_mul χ q.1 q.2,
      ψ.map_add_eq_mul]
    ring
  rw [hrot, ← Fintype.sum_mul_sum, twisted_sum hχ₁ hχ₂ ψ α, twisted_sum hχ₁ hχ₂ ψ β]
  -- the factorization of the target class
  have hfac : ξ ^ 2 - η ^ 2 = 2 * 2 * (α * β) := by
    rw [hα, hβ]
    field_simp
    ring
  have h2sq : χ 2 * χ 2 = 1 := quad_sq_one hχ₂ h2
  have hexp : χ (ξ ^ 2 - η ^ 2) = χ α * χ β := by
    rw [hfac, show χ (2 * 2 * (α * β)) = χ (2 * 2) * χ (α * β) from map_mul χ _ _,
      show χ ((2 : F) * 2) = χ 2 * χ 2 from map_mul χ _ _,
      show χ (α * β) = χ α * χ β from map_mul χ _ _, h2sq, one_mul]
  rw [hexp]
  ring

/-! ## 3. The family eigenidentity on the split residues -/

set_option maxHeartbeats 1000000 in
/-- **THE FAMILY EIGENIDENTITY ON THE SPLIT RESIDUES**: at every prime
`p ≡ 1 (mod 4)`, for every primitive additive character,

`∑_{r,s} χ_p(r² − s²)·ψ(ξr + ηs) = p·χ_p(ξ² − η²)`

— the eigenidentity that carried the five-theta functional equation, with the
modulus a parameter.  The eigenvalue is the modulus itself because `g(χ)² = χ(−1)·p`
and the split residues make `−1` a square. -/
theorem theFamilyEigenIdentityOnTheSplitResidues (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (ξ η : ZMod p) :
    ∑ r : ZMod p, ∑ s : ZMod p,
        ((quadraticChar (ZMod p) (r ^ 2 - s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s)
      = (p : ℂ) * ((quadraticChar (ZMod p) (ξ ^ 2 - η ^ 2) : ℤ) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := Ring.two_ne_zero hchar
    exact this
  set χ : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) with hχ
  have hχ₁ : χ ≠ 1 := by
    rw [hχ, MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)]
    exact quadraticChar_ne_one hchar
  have hχ₂ : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have happ : ∀ a : ZMod p, χ a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
    intro a
    rw [hχ]
    rfl
  have hmain := theSplitChartRotationAtEveryModulus h2 hχ₁ hχ₂ ψ ξ η
  have hgauss : gaussSum χ ψ ^ 2 = (p : ℂ) := by
    rw [gaussSum_sq hχ₁ hχ₂ hψ]
    have hm1 : χ (-1) = 1 := by
      rw [happ, quadraticChar_neg_one hchar, ZMod.card p, ZMod.χ₄_nat_one_mod_four hp1]
      norm_num
    rw [hm1, one_mul, ZMod.card p]
  calc ∑ r : ZMod p, ∑ s : ZMod p,
        ((quadraticChar (ZMod p) (r ^ 2 - s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s)
      = ∑ r : ZMod p, ∑ s : ZMod p, χ (r ^ 2 - s ^ 2) * ψ (ξ * r + η * s) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        rw [happ]
    _ = χ (ξ ^ 2 - η ^ 2) * gaussSum χ ψ ^ 2 := hmain
    _ = (p : ℂ) * ((quadraticChar (ZMod p) (ξ ^ 2 - η ^ 2) : ℤ) : ℂ) := by
        rw [hgauss, happ]
        ring

end Soma.Holonics.Millennium.FamilyGauss
