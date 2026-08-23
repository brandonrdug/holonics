import ElementaryHolonics.Millennium.FamilyGenocchi
import Mathlib.Tactic

/-!
# FamilyFiveDescent: the descent collapses to eight cells at every prime five mod eight

**The unconditional rank squeeze on the odd-sign branch.**  At `p ≡ 5 (mod 8)` the
character table reads `χ_p(−1) = 1`, `χ_p(2) = χ_p(−2) = −1`, and the residue reads
alone collapse the sixty-four descent cells to **eight** — four torsion cells and one
coset:

* **`theSlotClassesCollapseOnTheFiveModEightBranch`** — the mod-`p` collapse;
* (next stage) the eight-cell pigeonhole forces `2^{r+2} ≤ 8`, so the rank is at
  most **one** at every prime `p ≡ 5 (mod 8)` — against the standing analytic rank
  `≥ 1`, the conjecture's prediction of rank exactly one is squeezed to within a
  single point.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyFiveDescent

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyGenocchi

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The character table at five mod eight -/

lemma chi5_neg_one (hp8 : p % 8 = 5) :
    quadraticChar (ZMod p) ((-1 : ℤ) : ZMod p) = 1 := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [show ((-1 : ℤ) : ZMod p) = (-1 : ZMod p) from by push_cast; ring,
    quadraticChar_neg_one hchar, ZMod.card p, ZMod.χ₄_nat_one_mod_four (by omega)]

lemma chi5_two (hp8 : p % 8 = 5) :
    quadraticChar (ZMod p) ((2 : ℤ) : ZMod p) = -1 := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) from by push_cast; ring,
    quadraticChar_two hchar, ZMod.card p, ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (by omega), if_neg (by omega)]

lemma chi5_neg_two (hp8 : p % 8 = 5) :
    quadraticChar (ZMod p) ((-2 : ℤ) : ZMod p) = -1 := by
  have h := congrArg (quadraticChar (ZMod p))
    (show ((-2 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) * ((2 : ℤ) : ZMod p) from by
      push_cast; ring)
  rw [map_mul, chi5_neg_one hp8, chi5_two hp8] at h
  rw [h]
  ring

/-- The `p`-free rungs with character one are `1` and `−1`. -/
lemma rung5_char_one (hp8 : p % 8 = 5) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hfree : ¬ (p : ℤ) ∣ d)
    (hchi : quadraticChar (ZMod p) ((d : ZMod p)) = 1) :
    d = 1 ∨ d = -1 := by
  have hp : p.Prime := Fact.out
  have h4 := FamilyPrimeRank.dvd_two_mul_prime hp hdvd
  have habs := Int.natAbs_eq d
  have hpd : (p : ℤ) ∣ (p : ℤ) := dvd_refl ((p : ℤ))
  have h2pd : (p : ℤ) ∣ 2 * (p : ℤ) := ⟨2, by ring⟩
  have hnp : d ≠ (p : ℤ) ∧ d ≠ -(p : ℤ) ∧ d ≠ 2 * p ∧ d ≠ -(2 * (p : ℤ)) := by
    refine ⟨fun h0 => hfree (h0 ▸ hpd), fun h0 => hfree (h0 ▸ dvd_neg.mpr hpd),
      fun h0 => hfree (h0 ▸ h2pd), fun h0 => hfree (h0 ▸ dvd_neg.mpr h2pd)⟩
  have hd14 : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
    rcases h4 with h | h | h | h <;> omega
  rcases hd14 with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [chi5_two hp8] at hchi
    omega
  · rw [chi5_neg_two hp8] at hchi
    omega

/-- The `p`-free rungs with character minus one are `2` and `−2`. -/
lemma rung5_char_neg_one (hp8 : p % 8 = 5) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hfree : ¬ (p : ℤ) ∣ d)
    (hchi : quadraticChar (ZMod p) ((d : ZMod p)) = -1) :
    d = 2 ∨ d = -2 := by
  have hp : p.Prime := Fact.out
  have h4 := FamilyPrimeRank.dvd_two_mul_prime hp hdvd
  have habs := Int.natAbs_eq d
  have hpd : (p : ℤ) ∣ (p : ℤ) := dvd_refl ((p : ℤ))
  have h2pd : (p : ℤ) ∣ 2 * (p : ℤ) := ⟨2, by ring⟩
  have hnp : d ≠ (p : ℤ) ∧ d ≠ -(p : ℤ) ∧ d ≠ 2 * p ∧ d ≠ -(2 * (p : ℤ)) := by
    refine ⟨fun h0 => hfree (h0 ▸ hpd), fun h0 => hfree (h0 ▸ dvd_neg.mpr hpd),
      fun h0 => hfree (h0 ▸ h2pd), fun h0 => hfree (h0 ▸ dvd_neg.mpr h2pd)⟩
  have hd14 : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
    rcases h4 with h | h | h | h <;> omega
  rcases hd14 with rfl | rfl | rfl | rfl
  · rw [chi_one'] at hchi
    omega
  · rw [chi5_neg_one hp8] at hchi
    omega
  · exact Or.inl rfl
  · exact Or.inr rfl


/-! ## 2. The collapse at five mod eight -/

open WeierstrassCurve.Affine
open DirectSum
open Soma.Holonics.Millennium.FamilyKernel
open Soma.Holonics.Millennium.FamilySupport

set_option maxHeartbeats 4000000 in
/-- **THE SLOT CLASSES COLLAPSE ON THE FIVE-MOD-EIGHT BRANCH**: at every prime
`p ≡ 5 (mod 8)`, the slot-class pair of any point of `y² = x³ − p²x` with `y ≠ 0`
lies among **eight** named cells — four torsion cells and one coset — under the
character table `χ_p(−1) = 1`, `χ_p(2) = χ_p(−2) = −1`. -/
theorem theSlotClassesCollapseOnTheFiveModEightBranch
    (hp8 : p % 8 = 5) {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - ((p : ℕ) : ℚ) ^ 2 * x) (hy : y ≠ 0)
    {d₁ d₂ : ℤ} (h₁0 : d₁ ≠ 0) (h₂0 : d₂ ≠ 0)
    (h₁v : d₁.natAbs ∣ 2 * p) (h₂v : d₂.natAbs ∣ 2 * p)
    (h₁ : Descent.SqCls x ((d₁ : ℤ) : ℚ))
    (h₂ : Descent.SqCls (x - ((p : ℕ) : ℚ)) ((d₂ : ℤ) : ℚ)) :
    (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = -1 ∧ d₂ = -1) ∨
    (d₁ = 1 ∧ d₂ = (p : ℤ)) ∨ (d₁ = -1 ∧ d₂ = -(p : ℤ)) ∨
    (d₁ = (p : ℤ) ∧ d₂ = 2) ∨ (d₁ = -(p : ℤ) ∧ d₂ = -2) ∨
    (d₁ = (p : ℤ) ∧ d₂ = 2 * p) ∨ (d₁ = -(p : ℤ) ∧ d₂ = -2 * p) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hpqpos : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  obtain ⟨hx0, hxn, hxmn⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
  have hxm0 : x - ((p : ℕ) : ℚ) ≠ 0 := sub_ne_zero.mpr hxn
  have hxp0 : x + ((p : ℕ) : ℚ) ≠ 0 := fun hc => hxmn (by linarith)
  have hy2 : 0 < y ^ 2 :=
    (sq_nonneg y).lt_of_ne fun h => hy (pow_eq_zero_iff two_ne_zero |>.mp h.symm)
  have hfact : y ^ 2 = x * (x - ((p : ℕ) : ℚ)) * (x + ((p : ℕ) : ℚ)) := by
    linear_combination hcurve
  have hxppos : 0 < x + ((p : ℕ) : ℚ) := by
    rcases lt_trichotomy (x + ((p : ℕ) : ℚ)) 0 with h | h | h
    · exfalso
      have hxneg : x < 0 := by linarith
      have hxmneg : x - ((p : ℕ) : ℚ) < 0 := by linarith
      nlinarith [mul_pos_of_neg_of_neg hxneg hxmneg]
    · exact absurd h hxp0
    · exact h
  have h₃ : Descent.SqCls (x + ((p : ℕ) : ℚ)) (((d₁ * d₂ : ℤ)) : ℚ) :=
    sqcls_third hcurve hy hx0 hxm0 h₁ h₂
  have h₁₂0 : d₁ * d₂ ≠ 0 := mul_ne_zero h₁0 h₂0
  have h₁₂pos : 0 < d₁ * d₂ := sqcls_sign h₃ hxppos
  -- the valuation ledger
  have hvp : padicValRat p (((p : ℕ) : ℚ)) = 1 := val_p hp
  have hvsum : 2 * padicValRat p y = padicValRat p x
      + padicValRat p (x - ((p : ℕ) : ℚ)) + padicValRat p (x + ((p : ℕ) : ℚ)) := by
    have h1 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← h1, hfact, padicValRat.mul (mul_ne_zero hx0 hxm0) hxp0,
      padicValRat.mul hx0 hxm0]
  set V : ℤ := padicValRat p x with hV
  by_cases hVle : V ≤ 0
  · -- the shifted-unit case: both classes are `p`-free with character one
    have hvxm : padicValRat p (x - ((p : ℕ) : ℚ)) = V := by
      have he : x - ((p : ℕ) : ℚ) = x + (-((p : ℕ) : ℚ)) := by ring
      rw [he]
      refine FamilySupport.val_add_left hx0 (by rw [← he]; exact hxm0) ?_
      rw [padicValRat.neg, hvp]
      omega
    have hvxp : padicValRat p (x + ((p : ℕ) : ℚ)) = V := by
      refine FamilySupport.val_add_left hx0 hxp0 ?_
      rw [hvp]
      omega
    have hVeven : Even V := by
      rw [hvxm, hvxp] at hvsum
      exact ⟨padicValRat p y - V, by omega⟩
    -- the classes are `p`-free
    have hfree₁ : ¬ (p : ℤ) ∣ d₁ := by
      rcases rung_split (by omega) h₁0 h₁v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
      · exact hf
      · obtain ⟨e, he⟩ := sqcls_val_parity (p := p) hx0 h₁0 h₁
        rw [hv1] at he
        obtain ⟨w, hw⟩ := hVeven
        omega
    have hfree₂ : ¬ (p : ℤ) ∣ d₂ := by
      rcases rung_split (by omega) h₂0 h₂v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
      · exact hf
      · obtain ⟨e, he⟩ := sqcls_val_parity (p := p) hxm0 h₂0 h₂
        rw [hvxm, hv1] at he
        obtain ⟨w, hw⟩ := hVeven
        omega
    have hfree₁₂ : ¬ (p : ℤ) ∣ d₁ * d₂ := by
      intro hc
      rw [int_dvd_natAbs, Int.natAbs_mul] at hc
      rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
      · exact hfree₁ (int_dvd_natAbs.mpr h)
      · exact hfree₂ (int_dvd_natAbs.mpr h)
    -- the shift to valuation zero
    set k : ℕ := (-V).toNat with hk
    have hkV : (k : ℤ) = -V := Int.toNat_of_nonneg (by omega)
    obtain ⟨j, hj⟩ : Even k := by
      obtain ⟨w, hw⟩ := hVeven
      refine ⟨(-w).toNat, ?_⟩
      omega
    have hppow : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ hpq0
    have hvpow : padicValRat p (((p : ℕ) : ℚ) ^ k) = k := by
      rw [padicValRat.pow hpq0, hvp]
      ring
    set x₁ : ℚ := x * ((p : ℕ) : ℚ) ^ k with hx₁
    set x₂ : ℚ := (x - ((p : ℕ) : ℚ)) * ((p : ℕ) : ℚ) ^ k with hx₂
    set x₃ : ℚ := (x + ((p : ℕ) : ℚ)) * ((p : ℕ) : ℚ) ^ k with hx₃
    have hx₁0 : x₁ ≠ 0 := mul_ne_zero hx0 hppow
    have hx₂0 : x₂ ≠ 0 := mul_ne_zero hxm0 hppow
    have hx₃0 : x₃ ≠ 0 := mul_ne_zero hxp0 hppow
    have hvx₁ : padicValRat p x₁ = 0 := by
      rw [hx₁, padicValRat.mul hx0 hppow, hvpow]
      omega
    have hvx₂ : padicValRat p x₂ = 0 := by
      rw [hx₂, padicValRat.mul hxm0 hppow, hvpow, hvxm]
      omega
    have hvx₃ : padicValRat p x₃ = 0 := by
      rw [hx₃, padicValRat.mul hxp0 hppow, hvpow, hvxp]
      omega
    have hsq₁ : Descent.SqCls x₁ ((d₁ : ℤ) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₁
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₁, hcv, hj]
      ring
    have hsq₂ : Descent.SqCls x₂ ((d₂ : ℤ) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₂
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₂, hcv, hj]
      ring
    have hsq₃ : Descent.SqCls x₃ (((d₁ * d₂ : ℤ)) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₃
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₃, hcv, hj]
      ring
    have hr₁ := chiRead_of_sqcls hx₁0 hvx₁ hfree₁ hsq₁
    have hr₂ := chiRead_of_sqcls hx₂0 hvx₂ hfree₂ hsq₂
    have hr₃ := chiRead_of_sqcls hx₃0 hvx₃ hfree₁₂ hsq₃
    have hc₁₂ : chiRead p x₁ = chiRead p x₂ := by
      refine chiRead_congr hx₁0 hx₂0 hvx₁ hvx₂ ?_
      have hd : x₁ - x₂ = ((p : ℕ) : ℚ) ^ (k + 1) := by
        rw [hx₁, hx₂]
        ring
      rw [hd, padicValRat.pow hpq0, hvp]
      omega
    have hc₁₃ : chiRead p x₁ = chiRead p x₃ := by
      refine chiRead_congr hx₁0 hx₃0 hvx₁ hvx₃ ?_
      have hd : x₁ - x₃ = -((p : ℕ) : ℚ) ^ (k + 1) := by
        rw [hx₁, hx₃]
        ring
      rw [hd, padicValRat.neg, padicValRat.pow hpq0, hvp]
      omega
    have hmul : quadraticChar (ZMod p) (((d₁ * d₂ : ℤ)) : ZMod p)
        = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
          quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [show (((d₁ * d₂ : ℤ)) : ZMod p) = ((d₁ : ZMod p)) * ((d₂ : ZMod p)) from by
        push_cast; ring, map_mul]
    have heq₁₂ : quadraticChar (ZMod p) ((d₁ : ZMod p))
        = quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [← hr₁, ← hr₂, hc₁₂]
    have heqprod : quadraticChar (ZMod p) ((d₁ : ZMod p))
        = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
          quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [← hmul, ← hr₃, ← hc₁₃, hr₁]
    have hne₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) ≠ 0 := by
      rw [Ne, quadraticChar_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hfree₁
    have hchi₂ : quadraticChar (ZMod p) ((d₂ : ZMod p)) = 1 :=
      mul_left_cancel₀ hne₁ (by rw [← heqprod, mul_one])
    have hchi₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) = 1 := by
      rw [heq₁₂, hchi₂]
    rcases rung5_char_one hp8 h₁0 h₁v hfree₁ hchi₁ with rfl | rfl <;>
      rcases rung5_char_one hp8 h₂0 h₂v hfree₂ hchi₂ with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      omega
    · exfalso
      omega
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · -- the `p`-adic branch: at least one slot meets the prime
    push_neg at hVle
    have hVpos : 0 < V := hVle
    have hvxm1 : 1 ≤ padicValRat p (x - ((p : ℕ) : ℚ)) := by
      have he : x - ((p : ℕ) : ℚ) = x + (-((p : ℕ) : ℚ)) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := -((p : ℕ) : ℚ)) (by rw [← he]; exact hxm0)
      rw [padicValRat.neg, hvp] at hmin
      rw [he]
      omega
    have hvxp1 : 1 ≤ padicValRat p (x + ((p : ℕ) : ℚ)) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := ((p : ℕ) : ℚ)) hxp0
      rw [hvp] at hmin
      omega
    set v₂ : ℤ := padicValRat p (x - ((p : ℕ) : ℚ)) with hv₂
    set v₃ : ℤ := padicValRat p (x + ((p : ℕ) : ℚ)) with hv₃
    -- at most one of the three valuations exceeds one
    have hpair₁₂ : ¬ (2 ≤ V ∧ 2 ≤ v₂) := by
      rintro ⟨ha, hb⟩
      have he : ((p : ℕ) : ℚ) = x + (-(x - ((p : ℕ) : ℚ))) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := -(x - ((p : ℕ) : ℚ))) (by rw [← he]; exact hpq0)
      rw [← he, padicValRat.neg, hvp] at hmin
      omega
    have hpair₁₃ : ¬ (2 ≤ V ∧ 2 ≤ v₃) := by
      rintro ⟨ha, hb⟩
      have he : ((p : ℕ) : ℚ) = (x + ((p : ℕ) : ℚ)) + (-x) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x + ((p : ℕ) : ℚ)) (r := -x) (by rw [← he]; exact hpq0)
      rw [← he, padicValRat.neg, hvp] at hmin
      omega
    have hv2p : padicValRat p ((2 : ℚ) * ((p : ℕ) : ℚ)) = 1 := by
      have h2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
        intro hc
        have := Int.le_of_dvd (by norm_num) hc
        omega
      have hv2 : padicValRat p ((2 : ℚ)) = 0 := by
        have := int_val_zero (p := p) h2
        push_cast at this ⊢
        exact this
      rw [padicValRat.mul (by norm_num) hpq0, hv2, hvp]
      ring
    have hpair₂₃ : ¬ (2 ≤ v₂ ∧ 2 ≤ v₃) := by
      rintro ⟨ha, hb⟩
      have he : (2 : ℚ) * ((p : ℕ) : ℚ)
          = (x + ((p : ℕ) : ℚ)) + (-(x - ((p : ℕ) : ℚ))) := by ring
      have hne : (2 : ℚ) * ((p : ℕ) : ℚ) ≠ 0 := by
        have := hpqpos
        positivity
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x + ((p : ℕ) : ℚ)) (r := -(x - ((p : ℕ) : ℚ))) (by rw [← he]; exact hne)
      rw [← he, padicValRat.neg, hv2p] at hmin
      omega
    -- the parities of the classes track the valuations
    obtain ⟨e₁, he₁⟩ := sqcls_val_parity (p := p) hx0 h₁0 h₁
    obtain ⟨e₂, he₂⟩ := sqcls_val_parity (p := p) hxm0 h₂0 h₂
    -- helper facts about small integers
    have hnd1 : ¬ (p : ℤ) ∣ (1 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) hc
      omega
    have hndm1 : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) (dvd_neg.mp hc)
      omega
    have hnd2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) hc
      omega
    have hndm2 : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) (dvd_neg.mp hc)
      omega
    -- decide which valuation is the even one
    rcases Int.even_or_odd V with hVe | hVo
    · -- `V` even, so `V ≥ 2` and `v₂ = v₃ = 1`
      have hV2 : 2 ≤ V := by
        obtain ⟨w, hw⟩ := hVe
        omega
      have hv₂1 : v₂ = 1 := by
        by_contra hc
        exact hpair₁₂ ⟨hV2, by omega⟩
      have hv₃1 : v₃ = 1 := by
        by_contra hc
        exact hpair₁₃ ⟨hV2, by omega⟩
      -- `d₁` is `p`-free, `d₂` meets the prime
      have hfree₁ : ¬ (p : ℤ) ∣ d₁ := by
        rcases rung_split (by omega) h₁0 h₁v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
        · exact hf
        · rw [hv1] at he₁
          obtain ⟨w, hw⟩ := hVe
          omega
      obtain ⟨d₂', hd₂', hd₂'free, hd₂'v, hd₂'0, -⟩ :
          ∃ d' : ℤ, d₂ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
            d' ≠ 0 ∧ padicValRat p ((d₂ : ℤ) : ℚ) = 1 := by
        rcases rung_split (by omega) h₂0 h₂v with ⟨hf, hv0⟩ | ⟨-, hr⟩
        · exfalso
          rw [hv0] at he₂
          omega
        · exact hr
      -- the reads at level `1/p`
      set z₂ : ℚ := (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₂
      set z₃ : ℚ := (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₃
      have hz₂0 : z₂ ≠ 0 := div_ne_zero hxm0 hpq0
      have hz₃0 : z₃ ≠ 0 := div_ne_zero hxp0 hpq0
      have hvz₂ : padicValRat p z₂ = 0 := by
        rw [hz₂, padicValRat.div hxm0 hpq0, hvp]
        omega
      have hvz₃ : padicValRat p z₃ = 0 := by
        rw [hz₃, padicValRat.div hxp0 hpq0, hvp]
        omega
      have hsqz₂ : Descent.SqCls z₂ ((d₂' : ℤ) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₂
        refine ⟨c, hc, ?_⟩
        rw [hz₂, hcv, hd₂']
        push_cast
        field_simp
        try ring
      have hsqz₃ : Descent.SqCls z₃ (((d₁ * d₂' : ℤ)) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₃
        refine ⟨c, hc, ?_⟩
        rw [hz₃, hcv, hd₂']
        push_cast
        field_simp
        try ring
      have hfree₁₂' : ¬ (p : ℤ) ∣ d₁ * d₂' := by
        intro hc
        rw [int_dvd_natAbs, Int.natAbs_mul] at hc
        rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
        · exact hfree₁ (int_dvd_natAbs.mpr h)
        · exact hd₂'free (int_dvd_natAbs.mpr h)
      have hrz₂ := chiRead_of_sqcls hz₂0 hvz₂ hd₂'free hsqz₂
      have hrz₃ := chiRead_of_sqcls hz₃0 hvz₃ hfree₁₂' hsqz₃
      have hcong₂ : chiRead p z₂ = chiRead p (((-1 : ℤ)) : ℚ) := by
        refine chiRead_congr hz₂0 (by norm_num) hvz₂ (int_val_zero hndm1) ?_
        have hd : z₂ - (((-1 : ℤ)) : ℚ) = x / ((p : ℕ) : ℚ) := by
          rw [hz₂]
          push_cast
          field_simp
          try ring
        rw [hd, padicValRat.div hx0 hpq0, hvp]
        omega
      have hcong₃ : chiRead p z₃ = chiRead p (((1 : ℤ)) : ℚ) := by
        refine chiRead_congr hz₃0 (by norm_num) hvz₃ (int_val_zero hnd1) ?_
        have hd : z₃ - (((1 : ℤ)) : ℚ) = x / ((p : ℕ) : ℚ) := by
          rw [hz₃]
          push_cast
          field_simp
          try ring
        rw [hd, padicValRat.div hx0 hpq0, hvp]
        omega
      have hchi₂' : quadraticChar (ZMod p) ((d₂' : ZMod p)) = 1 := by
        rw [← hrz₂, hcong₂, chiRead_intCast, chi5_neg_one hp8]
      have hchi₁₂' : quadraticChar (ZMod p) (((d₁ * d₂' : ℤ)) : ZMod p) = 1 := by
        rw [← hrz₃, hcong₃, chiRead_intCast, chi_one']
      have hchi₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) = 1 := by
        have hmul : quadraticChar (ZMod p) (((d₁ * d₂' : ℤ)) : ZMod p)
            = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
              quadraticChar (ZMod p) ((d₂' : ZMod p)) := by
          rw [show (((d₁ * d₂' : ℤ)) : ZMod p)
              = ((d₁ : ZMod p)) * ((d₂' : ZMod p)) from by push_cast; ring, map_mul]
        rw [hmul, hchi₂'] at hchi₁₂'
        linarith
      rcases rung5_char_one hp8 h₁0 h₁v hfree₁ hchi₁ with rfl | rfl <;>
        rcases rung5_char_one hp8 hd₂'0 hd₂'v hd₂'free hchi₂' with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    · -- `V = 1`; the even slot is the second or the third
      have hV1 : V = 1 := by
        by_contra hc
        have hV2 : 2 ≤ V := by
          obtain ⟨w, hw⟩ := hVo
          omega
        have hv₂1 : v₂ = 1 := by
          by_contra hc2
          exact hpair₁₂ ⟨hV2, by omega⟩
        have hv₃1 : v₃ = 1 := by
          by_contra hc2
          exact hpair₁₃ ⟨hV2, by omega⟩
        obtain ⟨w, hw⟩ := hVo
        omega
      obtain ⟨d₁', hd₁', hd₁'free, hd₁'v, hd₁'0, -⟩ :
          ∃ d' : ℤ, d₁ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
            d' ≠ 0 ∧ padicValRat p ((d₁ : ℤ) : ℚ) = 1 := by
        rcases rung_split (by omega) h₁0 h₁v with ⟨hf, hv0⟩ | ⟨-, hr⟩
        · exfalso
          rw [hv0] at he₁
          omega
        · exact hr
      set z₁ : ℚ := x / ((p : ℕ) : ℚ) with hz₁
      have hz₁0 : z₁ ≠ 0 := div_ne_zero hx0 hpq0
      have hvz₁ : padicValRat p z₁ = 0 := by
        rw [hz₁, padicValRat.div hx0 hpq0, hvp]
        omega
      have hsqz₁ : Descent.SqCls z₁ ((d₁' : ℤ) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₁
        refine ⟨c, hc, ?_⟩
        rw [hz₁, hcv, hd₁']
        push_cast
        field_simp
        try ring
      have hrz₁ := chiRead_of_sqcls hz₁0 hvz₁ hd₁'free hsqz₁
      rcases Int.even_or_odd v₂ with hv₂e | hv₂o
      · -- `v₂` even: the cells `(p, 2)` and `(−2p, −1)`
        have hv₂2 : 2 ≤ v₂ := by
          obtain ⟨w, hw⟩ := hv₂e
          omega
        have hfree₂ : ¬ (p : ℤ) ∣ d₂ := by
          rcases rung_split (by omega) h₂0 h₂v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
          · exact hf
          · rw [hv1] at he₂
            obtain ⟨w, hw⟩ := hv₂e
            omega
        set z₃ : ℚ := (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₃
        have hz₃0 : z₃ ≠ 0 := div_ne_zero hxp0 hpq0
        have hv₃1 : v₃ = 1 := by
          by_contra hc
          exact hpair₂₃ ⟨hv₂2, by omega⟩
        have hvz₃ : padicValRat p z₃ = 0 := by
          rw [hz₃, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hsqz₃ : Descent.SqCls z₃ (((d₁' * d₂ : ℤ)) : ℚ) := by
          obtain ⟨c, hc, hcv⟩ := h₃
          refine ⟨c, hc, ?_⟩
          rw [hz₃, hcv, hd₁']
          push_cast
          field_simp
          try ring
        have hfree₁₂' : ¬ (p : ℤ) ∣ d₁' * d₂ := by
          intro hc
          rw [int_dvd_natAbs, Int.natAbs_mul] at hc
          rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
          · exact hd₁'free (int_dvd_natAbs.mpr h)
          · exact hfree₂ (int_dvd_natAbs.mpr h)
        have hrz₃ := chiRead_of_sqcls hz₃0 hvz₃ hfree₁₂' hsqz₃
        have hcong₁ : chiRead p z₁ = chiRead p (((1 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₁0 (by norm_num) hvz₁ (int_val_zero hnd1) ?_
          have hd : z₁ - (((1 : ℤ)) : ℚ) = (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₁]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hcong₃ : chiRead p z₃ = chiRead p (((2 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₃0 (by norm_num) hvz₃ (int_val_zero hnd2) ?_
          have hd : z₃ - (((2 : ℤ)) : ℚ) = (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₃]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hchi₁' : quadraticChar (ZMod p) ((d₁' : ZMod p)) = 1 := by
          rw [← hrz₁, hcong₁, chiRead_intCast, chi_one']
        have hchi₁₂' : quadraticChar (ZMod p) (((d₁' * d₂ : ℤ)) : ZMod p) = -1 := by
          rw [← hrz₃, hcong₃, chiRead_intCast, chi5_two hp8]
        have hchi₂ : quadraticChar (ZMod p) ((d₂ : ZMod p)) = -1 := by
          have hmul : quadraticChar (ZMod p) (((d₁' * d₂ : ℤ)) : ZMod p)
              = quadraticChar (ZMod p) ((d₁' : ZMod p)) *
                quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
            rw [show (((d₁' * d₂ : ℤ)) : ZMod p)
                = ((d₁' : ZMod p)) * ((d₂ : ZMod p)) from by push_cast; ring, map_mul]
          rw [hmul, hchi₁'] at hchi₁₂'
          linarith
        rcases rung5_char_one hp8 hd₁'0 hd₁'v hd₁'free hchi₁' with rfl | rfl <;>
          rcases rung5_char_neg_one hp8 h₂0 h₂v hfree₂ hchi₂ with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))))
      · -- `v₂ = 1` and `v₃` even: the cells `(2p, p)` and `(−p, −2p)`
        have hv₂1 : v₂ = 1 := by
          by_contra hc
          have hv₂2 : 2 ≤ v₂ := by
            obtain ⟨w, hw⟩ := hv₂o
            omega
          have hv₃1 : v₃ = 1 := by
            by_contra hc2
            exact hpair₂₃ ⟨hv₂2, by omega⟩
          obtain ⟨w, hw⟩ := hv₂o
          omega
        have hv₃e : Even v₃ := by
          rw [hV1, hv₂1] at hvsum
          exact ⟨padicValRat p y - 1, by omega⟩
        obtain ⟨d₂', hd₂', hd₂'free, hd₂'v, hd₂'0, -⟩ :
            ∃ d' : ℤ, d₂ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
              d' ≠ 0 ∧ padicValRat p ((d₂ : ℤ) : ℚ) = 1 := by
          rcases rung_split (by omega) h₂0 h₂v with ⟨hf, hv0⟩ | ⟨-, hr⟩
          · exfalso
            rw [hv0] at he₂
            omega
          · exact hr
        set z₂ : ℚ := (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₂
        have hz₂0 : z₂ ≠ 0 := div_ne_zero hxm0 hpq0
        have hvz₂ : padicValRat p z₂ = 0 := by
          rw [hz₂, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hsqz₂ : Descent.SqCls z₂ ((d₂' : ℤ) : ℚ) := by
          obtain ⟨c, hc, hcv⟩ := h₂
          refine ⟨c, hc, ?_⟩
          rw [hz₂, hcv, hd₂']
          push_cast
          field_simp
          try ring
        have hrz₂ := chiRead_of_sqcls hz₂0 hvz₂ hd₂'free hsqz₂
        have hv₃2 : 2 ≤ v₃ := by
          obtain ⟨w, hw⟩ := hv₃e
          omega
        have hcong₁ : chiRead p z₁ = chiRead p (((-1 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₁0 (by norm_num) hvz₁ (int_val_zero hndm1) ?_
          have hd : z₁ - (((-1 : ℤ)) : ℚ) = (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₁]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hcong₂ : chiRead p z₂ = chiRead p (((-2 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₂0 (by norm_num) hvz₂ (int_val_zero hndm2) ?_
          have hd : z₂ - (((-2 : ℤ)) : ℚ) = (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₂]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hchi₁' : quadraticChar (ZMod p) ((d₁' : ZMod p)) = 1 := by
          rw [← hrz₁, hcong₁, chiRead_intCast, chi5_neg_one hp8]
        have hchi₂' : quadraticChar (ZMod p) ((d₂' : ZMod p)) = -1 := by
          rw [← hrz₂, hcong₂, chiRead_intCast, chi5_neg_two hp8]
        rcases rung5_char_one hp8 hd₁'0 hd₁'v hd₁'free hchi₁' with rfl | rfl <;>
          rcases rung5_char_neg_one hp8 hd₂'0 hd₂'v hd₂'free hchi₂' with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega⟩))))))
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by omega, by omega⟩))))))





/-! ## 3. The rung pins: three invariants determine the class -/

private lemma rung_cases (hp3 : 2 < p) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) :
    d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨ d = (p : ℤ) ∨ d = -(p : ℤ) ∨
    d = 2 * p ∨ d = -(2 * (p : ℤ)) := by
  have h4 := FamilyPrimeRank.dvd_two_mul_prime (Fact.out : p.Prime) hdvd
  have habs := Int.natAbs_eq d
  rcases h4 with h | h | h | h <;> omega

private lemma val2_p (hp2' : p ≠ 2) : padicValRat 2 (((p : ℕ) : ℚ)) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2'
    · exact h
  have hnd : ¬ (2 : ℤ) ∣ ((p : ℕ) : ℤ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
    omega
  have := int_val_zero (p := 2) hnd
  push_cast at this ⊢
  exact this

private lemma val2_two : padicValRat 2 ((2 : ℚ)) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := padicValRat.self (p := 2) (by norm_num)
  push_cast at this ⊢
  exact this

/-- The master pin: the sign and the two valuation parities of a member read the
sign and the two prime supports of its rung. -/
private lemma master_pin (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ)) :
    (0 < z → 0 < d) ∧ (z < 0 → d < 0) ∧
    (Even (padicValRat p z) → ¬ (p : ℤ) ∣ d) ∧
    (Odd (padicValRat p z) → (p : ℤ) ∣ d) ∧
    (Even (padicValRat 2 z) → ¬ (2 : ℤ) ∣ d) ∧
    (Odd (padicValRat 2 z) → (2 : ℤ) ∣ d) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := by
    have := hp.two_le
    omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2'
    · exact h
  obtain ⟨ep, hep⟩ := sqcls_val_parity (p := p) hz0 hd0 hsq
  obtain ⟨e2, he2⟩ := sqcls_val_parity (p := 2) hz0 hd0 hsq
  -- the two-adic valuation of a rung tracks two-divisibility
  have hv2d : ((2 : ℤ) ∣ d ∧ padicValRat 2 ((d : ℤ) : ℚ) = 1) ∨
      (¬ (2 : ℤ) ∣ d ∧ padicValRat 2 ((d : ℤ) : ℚ) = 0) := by
    rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · right
      exact ⟨by norm_num, by
        have := int_val_zero (p := 2) (show ¬ (2:ℤ) ∣ 1 from by norm_num)
        push_cast at this ⊢
        exact this⟩
    · right
      exact ⟨by norm_num, by
        have := int_val_zero (p := 2) (show ¬ (2:ℤ) ∣ -1 from by norm_num)
        push_cast at this ⊢
        exact this⟩
    · left
      exact ⟨⟨1, by ring⟩, by push_cast; exact val2_two⟩
    · left
      refine ⟨⟨-1, by ring⟩, ?_⟩
      have h1 : ((( -2 : ℤ)) : ℚ) = -(2 : ℚ) := by push_cast; ring
      rw [h1, padicValRat.neg]
      exact val2_two
    · right
      refine ⟨?_, by push_cast; exact val2_p hp2'⟩
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
      omega
    · right
      refine ⟨?_, ?_⟩
      · rw [Int.dvd_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
          Int.natCast_dvd_natCast]
        omega
      · have h1 : (((-(p : ℤ)) : ℤ) : ℚ) = -(((p : ℕ) : ℚ)) := by push_cast; ring
        rw [h1, padicValRat.neg]
        exact val2_p hp2'
    · left
      refine ⟨⟨(p : ℤ), by ring⟩, ?_⟩
      have h1 : (((2 * (p : ℤ)) : ℤ) : ℚ) = (2 : ℚ) * (((p : ℕ) : ℚ)) := by
        push_cast; ring
      rw [h1, padicValRat.mul (by norm_num) (by exact_mod_cast hp.pos.ne'),
        val2_two, val2_p hp2']
      ring
    · left
      refine ⟨⟨-(p : ℤ), by ring⟩, ?_⟩
      have h1 : (((-(2 * (p : ℤ))) : ℤ) : ℚ) = -((2 : ℚ) * (((p : ℕ) : ℚ))) := by
        push_cast; ring
      rw [h1, padicValRat.neg,
        padicValRat.mul (by norm_num) (by exact_mod_cast hp.pos.ne'),
        val2_two, val2_p hp2']
      ring
  -- the `p`-adic valuation of a rung tracks `p`-divisibility
  have hvpd : ((p : ℤ) ∣ d ∧ padicValRat p ((d : ℤ) : ℚ) = 1) ∨
      (¬ (p : ℤ) ∣ d ∧ padicValRat p ((d : ℤ) : ℚ) = 0) := by
    rcases rung_split (by omega) hd0 hdvd with ⟨hf, hv⟩ | ⟨hdv, -, -, -, -, -, hv⟩
    · exact Or.inr ⟨hf, hv⟩
    · exact Or.inl ⟨hdv, hv⟩
  refine ⟨fun hz => sqcls_sign hsq hz, fun hz => ?_, fun he => ?_, fun ho => ?_,
    fun he => ?_, fun ho => ?_⟩
  · by_contra hdpos
    push_neg at hdpos
    have hd' : 0 < d := lt_of_le_of_ne hdpos (Ne.symm hd0)
    obtain ⟨c, hc, hv⟩ := hsq
    have : 0 < z := by
      rw [hv]
      have h1 : (0 : ℚ) < ((d : ℤ) : ℚ) := by exact_mod_cast hd'
      positivity
    linarith
  · rcases hvpd with ⟨hdv, hv⟩ | ⟨hf, hv⟩
    · rw [hv] at hep
      obtain ⟨w, hw⟩ := he
      omega
    · exact hf
  · rcases hvpd with ⟨hdv, hv⟩ | ⟨hf, hv⟩
    · exact hdv
    · rw [hv] at hep
      obtain ⟨w, hw⟩ := ho
      omega
  · rcases hv2d with ⟨hdv, hv⟩ | ⟨hf, hv⟩
    · rw [hv] at he2
      obtain ⟨w, hw⟩ := he
      omega
    · exact hf
  · rcases hv2d with ⟨hdv, hv⟩ | ⟨hf, hv⟩
    · exact hdv
    · rw [hv] at he2
      obtain ⟨w, hw⟩ := ho
      omega


/-! ## 4. The six torsion pins -/

private lemma vp_neg_psq :
    padicValRat p (-(((p : ℕ) : ℚ)) ^ 2) = 2 := by
  have hp : p.Prime := Fact.out
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [show (-(((p : ℕ) : ℚ)) ^ 2) = -((((p : ℕ) : ℚ)) ^ 2) from by ring,
    padicValRat.neg, padicValRat.pow hpq0, val_p hp]
  ring

private lemma v2_neg_psq (hp2' : p ≠ 2) :
    padicValRat 2 (-(((p : ℕ) : ℚ)) ^ 2) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [show (-(((p : ℕ) : ℚ)) ^ 2) = -((((p : ℕ) : ℚ)) ^ 2) from by ring,
    padicValRat.neg, padicValRat.pow hpq0, val2_p hp2']
  ring

private lemma vp_two_psq (hp2' : p ≠ 2) :
    padicValRat p ((2 : ℚ) * (((p : ℕ) : ℚ)) ^ 2) = 2 := by
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := by have := hp.two_le; omega
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hv2 : padicValRat p ((2 : ℚ)) = 0 := by
    have hnd : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    have := int_val_zero (p := p) hnd
    push_cast at this ⊢
    exact this
  rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hpq0), hv2,
    padicValRat.pow hpq0, val_p hp]
  ring

private lemma v2_two_psq (hp2' : p ≠ 2) :
    padicValRat 2 ((2 : ℚ) * (((p : ℕ) : ℚ)) ^ 2) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hpq0), val2_two,
    padicValRat.pow hpq0, val2_p hp2']
  ring

private lemma vp_neg_p : padicValRat p (-((p : ℕ) : ℚ)) = 1 := by
  have hp : p.Prime := Fact.out
  rw [padicValRat.neg, val_p hp]

private lemma v2_neg_p (hp2' : p ≠ 2) : padicValRat 2 (-((p : ℕ) : ℚ)) = 0 := by
  rw [padicValRat.neg, val2_p hp2']

private lemma vp_neg_2p (hp2' : p ≠ 2) :
    padicValRat p (-((2 : ℚ) * ((p : ℕ) : ℚ))) = 1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := by have := hp.two_le; omega
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hv2 : padicValRat p ((2 : ℚ)) = 0 := by
    have hnd : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    have := int_val_zero (p := p) hnd
    push_cast at this ⊢
    exact this
  rw [padicValRat.neg, padicValRat.mul (by norm_num) hpq0, hv2, val_p hp]
  ring

private lemma v2_neg_2p (hp2' : p ≠ 2) :
    padicValRat 2 (-((2 : ℚ) * ((p : ℕ) : ℚ))) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [padicValRat.neg, padicValRat.mul (by norm_num) hpq0, val2_two, val2_p hp2']
  ring

/-- Shared kill-kit for the pins. -/
private lemma pin_facts (hp2' : p ≠ 2) :
    ¬ (p : ℤ) ∣ (1 : ℤ) ∧ ¬ (p : ℤ) ∣ (2 : ℤ) ∧ (0 : ℤ) < (p : ℤ) ∧ p % 2 = 1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := by have := hp.two_le; omega
  refine ⟨fun h => ?_, fun h => ?_, by exact_mod_cast hp.pos, ?_⟩
  · have := Int.le_of_dvd (by norm_num) h
    omega
  · have := Int.le_of_dvd (by norm_num) h
    omega
  · rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2'
    · exact h

private lemma pin_one' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzpos : 0 < z) (hvpe : Even (padicValRat p z)) (hv2e : Even (padicValRat 2 z)) :
    d = 1 := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨hpos, -, hevp, -, hev2, -⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdpos := hpos hzpos
  have hnp := hevp hvpe
  have hn2 := hev2 hv2e
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · omega
  · exact absurd ⟨1, by ring⟩ hn2
  · omega
  · exact absurd (dvd_refl _) hnp
  · omega
  · exact absurd ⟨2, by ring⟩ hnp
  · omega

private lemma pin_neg_one' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzneg : z < 0) (hvpe : Even (padicValRat p z)) (hv2e : Even (padicValRat 2 z)) :
    d = -1 := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨-, hneg, hevp, -, hev2, -⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdneg := hneg hzneg
  have hnp := hevp hvpe
  have hn2 := hev2 hv2e
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · rfl
  · omega
  · exact absurd ⟨-1, by ring⟩ hn2
  · omega
  · exact absurd (dvd_neg.mpr (dvd_refl _)) hnp
  · omega
  · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hnp

private lemma pin_p' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzpos : 0 < z) (hvpo : Odd (padicValRat p z)) (hv2e : Even (padicValRat 2 z)) :
    d = (p : ℤ) := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨hpos, -, -, hodp, hev2, -⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdpos := hpos hzpos
  have hpd := hodp hvpo
  have hn2 := hev2 hv2e
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpd hdp1
  · omega
  · exact absurd hpd hdp2
  · omega
  · rfl
  · omega
  · exact absurd ⟨(p : ℤ), by ring⟩ hn2
  · omega

private lemma pin_neg_p' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzneg : z < 0) (hvpo : Odd (padicValRat p z)) (hv2e : Even (padicValRat 2 z)) :
    d = -(p : ℤ) := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨-, hneg, -, hodp, hev2, -⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdneg := hneg hzneg
  have hpd := hodp hvpo
  have hn2 := hev2 hv2e
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact absurd (Int.dvd_neg.mp hpd) hdp1
  · omega
  · exact absurd (Int.dvd_neg.mp hpd) hdp2
  · omega
  · rfl
  · omega
  · exact absurd ⟨-(p : ℤ), by ring⟩ hn2

private lemma pin_two' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzpos : 0 < z) (hvpe : Even (padicValRat p z)) (hv2o : Odd (padicValRat 2 z)) :
    d = 2 := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨hpos, -, hevp, -, -, hod2⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdpos := hpos hzpos
  have hnp := hevp hvpe
  have h2d := hod2 hv2o
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨c, hc⟩ := h2d
    omega
  · omega
  · rfl
  · omega
  · obtain ⟨c, hc⟩ := h2d
    omega
  · omega
  · exact absurd ⟨2, by ring⟩ hnp
  · omega

private lemma pin_neg_2p' (hp2' : p ≠ 2) {z : ℚ} {d : ℤ} (hz0 : z ≠ 0) (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hsq : Descent.SqCls z ((d : ℤ) : ℚ))
    (hzneg : z < 0) (hvpo : Odd (padicValRat p z)) (hv2o : Odd (padicValRat 2 z)) :
    d = -(2 * (p : ℤ)) := by
  obtain ⟨hdp1, hdp2, hpp, hpodd⟩ := pin_facts hp2'
  have hp3 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨-, hneg, -, hodp, -, hod2⟩ := master_pin hp2' hz0 hd0 hdvd hsq
  have hdneg := hneg hzneg
  have hpd := hodp hvpo
  have h2d := hod2 hv2o
  rcases rung_cases hp3 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact absurd (Int.dvd_neg.mp hpd) hdp1
  · omega
  · exact absurd (Int.dvd_neg.mp hpd) hdp2
  · omega
  · obtain ⟨c, hc⟩ := h2d
    omega
  · omega
  · rfl


/-! ## 5. The eight cells and the collision -/

/-- The eight admitted cells at `p ≡ 5 (mod 8)`. -/
def cells5 (p : ℕ) : Finset (ℤ × ℤ) :=
  {((1 : ℤ), (1 : ℤ)), ((-1 : ℤ), (-1 : ℤ)), ((1 : ℤ), (p : ℤ)),
   ((-1 : ℤ), -(p : ℤ)), ((p : ℤ), (2 : ℤ)), (-(p : ℤ), (-2 : ℤ)),
   ((p : ℤ), 2 * (p : ℤ)), (-(p : ℤ), -2 * (p : ℤ))}

lemma cells5_card_le (p : ℕ) : (cells5 p).card ≤ 8 := by
  unfold cells5
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  exact Finset.card_singleton _ |>.le

/-- **Every point lands in the eight cells**: the collapse places the moving
points, and the six pins place the torsion. -/
lemma classOf_mem_cells5 (hp2' : p ≠ 2) (hp8 : p % 8 = 5)
    (P : (FamilyFace.E (((p : ℕ) : ℚ))).Point) :
    FamilyCollision.classOf (Fact.out : p.Prime).pos P ∈ cells5 p := by
  have hp : p.Prime := Fact.out
  have hn : 0 < p := hp.pos
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hpqpos : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  obtain ⟨h10, h20, h1d, h2d, hsq1, hsq2⟩ := FamilyCollision.classOf_spec hn P
  set d₁ := (FamilyCollision.classOf hn P).1 with hd₁def
  set d₂ := (FamilyCollision.classOf hn P).2 with hd₂def
  simp only [cells5, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rcases P with _ | @⟨x, y, hns⟩
  · -- the zero point: both slots read `1`
    have hs1 : slotOneAt (((p : ℕ) : ℚ)) 0 = 1 := rfl
    have hs2 : slotTwoAt (((p : ℕ) : ℚ)) 0 = 1 := rfl
    rw [← Point.zero_def] at hsq1 hsq2
    rw [hs1] at hsq1
    rw [hs2] at hsq2
    left
    rw [Prod.ext_iff]
    constructor
    · exact pin_one' hp2' one_ne_zero h10 h1d hsq1 one_pos
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
    · exact pin_one' hp2' one_ne_zero h20 h2d hsq2 one_pos
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
  · by_cases hy : y = 0
    · -- torsion abscissae: `x ∈ {0, p, −p}`
      have hcurve := onCurveAt hns
      rw [hy] at hcurve
      have hroots : x * (x - ((p : ℕ) : ℚ)) * (x + ((p : ℕ) : ℚ)) = 0 := by
        have : (0 : ℚ) ^ 2 = 0 := by norm_num
        nlinarith [hcurve]
      rcases mul_eq_zero.mp hroots with hxa | hxp
      rcases mul_eq_zero.mp hxa with hx0 | hxm
      · -- x = 0 : slots read (−p², −p)
        rw [slotOneAt_some, if_pos hx0] at hsq1
        rw [slotTwoAt_some, if_neg (by rw [hx0]; exact fun hc => hpq0 hc.symm)] at hsq2
        have hs2v : x - ((p : ℕ) : ℚ) = -((p : ℕ) : ℚ) := by rw [hx0]; ring
        rw [hs2v] at hsq2
        right; right; right; left
        rw [Prod.ext_iff]
        constructor
        · exact pin_neg_one' hp2' (neg_ne_zero.mpr (pow_ne_zero 2 hpq0)) h10 h1d hsq1
            (neg_lt_zero.mpr (by positivity)) (by rw [vp_neg_psq]; exact ⟨1, by ring⟩)
            (by rw [v2_neg_psq hp2']; exact ⟨0, by ring⟩)
        · exact pin_neg_p' hp2' (neg_ne_zero.mpr hpq0) h20 h2d hsq2
            (neg_lt_zero.mpr hpqpos) (by rw [vp_neg_p]; exact ⟨0, by ring⟩)
            (by rw [v2_neg_p hp2']; exact ⟨0, by ring⟩)
      · -- x = p : slots read (p, 2p²)
        have hxp' : x = ((p : ℕ) : ℚ) := by linarith [sub_eq_zero.mp hxm]
        rw [slotOneAt_some, if_neg (by rw [hxp']; exact hpq0)] at hsq1
        rw [slotTwoAt_some, if_pos hxp'] at hsq2
        rw [hxp'] at hsq1
        right; right; right; right; left
        rw [Prod.ext_iff]
        constructor
        · exact pin_p' hp2' hpq0 h10 h1d hsq1 hpqpos
            (by rw [val_p hp]; exact ⟨0, by ring⟩)
            (by rw [val2_p hp2']; exact ⟨0, by ring⟩)
        · exact pin_two' hp2' (by positivity) h20 h2d hsq2 (by positivity)
            (by rw [vp_two_psq hp2']; exact ⟨1, by ring⟩)
            (by rw [v2_two_psq hp2']; exact ⟨0, by ring⟩)
      · -- x = −p : slots read (−p, −2p)
        have hxm' : x = -((p : ℕ) : ℚ) := by linarith [eq_neg_of_add_eq_zero_left hxp]
        rw [slotOneAt_some, if_neg (by rw [hxm']; exact neg_ne_zero.mpr hpq0)] at hsq1
        rw [slotTwoAt_some, if_neg (by rw [hxm']; intro hc; apply hpq0; linarith)] at hsq2
        rw [hxm'] at hsq1
        have hs2v : x - ((p : ℕ) : ℚ) = -((2 : ℚ) * ((p : ℕ) : ℚ)) := by
          rw [hxm']; ring
        rw [hs2v] at hsq2
        right; right; right; right; right; right; right
        rw [Prod.ext_iff]
        constructor
        · exact pin_neg_p' hp2' (neg_ne_zero.mpr hpq0) h10 h1d hsq1
            (neg_lt_zero.mpr hpqpos) (by rw [vp_neg_p]; exact ⟨0, by ring⟩)
            (by rw [v2_neg_p hp2']; exact ⟨0, by ring⟩)
        · have h := pin_neg_2p' hp2' (neg_ne_zero.mpr (by positivity)) h20 h2d hsq2
            (neg_lt_zero.mpr (by positivity)) (by rw [vp_neg_2p hp2']; exact ⟨0, by ring⟩)
            (by rw [v2_neg_2p hp2']; exact ⟨0, by ring⟩)
          exact h.trans (by ring)
    · -- moving points: the collapse
      have hcurve := onCurveAt hns
      rw [slotOneAt_some] at hsq1
      rw [slotTwoAt_some] at hsq2
      obtain ⟨hx0, hxn, -⟩ :=
        FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
      rw [if_neg hx0] at hsq1
      rw [if_neg hxn] at hsq2
      rcases theSlotClassesCollapseOnTheFiveModEightBranch hp8 hcurve hy
          h10 h20 h1d h2d hsq1 hsq2 with
        ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
          ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)
      · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))
      · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))

/-- **THE CLASSES COLLIDE ON THE FIVE-MOD-EIGHT BRANCH**: any family of more than
`8` points contains two whose difference is a double. -/
theorem theClassesCollideOnTheFiveModEightBranch (hp8 : p % 8 = 5) {α : Type}
    [Fintype α] (hcard : 8 < Fintype.card α)
    (f : α → (FamilyFace.E (((p : ℕ) : ℚ))).Point) :
    ∃ a b, a ≠ b ∧ ∃ Q : (FamilyFace.E (((p : ℕ) : ℚ))).Point, f a - f b = Q + Q := by
  have hp : p.Prime := Fact.out
  have hp2' : p ≠ 2 := by intro h; omega
  have hn : 0 < p := hp.pos
  have hmaps : ∀ a : α, FamilyCollision.classOf hn (f a) ∈ cells5 p := fun a =>
    classOf_mem_cells5 hp2' hp8 (f a)
  have hlt : (cells5 p).card < Fintype.card α :=
    lt_of_le_of_lt (cells5_card_le p) hcard
  obtain ⟨a, -, b, -, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.univ) (t := cells5 p)
      (by rw [Finset.card_univ]; exact hlt) fun a _ => hmaps a
  exact ⟨a, b, hab, FamilyCollision.sameClass_double hn (f a) (f b) hfab⟩


/-! ## 6. The rank is at most one -/

set_option maxHeartbeats 2000000 in
/-- **THE ALGEBRAIC RANK IS BOUNDED ON THE FIVE-MOD-EIGHT BRANCH**: whenever
`8 < 3·2^r`, no `r` points are independent modulo torsion. -/
theorem theAlgebraicRankIsBoundedOnTheFiveModEightBranch (r : ℕ)
    (hp8 : p % 8 = 5) (hr : 8 < 3 * 2 ^ r) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p r := by
  have hnp : p.Prime := Fact.out
  have hn : 0 < p := hnp.pos
  intro hR
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  obtain ⟨Pts, hind⟩ := hR
  have hnq : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hn
  haveI : AddGroup.FG ((FamilyFace.E (((p : ℕ) : ℚ))).Point) :=
    FamilyMordell.theMordellWeilTheoremAtEveryModulus p hn
  obtain ⟨m, ι, hι, qq, hqq, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((FamilyFace.E (((p : ℕ) : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (qq i ^ e i) := fun i => ⟨pow_ne_zero _ (hqq i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (qq i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (FamilyFace.E (((p : ℕ) : ℚ))).Point, (F X).1 = 0 →
      ∃ k : ℕ, 0 < k ∧ k • X = 0 := by
    intro X hX
    refine ⟨Nat.card (⨁ i, ZMod (qq i ^ e i)), Nat.card_pos, ?_⟩
    apply F.injective
    rw [map_nsmul, map_zero]
    have h2 : (Nat.card (⨁ i, ZMod (qq i ^ e i))) • F X
        = ((Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).1,
           (Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).2) := rfl
    rw [h2, hX, smul_zero, card_nsmul_eq_zero']
    rfl
  -- the free parts are independent, so the free rank dominates `r`
  set v : Fin r → (Fin m →₀ ℤ) := fun i => (F (Pts i)).1 with hv
  have hindZ : ∀ c : Fin r → ℤ, (∑ i, c i • v i) = 0 → ∀ i, c i = 0 := by
    intro c hczero i
    refine hind c ?_ i
    apply htor
    have hmap : F (∑ i, c i • Pts i) = ∑ i, c i • F (Pts i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]
    have h1 : (F (∑ i, c i • Pts i)).1 = ∑ i, c i • v i := by
      rw [hmap]
      have h2 := map_sum (AddMonoidHom.fst (Fin m →₀ ℤ) (⨁ i, ZMod (qq i ^ e i)))
        (fun i => c i • F (Pts i)) Finset.univ
      calc (∑ i, c i • F (Pts i)).1
          = ∑ i, (c i • F (Pts i)).1 := h2
        _ = ∑ i, c i • v i :=
            Finset.sum_congr rfl fun j _ => by rw [Prod.smul_fst]
    rw [h1, hczero]
  set castHom : (Fin m →₀ ℤ) →+ (Fin m →₀ ℚ) :=
    Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ) with hcastHom
  have hcastInj : Function.Injective castHom := by
    intro g h hgh
    ext j
    have h1 := DFunLike.congr_fun hgh j
    rw [hcastHom] at h1
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
      Int.coe_castAddHom] at h1
    exact_mod_cast h1
  set w : Fin r → (Fin m →₀ ℚ) := fun i => castHom (v i) with hw
  have hindW : LinearIndependent ℚ w := by
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    refine hindZ c ?_ i
    apply hcastInj
    rw [map_sum, map_zero]
    have hterm : ∀ j : Fin r, castHom (c j • v j) = c j • w j := by
      intro j
      rw [map_zsmul, hw]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact hc
  have hrm : r ≤ m := by
    have h1 := hindW.fintype_card_le_finrank
    rw [Module.finrank_finsupp_self] at h1
    simpa using h1
  -- the torsion trio and its free-part vanishing
  have h00 : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular 0 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp [FamilyFace.E]
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  have hn0 : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular (((p : ℕ) : ℚ)) 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp only [FamilyFace.E]
      ring
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  set T : Fin 3 → (FamilyFace.E (((p : ℕ) : ℚ))).Point :=
    ![0, Point.some h00, Point.some hn0] with hT
  have hT0 : T 0 = 0 := rfl
  have hT1 : T 1 = Point.some h00 := rfl
  have hT2 : T 2 = Point.some hn0 := rfl
  have htrio2 : ∀ b : Fin 3, T b + T b = 0 := by
    intro b
    rcases FamilyRankFin3.fin3_cases b with rfl | rfl | rfl
    · rw [hT0, add_zero]
    · rw [hT1]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
    · rw [hT2]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
  have hfree : ∀ b : Fin 3, (F (T b)).1 = 0 := by
    intro b
    have h2 : F (T b) + F (T b) = 0 := by
      rw [← map_add, htrio2 b, map_zero]
    have h3 : (F (T b)).1 + (F (T b)).1 = 0 := by
      have h4 := congrArg Prod.fst h2
      simpa using h4
    ext j
    have h5 := DFunLike.congr_fun h3 j
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
    omega
  set tt : Fin 3 → (⨁ i, ZMod (qq i ^ e i)) := fun b => (F (T b)).2 with htt
  have hFT : ∀ b : Fin 3, F (T b) = (0, tt b) := fun b =>
    Prod.ext_iff.mpr ⟨hfree b, rfl⟩
  -- the sign-vector free parts
  set wv : (Fin r → Bool) → (Fin m →₀ ℤ) := fun ε =>
    ∑ i : Fin r, if ε i then Finsupp.single (Fin.castLE hrm i) (1 : ℤ) else 0
    with hwv
  have hwv_apply : ∀ (ε : Fin r → Bool) (i : Fin r),
      wv ε (Fin.castLE hrm i) = if ε i then 1 else 0 := by
    intro ε i
    rw [hwv]
    simp only
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hb : ε i
      · rw [if_pos hb, if_pos hb, Finsupp.single_eq_same]
      · rw [if_neg hb, if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro j _ hji
      by_cases hb : ε j
      · rw [if_pos hb]
        exact Finsupp.single_eq_of_ne
          (fun hc => hji (Fin.castLE_injective hrm hc).symm)
      · rw [if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  -- the colliding family of `3·2^r` points
  obtain ⟨x, x', hnexx, Q, hQ⟩ :=
    theClassesCollideOnTheFiveModEightBranch hp8
      (α := (Fin r → Bool) × Fin 3)
      (by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
          Fintype.card_bool]
        omega)
      (fun ab => F.symm (wv ab.1, tt ab.2))
  obtain ⟨ε, b⟩ := x
  obtain ⟨δ, b'⟩ := x'
  dsimp only at hQ
  have himg : ((wv ε, tt b) : (Fin m →₀ ℤ) × (⨁ i, ZMod (qq i ^ e i)))
      - (wv δ, tt b') = F Q + F Q := by
    have h1 := congrArg F hQ
    rwa [map_sub, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  have hfst : wv ε - wv δ = (F Q).1 + (F Q).1 := by
    have h2 := congrArg Prod.fst himg
    simpa using h2
  by_cases hεδ : ε = δ
  · -- same signs: the torsion trio collides — refused
    subst hεδ
    have hbb : b ≠ b' := by
      intro h
      exact hnexx (by rw [h])
    have hFb : F (T b) = (0, tt b) := hFT b
    have hFb' : F (T b') = (0, tt b') := hFT b'
    have htdiff : T b - T b' = F.symm (0, (F Q).2) + F.symm (0, (F Q).2) := by
      have hsnd : tt b - tt b' = (F Q).2 + (F Q).2 := by
        have h2 := congrArg Prod.snd himg
        simpa using h2
      apply F.injective
      rw [map_sub, map_add, AddEquiv.apply_symm_apply, hFb, hFb',
        Prod.mk_sub_mk, Prod.mk_add_mk]
      exact Prod.ext_iff.mpr ⟨by simp, hsnd⟩
    exact FamilyCollision.theTorsionTrioDoesNotCollideAtEveryModulus hn T hT0 hT1
      hT2 b b' hbb (F.symm (0, (F Q).2)) htdiff
  · -- different signs: parity at the first differing coordinate refuses the double
    have hex : ∃ i : Fin r, ε i ≠ δ i := by
      by_contra hall
      push_neg at hall
      exact hεδ (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hev := DFunLike.congr_fun hfst (Fin.castLE hrm i₀)
    rw [Finsupp.sub_apply, Finsupp.add_apply, hwv_apply, hwv_apply] at hev
    rcases Bool.eq_false_or_eq_true (ε i₀) with hε | hε <;>
      rcases Bool.eq_false_or_eq_true (δ i₀) with hδ | hδ
    · exact hi₀ (hε.trans hδ.symm)
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · exact hi₀ (hε.trans hδ.symm)

/-- **THE RANK IS AT MOST ONE AT EVERY PRIME `p ≡ 5 (mod 8)`**: no two points of
`y² = x³ − p²x` are independent modulo torsion — the eight-cell collapse forces
`3·2^r ≤ 8`, so `r ≤ 1`.  Against the standing central vanishing
(`theAnalyticRankIsPositiveOnTheFiveModEightBranch`), the conjecture's prediction
of rank exactly one is squeezed to within a single point on this branch. -/
theorem theRankIsAtMostOneAtEveryFiveModEightPrime (hp8 : p % 8 = 5) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p 2 :=
  theAlgebraicRankIsBoundedOnTheFiveModEightBranch 2 hp8 (by norm_num)

end Soma.Holonics.Millennium.FamilyFiveDescent
