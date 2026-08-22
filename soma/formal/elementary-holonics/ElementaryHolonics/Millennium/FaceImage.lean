import ElementaryHolonics.Millennium.FamilyFace
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# FaceImage: the two-descent of the thirty-four twist is complete

**Rank exactly two, in descent form.**  On `y² = x³ − 34²x` the descent face
`P ↦ (x, x − 34)` mod squares is a homomorphism (`FamilyFace.lean`), and this file
computes its image **exactly**: the image is the sixteen-element group realized by the
half-turns and the two directions, no more and no less.

* **The support law** (`theSlotClassesAreSupportedOnTheDiscriminant`): every slot class
  of every point is `±2^a·17^b` mod squares — proved by the valuation-parity law: for a
  prime `ℓ ∉ {2, 17}`, the `ℓ`-adic valuation of each slot is even, because `ℓ` can
  divide at most one factor of `y² = x(x−34)(x+34)`.
* **The sign law** (`theSignsAgreeAcrossTheFace`): the two slot classes have equal
  signs, because the real curve with `y ≠ 0` lives on `x > 34` or `−34 < x < 0` —
  thirty-two of the sixty-four candidate classes die in the real frame.
* **The canonical refusal** (`theCanonicalCosetIsRefused`): no point has face
  `(1, 2)` — the class equations clear to `C² − 34D² = 2E²` and `C² + 34D² = 2F²`,
  which have no primitive solution mod eight (a kernel `decide`), and the halving
  descent kills the rest.  The other fifteen refused classes translate onto this one
  by adding a realized point and applying the homomorphism.
* **The image theorem** (`theFaceImageIsTheRealizedSixteen`): every point's face lies
  in the sixteen realized classes; with `theRealizedSixteenAreInTheImage` the image is
  exactly the realized group.

Classically — through the Mordell–Weil theorem, which is exterior to this tree — an
image of order sixteen with torsion image of order four says the rank of the
thirty-four twist is **at most two**, and the escape certificates of `FamilyFace.lean`
say it is **at least two**: rank exactly two.  That translation is interpretation; the
theorems here are the exact image computation.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the
Mordell–Weil finiteness that converts the image computation into the word "rank" is
classical and not claimed; the torsion classification at thirty-four remains owed;
nothing about the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.FaceImage

open WeierstrassCurve.Affine

/-! ## 1. Square-class helpers -/

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_symm {a b : ℚ} (h : Descent.SqCls a b) : Descent.SqCls b a := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hval]
  field_simp

private lemma sqcls_mul {a b c d : ℚ} (h₁ : Descent.SqCls a c) (h₂ : Descent.SqCls b d) :
    Descent.SqCls (a * b) (c * d) := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_sign {a d : ℚ} (h : Descent.SqCls a d) : (0 < a ↔ 0 < d) := by
  obtain ⟨c, hc, hval⟩ := h
  have hc2 : 0 < c ^ 2 := by positivity
  constructor
  · intro ha
    nlinarith
  · intro hd
    nlinarith

/-! ## 2. The curve data at thirty-four -/

private lemma onCurve34 {x y : ℚ} (h : (FamilyFace.E 34).Nonsingular x y) :
    y ^ 2 = x ^ 3 - 1156 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

private lemma avoid34 {x y : ℚ} (h : y ^ 2 = x ^ 3 - 1156 * x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ 34 ∧ x ≠ -34 :=
  FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots
    (n := 34) (by linear_combination h) hy

private lemma slot34One_some {x y : ℚ} (h : (FamilyFace.E 34).Nonsingular x y) :
    FamilyFace.slotOne 34 (.some h) = if x = 0 then -34 ^ 2 else x := rfl

private lemma slot34Two_some {x y : ℚ} (h : (FamilyFace.E 34).Nonsingular x y) :
    FamilyFace.slotTwo 34 (.some h) = if x = 34 then 2 * 34 ^ 2 else x - 34 := rfl

/-! ## 3. The sign law: thirty-two classes die in the real frame -/

/-- **The signs agree across the face**: for a point off the two-torsion, the two slot
classes carry one sign — the real curve with `y ≠ 0` lives on `x > 34` (both positive)
or `−34 < x < 0` (both negative). -/
theorem theSignsAgreeAcrossTheFace {x y d₁ d₂ : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - 1156 * x) (hy : y ≠ 0)
    (h₁ : Descent.SqCls x d₁) (h₂ : Descent.SqCls (x - 34) d₂) :
    (0 < d₁ ∧ 0 < d₂) ∨ (d₁ < 0 ∧ d₂ < 0) := by
  obtain ⟨hx0, hx34, hxm34⟩ := avoid34 hcurve hy
  have hy2 : 0 < y ^ 2 := by positivity
  have hs₁ := sqcls_sign h₁
  have hs₂ := sqcls_sign h₂
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · -- x < 0: the egg; x − 34 < 0, and x + 34 > 0 is forced by the curve
    right
    constructor
    · by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hd | hd
      · exact absurd (hs₁.mpr hd) (by linarith)
      · obtain ⟨c, hc, hval⟩ := h₁
        rw [← hd] at hval
        exact hx0 (by linarith [hval])
    · by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hd | hd
      · exact absurd (hs₂.mpr hd) (by linarith)
      · obtain ⟨c, hc, hval⟩ := h₂
        rw [← hd] at hval
        exact hx34 (by linarith [hval])
  · -- x > 0: the branch; the curve forces x > 34
    left
    have hx34' : 34 < x := by
      by_contra hcon
      push_neg at hcon
      have hlt : x < 34 := lt_of_le_of_ne hcon hx34
      have hx2 : x ^ 2 < 1156 := by nlinarith
      have hpos : 0 < x * (1156 - x ^ 2) := mul_pos hx (by linarith)
      nlinarith [hy2]
    exact ⟨hs₁.mp hx, hs₂.mp (by linarith)⟩

/-! ## 4. The valuation-parity law: a distant prime sees an even valuation -/

private lemma val_add_left {ℓ : ℕ} [Fact ℓ.Prime] {a b : ℚ} (ha : a ≠ 0)
    (hab : a + b ≠ 0) (h : padicValRat ℓ a < padicValRat ℓ b) :
    padicValRat ℓ (a + b) = padicValRat ℓ a := by
  have h1 : padicValRat ℓ a ≤ padicValRat ℓ (a + b) := by
    have hmin := padicValRat.min_le_padicValRat_add (p := ℓ) (q := a) (r := b) hab
    omega
  have h2 : padicValRat ℓ (a + b) ≤ padicValRat ℓ a := by
    by_contra hcon
    push_neg at hcon
    have hrw : a + b + -b = a := by ring
    have hmin := padicValRat.min_le_padicValRat_add (p := ℓ) (q := a + b) (r := -b)
      (by rw [hrw]; exact ha)
    rw [hrw, padicValRat.neg] at hmin
    omega
  omega

private lemma prime_not_dvd_68 {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (h17 : ℓ ≠ 17) :
    ¬ ℓ ∣ 68 := by
  intro hc
  have h4 : ℓ ∣ 4 * 17 := by simpa using hc
  rcases (Nat.Prime.dvd_mul hℓ).mp h4 with h | h
  · have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow (n := 2) (by simpa using h)
    exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  · exact h17 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h)

private lemma val_const_zero {ℓ : ℕ} [hf : Fact ℓ.Prime] (h2 : ℓ ≠ 2) (h17 : ℓ ≠ 17) :
    padicValRat ℓ (34 : ℚ) = 0 ∧ padicValRat ℓ (-34 : ℚ) = 0 ∧
    padicValRat ℓ (68 : ℚ) = 0 := by
  have hℓ : ℓ.Prime := hf.out
  have key : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → padicValRat ℓ (m : ℚ) = 0 := by
    intro m hdvd
    rw [padicValRat.of_int, padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hdvd))]
    simp
  have hnd : ∀ m : ℤ, m.natAbs ∣ 68 → m ≠ 0 → ¬ (ℓ : ℤ) ∣ m := by
    intro m hm hm0 hc
    refine prime_not_dvd_68 hℓ h2 h17 (dvd_trans ?_ hm)
    simpa using Int.natAbs_dvd_natAbs.mpr hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using key 34 (hnd 34 (by norm_num) (by norm_num))
  · simpa using key (-34) (hnd (-34) (by norm_num) (by norm_num))
  · simpa using key 68 (hnd 68 (by norm_num) (by norm_num))

private lemma even_slot_val {ℓ : ℕ} [Fact ℓ.Prime] (h2 : ℓ ≠ 2) (h17 : ℓ ≠ 17)
    {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 1156 * x) (hy : y ≠ 0) :
    Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - 34)) := by
  obtain ⟨hx0, hx34, hxm34⟩ := avoid34 hcurve hy
  have hxm : x - 34 ≠ 0 := sub_ne_zero.mpr hx34
  have hxp : x + 34 ≠ 0 := fun hc => hxm34 (by linarith)
  have hfact : y ^ 2 = x * (x - 34) * (x + 34) := by linear_combination hcurve
  have hprod : 2 * padicValRat ℓ y =
      padicValRat ℓ x + padicValRat ℓ (x - 34) + padicValRat ℓ (x + 34) := by
    have hmul1 : padicValRat ℓ (x * (x - 34) * (x + 34)) =
        padicValRat ℓ x + padicValRat ℓ (x - 34) + padicValRat ℓ (x + 34) := by
      rw [padicValRat.mul (mul_ne_zero hx0 hxm) hxp, padicValRat.mul hx0 hxm]
    have hpow : padicValRat ℓ (y ^ 2) = 2 * padicValRat ℓ y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← hpow, hfact, hmul1]
  obtain ⟨v34, vm34, v68⟩ := val_const_zero (ℓ := ℓ) h2 h17
  constructor
  · -- the first slot
    rcases lt_trichotomy (padicValRat ℓ x) 0 with hv | hv | hv
    · -- deep: all three factors carry the same valuation
      have e1 : padicValRat ℓ (x - 34) = padicValRat ℓ x := by
        have := val_add_left hx0
          (by rw [show x + -34 = x - 34 by ring]; exact hxm) (by rw [vm34]; exact hv)
        rw [show x + -34 = x - 34 by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + 34) = padicValRat ℓ x := by
        have := val_add_left hx0 hxp (by rw [v34]; exact hv)
        exact this
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ x, by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · -- shallow: the shifted factors carry valuation zero
      have e1 : padicValRat ℓ (x - 34) = 0 := by
        have := val_add_left (by norm_num : (-34 : ℚ) ≠ 0)
          (by rw [show -34 + x = x - 34 by ring]; exact hxm) (by rw [vm34]; exact hv)
        rw [show (-34 : ℚ) + x = x - 34 by ring, vm34] at this
        exact this
      have e2 : padicValRat ℓ (x + 34) = 0 := by
        have := val_add_left (by norm_num : (34 : ℚ) ≠ 0)
          (by rw [show (34 : ℚ) + x = x + 34 by ring]; exact hxp) (by rw [v34]; exact hv)
        rw [show (34 : ℚ) + x = x + 34 by ring, v34] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩
  · -- the second slot
    rcases lt_trichotomy (padicValRat ℓ (x - 34)) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ x = padicValRat ℓ (x - 34) := by
        have := val_add_left hxm
          (by rw [show x - 34 + 34 = x by ring]; exact hx0) (by rw [v34]; exact hv)
        rw [show x - 34 + 34 = x by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + 34) = padicValRat ℓ (x - 34) := by
        have := val_add_left hxm
          (by rw [show x - 34 + 68 = x + 34 by ring]; exact hxp) (by rw [v68]; exact hv)
        rw [show x - 34 + 68 = x + 34 by ring] at this
        exact this
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ (x - 34), by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ x = 0 := by
        have := val_add_left (by norm_num : (34 : ℚ) ≠ 0)
          (by rw [show (34 : ℚ) + (x - 34) = x by ring]; exact hx0) (by rw [v34]; exact hv)
        rw [show (34 : ℚ) + (x - 34) = x by ring, v34] at this
        exact this
      have e2 : padicValRat ℓ (x + 34) = 0 := by
        have := val_add_left (by norm_num : (68 : ℚ) ≠ 0)
          (by rw [show (68 : ℚ) + (x - 34) = x + 34 by ring]; exact hxp)
          (by rw [v68]; exact hv)
        rw [show (68 : ℚ) + (x - 34) = x + 34 by ring, v68] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩

/-! ## 5. The bridge: even distant valuations put the class on the discriminant -/

/-- The eight candidate classes: `±1, ±2, ±17, ±34`. -/
def OnDiscriminant (d : ℚ) : Prop :=
  d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 17 ∨ d = -17 ∨ d = 34 ∨ d = -34

private lemma classFromEvenValuations {x : ℚ} (hx : x ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 17 → Even (padicValRat ℓ x)) :
    ∃ d : ℚ, OnDiscriminant d ∧ Descent.SqCls x d := by
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hdenQ : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hm0 : x.num * (x.den : ℤ) ≠ 0 := mul_ne_zero hnum hden
  -- the slot class is carried by the integer `num · den`
  have hcls : Descent.SqCls x ((x.num * (x.den : ℤ) : ℤ) : ℚ) := by
    refine ⟨1 / (x.den : ℚ), one_div_ne_zero hdenQ, ?_⟩
    have hxd : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
    push_cast
    field_simp
    linear_combination hxd
  -- the even valuations transfer to the integer carrier
  have hmv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 17 →
      Even ((x.num * (x.den : ℤ)).natAbs.factorization ℓ) := by
    intro ℓ hℓ h2 h17
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hval := h ℓ hℓ h2 h17
    have hunfold : padicValRat ℓ x =
        (padicValNat ℓ x.num.natAbs : ℤ) - padicValNat ℓ x.den := rfl
    rw [hunfold] at hval
    have habs : (x.num * (x.den : ℤ)).natAbs = x.num.natAbs * x.den := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [habs, Nat.factorization_def _ hℓ,
      padicValNat.mul (Int.natAbs_ne_zero.mpr hnum) x.den_nz]
    have h1 : Even ((padicValNat ℓ x.num.natAbs : ℤ) + padicValNat ℓ x.den) := by
      obtain ⟨k, hk⟩ := hval
      exact ⟨k + padicValNat ℓ x.den, by linarith⟩
    exact_mod_cast h1
  -- decompose the carrier into a square and a squarefree part
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree (x.num * (x.den : ℤ)).natAbs
  have hn0 : (x.num * (x.den : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  have ha0 : a ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hab
    exact hn0 hab.symm
  have hb0 : b ≠ 0 := by
    intro hc
    rw [hc] at hab
    simp at hab
    exact hn0 hab.symm
  -- the squarefree part is supported on {2, 17}
  have hadvd : a ∣ 34 := by
    rw [← Nat.factorization_le_iff_dvd ha0 (by norm_num)]
    rw [Finsupp.le_def]
    intro ℓ
    by_cases hℓp : ℓ.Prime
    · by_cases hdvd : ℓ ∣ a
      · have hle1 : a.factorization ℓ ≤ 1 :=
          (Nat.squarefree_iff_factorization_le_one ha0).mp hsq ℓ
        have hmem : ℓ = 2 ∨ ℓ = 17 := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨h2, h17⟩ := hcon
          have heven := hmv ℓ hℓp h2 h17
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul] at heven
          have hpos : 0 < a.factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp ha0 hdvd
          obtain ⟨k, hk⟩ := heven
          omega
        rcases hmem with rfl | rfl
        · have h2f : (34 : ℕ).factorization 2 = 1 := by
            rw [show (34 : ℕ) = 2 * 17 by norm_num,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.Prime.factorization_self (by norm_num),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
          rw [h2f]
          exact hle1
        · have h17f : (34 : ℕ).factorization 17 = 1 := by
            rw [show (34 : ℕ) = 2 * 17 by norm_num,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.factorization_eq_zero_of_not_dvd (by norm_num),
              Nat.Prime.factorization_self (by norm_num)]
          rw [h17f]
          exact hle1
      · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hℓp]
      exact Nat.zero_le _
  have hamem : a = 1 ∨ a = 2 ∨ a = 17 ∨ a = 34 := by
    have hle : a ≤ 34 := Nat.le_of_dvd (by norm_num) hadvd
    interval_cases a <;> revert hadvd <;> decide
  -- the sign of the carrier
  rcases Int.natAbs_eq (x.num * (x.den : ℤ)) with hs | hs
  · -- positive carrier: d = a
    refine ⟨(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inl (by norm_num)
      · exact Or.inr (Or.inr (Or.inl (by norm_num)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring
  · -- negative carrier: d = −a
    refine ⟨-(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by norm_num)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring

/-- **THE SLOT CLASSES ARE SUPPORTED ON THE DISCRIMINANT**: for every point of the
thirty-four twist off the two-torsion, both slot classes are `±1, ±2, ±17` or `±34` —
the distant primes all see even valuations, so nothing else survives the square
quotient. -/
theorem theSlotClassesAreSupportedOnTheDiscriminant {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - 1156 * x) (hy : y ≠ 0) :
    (∃ d₁ : ℚ, OnDiscriminant d₁ ∧ Descent.SqCls x d₁) ∧
    (∃ d₂ : ℚ, OnDiscriminant d₂ ∧ Descent.SqCls (x - 34) d₂) := by
  obtain ⟨hx0, hx34, -⟩ := avoid34 hcurve hy
  constructor
  · exact classFromEvenValuations hx0 fun ℓ hℓ h2 h17 =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_val h2 h17 hcurve hy).1
  · exact classFromEvenValuations (sub_ne_zero.mpr hx34) fun ℓ hℓ h2 h17 =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_val h2 h17 hcurve hy).2

/-! ## 6. The canonical refusal: no face lands on `(1, 2)` -/

private lemma theHalvingDies : ∀ (n : ℕ), ∀ C E F D : ℤ, D.natAbs = n → D ≠ 0 →
    C ^ 2 - 34 * D ^ 2 = 2 * E ^ 2 → C ^ 2 + 34 * D ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F D hD hD0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, a ^ 2 - 34 * d ^ 2 = 2 * b ^ 2 →
        a ^ 2 + 34 * d ^ 2 = 2 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : (C : ZMod 8) ^ 2 - 34 * (D : ZMod 8) ^ 2 = 2 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : (C : ZMod 8) ^ 2 + 34 * (D : ZMod 8) ^ 2 = 2 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8 : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨D', rfl⟩ := hdvd D hD8
    have hD'0 : D' ≠ 0 := fun hc => hD0 (by rw [hc]; ring)
    have h1' : C' ^ 2 - 34 * D' ^ 2 = 2 * E' ^ 2 := by linarith [h1]
    have h2' : C' ^ 2 + 34 * D' ^ 2 = 2 * F' ^ 2 := by linarith [h2]
    have hlt : D'.natAbs < n := by
      have h2n : (2 * D').natAbs = 2 * D'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'0
      omega
    exact ih D'.natAbs hlt C' E' F' D' rfl hD'0 h1' h2'

/-- **THE CANONICAL COSET IS REFUSED**: no point of the thirty-four twist has face
`(1, 2)`.  The class equations clear to a pair of integer quadratic forms with no
primitive solution mod eight; the halving descent kills the imprimitive ones. -/
theorem theCanonicalCosetIsRefused (P : (FamilyFace.E 34).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne 34 P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo 34 P) 2) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs2
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve34 hP
    by_cases hy : y = 0
    · -- a half-turn: each concrete first slot refuses
      rw [hy] at hcurve
      have h0 : x * (x - 34) * (x + 34) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 34 ∨ x = -34 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot34One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
      · rw [slot34One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        exact ChordFace.theThirtyFourIsNotASquare ⟨c, by rw [hval]; ring⟩
      · rw [slot34One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · -- generic: build the three square parameters and clear denominators
      obtain ⟨hx0, hx34, hxm34⟩ := avoid34 hcurve hy
      rw [slot34One_some, if_neg hx0] at hs1
      rw [slot34Two_some, if_neg hx34] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      rw [mul_one] at hcv
      -- the third slot from the curve
      have hce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hc0) he0
      have hf : x + 34 = 2 * (y / (2 * c * e)) ^ 2 := by
        have hs1' : (x + 34) * (2 * c * e) ^ 2 = (x + 34) * (4 * x * e ^ 2) := by
          linear_combination (-4 * (x + 34) * e ^ 2) * hcv
        have hs2' : (x + 34) * (4 * x * e ^ 2) = 2 * x * (x - 34) * (x + 34) := by
          linear_combination (-2 * x * (x + 34)) * hev
        have hs3' : 2 * x * (x - 34) * (x + 34) = 2 * y ^ 2 := by
          linear_combination -2 * hcurve
        have hkey : (x + 34) * (2 * c * e) ^ 2 = 2 * y ^ 2 :=
          hs1'.trans (hs2'.trans hs3')
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hce)]
        exact hkey
      -- clear denominators against the common denominator
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / (2 * c * e)) * ((y / (2 * c * e)).den : ℚ) =
          (y / (2 * c * e)).num := Rat.mul_den_eq_num _
      set f := y / (2 * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
      -- the three integers
      have hCQ : ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) = c * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(e.den : ℚ) * (f.den : ℚ)) * hcd
      have hEQ : ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) = e * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (f.den : ℚ)) * hed
      have hFQ : ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) = f * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (e.den : ℚ)) * hfd
      -- the two integer equations
      have hint1 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 34 * (N : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * N) ^ 2 - 34 * (N : ℚ) ^ 2 = 2 * (e * N) ^ 2 := by
          have hsub : c ^ 2 - 34 = 2 * e ^ 2 := by
            linear_combination -hcv + hev
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 34 * (N : ℚ) ^ 2 =
          2 * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 34 * (N : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * N) ^ 2 + 34 * (N : ℚ) ^ 2 = 2 * (f * N) ^ 2 := by
          have hsub : c ^ 2 + 34 = 2 * f ^ 2 := by
            linear_combination -hcv + hf
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 34 * (N : ℚ) ^ 2 =
          2 * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : ((N : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact theHalvingDies (N : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

/-! ## 7. The realizer faces, and the sixteen translated refusals -/

private lemma hom34 (P Q : (FamilyFace.E 34).Point) :
    Descent.SqCls (FamilyFace.slotOne 34 (P + Q))
      (FamilyFace.slotOne 34 P * FamilyFace.slotOne 34 Q) ∧
    Descent.SqCls (FamilyFace.slotTwo 34 (P + Q))
      (FamilyFace.slotTwo 34 P * FamilyFace.slotTwo 34 Q) :=
  FamilyFace.theFaceIsAHomomorphismOnEveryTwist (by norm_num) P Q

private lemma face_add {P Q : (FamilyFace.E 34).Point} {a b a' b' t₁ t₂ : ℚ}
    (hP : Descent.SqCls (FamilyFace.slotOne 34 P) a ∧
      Descent.SqCls (FamilyFace.slotTwo 34 P) b)
    (hQ : Descent.SqCls (FamilyFace.slotOne 34 Q) a' ∧
      Descent.SqCls (FamilyFace.slotTwo 34 Q) b')
    (h₁ : Descent.SqCls (a * a') t₁) (h₂ : Descent.SqCls (b * b') t₂) :
    Descent.SqCls (FamilyFace.slotOne 34 (P + Q)) t₁ ∧
    Descent.SqCls (FamilyFace.slotTwo 34 (P + Q)) t₂ := by
  obtain ⟨g₁, g₂⟩ := hom34 P Q
  exact ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hP.1 hQ.1) h₁),
    sqcls_trans g₂ (sqcls_trans (sqcls_mul hP.2 hQ.2) h₂)⟩

private lemma face_zero :
    Descent.SqCls (FamilyFace.slotOne 34 (0 : (FamilyFace.E 34).Point)) 1 ∧
    Descent.SqCls (FamilyFace.slotTwo 34 (0 : (FamilyFace.E 34).Point)) 1 :=
  ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩

private lemma face_T0 :
    Descent.SqCls (FamilyFace.slotOne 34 FamilyFace.torsionZero) (-1) ∧
    Descent.SqCls (FamilyFace.slotTwo 34 FamilyFace.torsionZero) (-34) := by
  constructor
  · rw [show FamilyFace.torsionZero = Point.some FamilyFace.nonsingular00 from rfl,
      slot34One_some, if_pos rfl]
    exact ⟨34, by norm_num, by norm_num⟩
  · rw [show FamilyFace.torsionZero = Point.some FamilyFace.nonsingular00 from rfl,
      slot34Two_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T34 :
    Descent.SqCls (FamilyFace.slotOne 34 FamilyFace.torsionRight) 34 ∧
    Descent.SqCls (FamilyFace.slotTwo 34 FamilyFace.torsionRight) 2 := by
  constructor
  · rw [show FamilyFace.torsionRight = Point.some FamilyFace.nonsingular340 from rfl,
      slot34One_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [show FamilyFace.torsionRight = Point.some FamilyFace.nonsingular340 from rfl,
      slot34Two_some, if_pos rfl]
    exact ⟨34, by norm_num, by norm_num⟩

private lemma face_P1 :
    Descent.SqCls (FamilyFace.slotOne 34 FamilyFace.firstDirection) (-2) ∧
    Descent.SqCls (FamilyFace.slotTwo 34 FamilyFace.firstDirection) (-1) := by
  constructor
  · rw [show FamilyFace.firstDirection = Point.some FamilyFace.nonsingularP1 from rfl,
      slot34One_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [show FamilyFace.firstDirection = Point.some FamilyFace.nonsingularP1 from rfl,
      slot34Two_some, if_neg (by norm_num)]
    exact ⟨6, by norm_num, by norm_num⟩

private lemma face_P2 :
    Descent.SqCls (FamilyFace.slotOne 34 FamilyFace.secondDirection) (-1) ∧
    Descent.SqCls (FamilyFace.slotTwo 34 FamilyFace.secondDirection) (-2) := by
  constructor
  · rw [show FamilyFace.secondDirection = Point.some FamilyFace.nonsingularP2 from rfl,
      slot34One_some, if_neg (by norm_num)]
    exact ⟨4, by norm_num, by norm_num⟩
  · rw [show FamilyFace.secondDirection = Point.some FamilyFace.nonsingularP2 from rfl,
      slot34Two_some, if_neg (by norm_num)]
    exact ⟨5, by norm_num, by norm_num⟩

private lemma face_T0T34 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight)) (-34) ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight)) (-17) :=
  face_add face_T0 face_T34 ⟨1, one_ne_zero, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩

private lemma face_T0P1 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.firstDirection)) 2 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.firstDirection)) 34 :=
  face_add face_T0 face_P1 ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.secondDirection)) 1 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.secondDirection)) 17 :=
  face_add face_T0 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩

private lemma face_T34P1 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionRight + FamilyFace.firstDirection)) (-17) ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionRight + FamilyFace.firstDirection)) (-2) :=
  face_add face_T34 face_P1 ⟨2, by norm_num, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T34P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionRight + FamilyFace.secondDirection)) (-34) ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionRight + FamilyFace.secondDirection)) (-1) :=
  face_add face_T34 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩

private lemma face_P1P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.firstDirection + FamilyFace.secondDirection)) 2 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.firstDirection + FamilyFace.secondDirection)) 2 :=
  face_add face_P1 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0T34P1 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection)) 17 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection)) 17 :=
  face_add face_T0T34 face_P1 ⟨2, by norm_num, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0T34P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.secondDirection)) 34 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.secondDirection)) 34 :=
  face_add face_T0T34 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0P1P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.firstDirection + FamilyFace.secondDirection)) (-2) ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.firstDirection + FamilyFace.secondDirection)) (-17) :=
  face_add face_T0P1 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩

private lemma face_T34P1P2 :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionRight + FamilyFace.firstDirection + FamilyFace.secondDirection)) 17 ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionRight + FamilyFace.firstDirection + FamilyFace.secondDirection)) 1 :=
  face_add face_T34P1 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩

private lemma face_all :
    Descent.SqCls (FamilyFace.slotOne 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection +
        FamilyFace.secondDirection)) (-17) ∧
    Descent.SqCls (FamilyFace.slotTwo 34
      (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection +
        FamilyFace.secondDirection)) (-34) :=
  face_add face_T0T34P1 face_P2 ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma refuse_by_translation {d₁ d₂ k₁ k₂ : ℚ} (P R : (FamilyFace.E 34).Point)
    (hR : Descent.SqCls (FamilyFace.slotOne 34 R) k₁ ∧
      Descent.SqCls (FamilyFace.slotTwo 34 R) k₂)
    (hc₁ : Descent.SqCls (FamilyFace.slotOne 34 P) d₁)
    (hc₂ : Descent.SqCls (FamilyFace.slotTwo 34 P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) 1) (ht₂ : Descent.SqCls (d₂ * k₂) 2) : False := by
  obtain ⟨g₁, g₂⟩ := hom34 P R
  exact theCanonicalCosetIsRefused (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

/-! ## 8. The image theorems -/

/-- The sixteen realized square-class pairs. -/
def Realized (d₁ d₂ : ℚ) : Prop :=

  (d₁ = 1 ∧ d₂ = 1) ∨
  (d₁ = 1 ∧ d₂ = 17) ∨
  (d₁ = 2 ∧ d₂ = 2) ∨
  (d₁ = 2 ∧ d₂ = 34) ∨
  (d₁ = 17 ∧ d₂ = 1) ∨
  (d₁ = 17 ∧ d₂ = 17) ∨
  (d₁ = 34 ∧ d₂ = 2) ∨
  (d₁ = 34 ∧ d₂ = 34) ∨
  (d₁ = -1 ∧ d₂ = -2) ∨
  (d₁ = -1 ∧ d₂ = -34) ∨
  (d₁ = -2 ∧ d₂ = -1) ∨
  (d₁ = -2 ∧ d₂ = -17) ∨
  (d₁ = -17 ∧ d₂ = -2) ∨
  (d₁ = -17 ∧ d₂ = -34) ∨
  (d₁ = -34 ∧ d₂ = -1) ∨
  (d₁ = -34 ∧ d₂ = -17)


/-- **THE FACE IMAGE IS THE REALIZED SIXTEEN**: every point of the thirty-four twist has
its face in the sixteen classes realized by the half-turns and the two directions — the
two-descent upper bound, closing rank at most two in descent form. -/
theorem theFaceImageIsTheRealizedSixteen (P : (FamilyFace.E 34).Point) :
    ∃ d₁ d₂ : ℚ, Realized d₁ d₂ ∧
      Descent.SqCls (FamilyFace.slotOne 34 P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo 34 P) d₂ := by
  rcases P with _ | @⟨x, y, hP⟩
  · exact ⟨1, 1, by simp [Realized], Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · have hcurve := onCurve34 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 34) * (x + 34) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 34 ∨ x = -34 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · refine ⟨-1, -34, by simp [Realized], ?_, ?_⟩
        · rw [slot34One_some, if_pos rfl]
          exact ⟨34, by norm_num, by norm_num⟩
        · rw [slot34Two_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
      · refine ⟨34, 2, by simp [Realized], ?_, ?_⟩
        · rw [slot34One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
        · rw [slot34Two_some, if_pos rfl]
          exact ⟨34, by norm_num, by norm_num⟩
      · refine ⟨-34, -17, by simp [Realized], ?_, ?_⟩
        · rw [slot34One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
        · rw [slot34Two_some, if_neg (by norm_num)]
          exact ⟨2, by norm_num, by norm_num⟩
    · obtain ⟨hx0, hx34, hxm34⟩ := avoid34 hcurve hy
      obtain ⟨⟨d₁, hd₁, hc₁⟩, ⟨d₂, hd₂, hc₂⟩⟩ :=
        theSlotClassesAreSupportedOnTheDiscriminant hcurve hy
      have hsig := theSignsAgreeAcrossTheFace hcurve hy hc₁ hc₂
      have hs1 : Descent.SqCls (FamilyFace.slotOne 34 (Point.some hP)) d₁ := by
        rw [slot34One_some, if_neg hx0]
        exact hc₁
      have hs2 : Descent.SqCls (FamilyFace.slotTwo 34 (Point.some hP)) d₂ := by
        rw [slot34Two_some, if_neg hx34]
        exact hc₂
      clear hc₁ hc₂
      rcases hd₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

      · -- (1, 1): realized
        exact ⟨1, 1, by simp [Realized], hs1, hs2⟩
      · -- (1, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 2): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (0 : (FamilyFace.E 34).Point) face_zero hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (1, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 17): realized
        exact ⟨1, 17, by simp [Realized], hs1, hs2⟩
      · -- (1, -17): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 34): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.secondDirection) face_T0P2 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (1, -34): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-1, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -1): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ FamilyFace.secondDirection face_P2 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-1, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -2): realized
        exact ⟨-1, -2, by simp [Realized], hs1, hs2⟩
      · -- (-1, 17): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -17): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ FamilyFace.torsionZero face_T0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (-1, 34): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -34): realized
        exact ⟨-1, -34, by simp [Realized], hs1, hs2⟩
      · -- (2, 1): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.firstDirection + FamilyFace.secondDirection) face_P1P2 hs1 hs2
          ⟨2, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (2, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 2): realized
        exact ⟨2, 2, by simp [Realized], hs1, hs2⟩
      · -- (2, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 17): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.firstDirection) face_T0P1 hs1 hs2
          ⟨2, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (2, -17): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 34): realized
        exact ⟨2, 34, by simp [Realized], hs1, hs2⟩
      · -- (2, -34): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-2, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -1): realized
        exact ⟨-2, -1, by simp [Realized], hs1, hs2⟩
      · -- (-2, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -2): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ FamilyFace.firstDirection face_P1 hs1 hs2
          ⟨2, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-2, 17): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -17): realized
        exact ⟨-2, -17, by simp [Realized], hs1, hs2⟩
      · -- (-2, 34): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -34): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.firstDirection + FamilyFace.secondDirection) face_T0P1P2 hs1 hs2
          ⟨2, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (17, 1): realized
        exact ⟨17, 1, by simp [Realized], hs1, hs2⟩
      · -- (17, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 2): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionRight + FamilyFace.firstDirection + FamilyFace.secondDirection) face_T34P1P2 hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (17, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 17): realized
        exact ⟨17, 17, by simp [Realized], hs1, hs2⟩
      · -- (17, -17): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 34): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection) face_T0T34P1 hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (17, -34): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-17, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -1): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionRight + FamilyFace.firstDirection) face_T34P1 hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-17, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -2): realized
        exact ⟨-17, -2, by simp [Realized], hs1, hs2⟩
      · -- (-17, 17): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -17): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.firstDirection + FamilyFace.secondDirection) face_all hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (-17, 34): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -34): realized
        exact ⟨-17, -34, by simp [Realized], hs1, hs2⟩
      · -- (34, 1): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ FamilyFace.torsionRight face_T34 hs1 hs2
          ⟨34, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (34, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 2): realized
        exact ⟨34, 2, by simp [Realized], hs1, hs2⟩
      · -- (34, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 17): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.torsionRight + FamilyFace.secondDirection) face_T0T34P2 hs1 hs2
          ⟨34, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (34, -17): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 34): realized
        exact ⟨34, 34, by simp [Realized], hs1, hs2⟩
      · -- (34, -34): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-34, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -1): realized
        exact ⟨-34, -1, by simp [Realized], hs1, hs2⟩
      · -- (-34, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -2): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionRight + FamilyFace.secondDirection) face_T34P2 hs1 hs2
          ⟨34, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-34, 17): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -17): realized
        exact ⟨-34, -17, by simp [Realized], hs1, hs2⟩
      · -- (-34, 34): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -34): translated onto the canonical coset and refused
        exact absurd (refuse_by_translation _ (FamilyFace.torsionZero + FamilyFace.torsionRight) face_T0T34 hs1 hs2
          ⟨34, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false


/-- **THE REALIZED SIXTEEN ARE IN THE IMAGE**: every one of the sixteen classes is the
face of an explicit point — sums of the half-turns and the two directions, their classes
read through the homomorphism.  With the upper bound the image is exactly the realized
group: the two-descent of the thirty-four twist is complete. -/
theorem theRealizedSixteenAreInTheImage (d₁ d₂ : ℚ) (h : Realized d₁ d₂) :
    ∃ P : (FamilyFace.E 34).Point,
      Descent.SqCls (FamilyFace.slotOne 34 P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo 34 P) d₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, face_zero⟩
  · exact ⟨_, face_T0P2⟩
  · exact ⟨_, face_P1P2⟩
  · exact ⟨_, face_T0P1⟩
  · exact ⟨_, face_T34P1P2⟩
  · exact ⟨_, face_T0T34P1⟩
  · exact ⟨_, face_T34⟩
  · exact ⟨_, face_T0T34P2⟩
  · exact ⟨_, face_P2⟩
  · exact ⟨_, face_T0⟩
  · exact ⟨_, face_P1⟩
  · exact ⟨_, face_T0P1P2⟩
  · exact ⟨_, face_T34P1⟩
  · exact ⟨_, face_all⟩
  · exact ⟨_, face_T34P2⟩
  · exact ⟨_, face_T0T34⟩

end Soma.Holonics.Millennium.FaceImage
