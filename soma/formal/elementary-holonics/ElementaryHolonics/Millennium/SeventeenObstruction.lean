import ElementaryHolonics.Millennium.StratumDescent
import Mathlib.Tactic

/-!
# SeventeenObstruction: the obstruction population is exhibited at seventeen

**The Tate–Shafarevich structure, made exact — the aggressive face of the mod-two
Birch–Swinnerton-Dyer goal.**  Seventeen sits where the governance matrix goes
**singular**: `17 ≡ 1 (mod 8)`, both governing characters vanish (`−1` and `2` are
squares mod seventeen), and the stratum machinery's `p`-adic refusals have nothing to
grip.  What happens is the classical first Ш phenomenon, and this file computes it:

* **the face image lies in the Selmer sixteen** (`theSeventeenFaceLiesInTheSelmerSixteen`):
  of the sixty-four candidate classes, thirty-two die in the real frame and sixteen die
  at the frame of eight (four kernel `decide`s with the halving descent) — every point's
  face lies in the sixteen survivors: the four realized torsion classes and **twelve
  locally invisible classes** forming three cosets;
* **the twelve are invisible at every congruence depth**
  (`theInvisibleCosetsPassEveryTwoAdicFrame`, `theInvisibleCosetsPassEverySeventeenAdicFrame`):
  for each of the three coset representatives, fixed integer witnesses solve the class
  system modulo `2^k` and modulo `17^k` for **every** `k` — one square-lifting lemma per
  prime — so no congruence refusal exists at any depth of either frame.  The instrument
  that killed twenty-eight classes provably cannot kill these twelve;
* **the global refusal is the named-open second descent**
  (`TheInvisibleCosetsAreGloballyRefused`): classically the three cosets contain no
  rational face (seventeen is not a congruent number; the refusal is a Lind–Reichardt-type
  quartic-residue descent, since `2` is a square but not a fourth power mod seventeen).
  Granted it, `Sel₂/image ≅ (ℤ/2)²` — the group **Ш(E₁₇)[2]**, the Birch–Swinnerton-Dyer
  obstruction object, with every local ingredient kernel-checked in this tree.

Unconditionally this file exhibits the local/global gap in the corpus's own vocabulary:
**a population locally admissible at every named frame and every depth, that the realized
current never reaches** — the phase-object of descent, invisible to every magnitude check
the completed descents used.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the global
refusal of the three invisible cosets is a named-open proposition with its falsifier, not
a theorem here; "Selmer" and "Ш" are classical readings carried as `interpretation`;
nothing about the Birch–Swinnerton-Dyer conjecture.
-/

set_option maxHeartbeats 1600000

namespace Soma.Holonics.Millennium.SeventeenObstruction

open WeierstrassCurve.Affine

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_mul {a b c d : ℚ} (h₁ : Descent.SqCls a c) (h₂ : Descent.SqCls b d) :
    Descent.SqCls (a * b) (c * d) := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma hp17 : Nat.Prime 17 := by norm_num

private lemma onCurve17 {x y : ℚ} (h : (FamilyFace.E (17 : ℕ)).Nonsingular x y) :
    y ^ 2 = x ^ 3 - 289 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  push_cast at h1
  linarith [h1]

private lemma avoid17 {x y : ℚ} (h : y ^ 2 = x ^ 3 - 289 * x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ 17 ∧ x ≠ -17 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by rw [h]; ring))

private lemma slot17One_some {x y : ℚ} (h : (FamilyFace.E (17 : ℕ)).Nonsingular x y) :
    FamilyFace.slotOne (17 : ℕ) (.some h) = if x = 0 then -((17 : ℕ) : ℚ) ^ 2 else x := rfl

private lemma slot17Two_some {x y : ℚ} (h : (FamilyFace.E (17 : ℕ)).Nonsingular x y) :
    FamilyFace.slotTwo (17 : ℕ) (.some h) =
      if x = ((17 : ℕ) : ℚ) then 2 * ((17 : ℕ) : ℚ) ^ 2 else x - ((17 : ℕ) : ℚ) := rfl

/-! ## 1. The four refusal kernels at the frame of eight -/

private lemma kernelTwoOne17 : ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - 17 * N ^ 2 = E ^ 2 → 2 * C ^ 2 + 17 * N ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 17 * d ^ 2 = b ^ 2 → 2 * a ^ 2 + 17 * d ^ 2 = 2 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 17 * (N : ZMod 8) ^ 2 = (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 17 * (N : ZMod 8) ^ 2 = 2 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8' : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨N', rfl⟩ := hdvd N hD8
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 17 * N' ^ 2 = E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 17 * N' ^ 2 = 2 * F' ^ 2 := by linarith [h2]
    have hlt : N'.natAbs < n := by
      have h2n : (2 * N').natAbs = 2 * N'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : N'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN'0
      omega
    exact ih N'.natAbs hlt C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoTwo17 : ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - 17 * N ^ 2 = 2 * E ^ 2 → 2 * C ^ 2 + 17 * N ^ 2 = F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 17 * d ^ 2 = 2 * b ^ 2 → 2 * a ^ 2 + 17 * d ^ 2 = c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 17 * (N : ZMod 8) ^ 2 = 2 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 17 * (N : ZMod 8) ^ 2 = (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8' : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨N', rfl⟩ := hdvd N hD8
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 17 * N' ^ 2 = 2 * E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 17 * N' ^ 2 = F' ^ 2 := by linarith [h2]
    have hlt : N'.natAbs < n := by
      have h2n : (2 * N').natAbs = 2 * N'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : N'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN'0
      omega
    exact ih N'.natAbs hlt C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoSeventeen17 : ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - 17 * N ^ 2 = 17 * E ^ 2 → 2 * C ^ 2 + 17 * N ^ 2 = 34 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 17 * d ^ 2 = 17 * b ^ 2 → 2 * a ^ 2 + 17 * d ^ 2 = 34 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 17 * (N : ZMod 8) ^ 2 = 17 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 17 * (N : ZMod 8) ^ 2 = 34 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8' : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨N', rfl⟩ := hdvd N hD8
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 17 * N' ^ 2 = 17 * E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 17 * N' ^ 2 = 34 * F' ^ 2 := by linarith [h2]
    have hlt : N'.natAbs < n := by
      have h2n : (2 * N').natAbs = 2 * N'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : N'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN'0
      omega
    exact ih N'.natAbs hlt C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoThirtyFour17 : ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - 17 * N ^ 2 = 34 * E ^ 2 → 2 * C ^ 2 + 17 * N ^ 2 = 17 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 17 * d ^ 2 = 34 * b ^ 2 → 2 * a ^ 2 + 17 * d ^ 2 = 17 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 17 * (N : ZMod 8) ^ 2 = 34 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 17 * (N : ZMod 8) ^ 2 = 17 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8' : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨N', rfl⟩ := hdvd N hD8
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 17 * N' ^ 2 = 34 * E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 17 * N' ^ 2 = 17 * F' ^ 2 := by linarith [h2]
    have hlt : N'.natAbs < n := by
      have h2n : (2 * N').natAbs = 2 * N'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : N'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN'0
      omega
    exact ih N'.natAbs hlt C' E' F' N' rfl hN'0 h1' h2'

/-! ## 2. The four refusal theorems -/

private lemma refuse17TwoOne (P : (FamilyFace.E (17 : ℕ)).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) (1)) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve17 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 17) * (x + 17) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 17 ∨ x = -17 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot17One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        push_cast at hval
        nlinarith [sq_nonneg c, hval]
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine ChordFace.theThirtyFourIsNotASquare ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoid17 hcurve hy
      rw [slot17One_some, if_neg hx0] at hs1
      rw [slot17Two_some, if_neg (by exact_mod_cast hxp),
        show ((17 : ℕ) : ℚ) = 17 from by norm_num] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      rw [mul_one] at hev
      have hmce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hc0) he0
      have hf : x + 17 = 2 * (y / (2 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := hcv
        have hcB : x - 17 = e ^ 2 * (1) := by linear_combination hev
        have hchain : (x + 17) * ((2 : ℚ) * c * e) ^ 2 = (2) * y ^ 2 := by
          have hstep1 : (x + 17) * ((2 : ℚ) * c * e) ^ 2 =
              (x + 17) * ((2) * x * e ^ 2) := by
            linear_combination (-(2 : ℚ) * (x + 17) * e ^ 2) * hcA
          have hstep2 : (x + 17) * ((2 : ℚ) * x * e ^ 2) =
              (2) * (x * (x - 17) * (x + 17)) := by
            linear_combination (-(2 : ℚ) * x * (x + 17)) * hcB
          have hstep3 : ((2 : ℚ)) * (x * (x - 17) * (x + 17)) = (2) * y ^ 2 := by
            linear_combination -(2 : ℚ) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2 : ℚ) * c * e)) * ((y / ((2 : ℚ) * c * e)).den : ℚ) =
          (y / ((2 : ℚ) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2 : ℚ) * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
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
      have hsub1 : 2 * c ^ 2 - (1 : ℚ) * e ^ 2 = 17 := by
        linear_combination hev - hcv
      have hsub2 : 2 * c ^ 2 + (17 : ℚ) = (2) * f ^ 2 := by
        rw [hfdef]
        linear_combination hf - hcv
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 17 * ((N : ℕ) : ℤ) ^ 2 =
          (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
            (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
          ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 17 * ((N : ℕ) : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
            (2 : ℚ) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
          (2 : ℚ) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoOne17 ((N : ℕ) : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuse17TwoTwo (P : (FamilyFace.E (17 : ℕ)).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) (2)) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve17 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 17) * (x + 17) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 17 ∨ x = -17 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot17One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        push_cast at hval
        nlinarith [sq_nonneg c, hval]
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine ChordFace.theThirtyFourIsNotASquare ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoid17 hcurve hy
      rw [slot17One_some, if_neg hx0] at hs1
      rw [slot17Two_some, if_neg (by exact_mod_cast hxp),
        show ((17 : ℕ) : ℚ) = 17 from by norm_num] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hc0) he0
      have hf : x + 17 = (y / (2 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := hcv
        have hcB : x - 17 = e ^ 2 * (2) := hev
        have hchain : (x + 17) * ((2 : ℚ) * c * e) ^ 2 = (1) * y ^ 2 := by
          have hstep1 : (x + 17) * ((2 : ℚ) * c * e) ^ 2 =
              (x + 17) * ((2) * x * e ^ 2) := by
            linear_combination (-(2 : ℚ) * (x + 17) * e ^ 2) * hcA
          have hstep2 : (x + 17) * ((2 : ℚ) * x * e ^ 2) =
              (1) * (x * (x - 17) * (x + 17)) := by
            linear_combination (-(1 : ℚ) * x * (x + 17)) * hcB
          have hstep3 : ((1 : ℚ)) * (x * (x - 17) * (x + 17)) = (1) * y ^ 2 := by
            linear_combination -(1 : ℚ) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hmce)]
        linear_combination hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2 : ℚ) * c * e)) * ((y / ((2 : ℚ) * c * e)).den : ℚ) =
          (y / ((2 : ℚ) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2 : ℚ) * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
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
      have hsub1 : 2 * c ^ 2 - (2 : ℚ) * e ^ 2 = 17 := by
        linear_combination hev - hcv
      have hsub2 : 2 * c ^ 2 + (17 : ℚ) = (1) * f ^ 2 := by
        rw [hfdef]
        linear_combination hf - hcv
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 17 * ((N : ℕ) : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
            (2 : ℚ) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
          (2 : ℚ) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 17 * ((N : ℕ) : ℤ) ^ 2 =
          (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
            (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
          ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoTwo17 ((N : ℕ) : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuse17TwoSeventeen (P : (FamilyFace.E (17 : ℕ)).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) (17)) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve17 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 17) * (x + 17) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 17 ∨ x = -17 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot17One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        push_cast at hval
        nlinarith [sq_nonneg c, hval]
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine ChordFace.theThirtyFourIsNotASquare ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoid17 hcurve hy
      rw [slot17One_some, if_neg hx0] at hs1
      rw [slot17Two_some, if_neg (by exact_mod_cast hxp),
        show ((17 : ℕ) : ℚ) = 17 from by norm_num] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmce : (34 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hc0) he0
      have hf : x + 17 = 34 * (y / (34 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := hcv
        have hcB : x - 17 = e ^ 2 * (17) := hev
        have hchain : (x + 17) * ((34 : ℚ) * c * e) ^ 2 = (34) * y ^ 2 := by
          have hstep1 : (x + 17) * ((34 : ℚ) * c * e) ^ 2 =
              (x + 17) * ((578) * x * e ^ 2) := by
            linear_combination (-(578 : ℚ) * (x + 17) * e ^ 2) * hcA
          have hstep2 : (x + 17) * ((578 : ℚ) * x * e ^ 2) =
              (34) * (x * (x - 17) * (x + 17)) := by
            linear_combination (-(34 : ℚ) * x * (x + 17)) * hcB
          have hstep3 : ((34 : ℚ)) * (x * (x - 17) * (x + 17)) = (34) * y ^ 2 := by
            linear_combination -(34 : ℚ) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((34 : ℚ) * c * e)) * ((y / ((34 : ℚ) * c * e)).den : ℚ) =
          (y / ((34 : ℚ) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((34 : ℚ) * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
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
      have hsub1 : 2 * c ^ 2 - (17 : ℚ) * e ^ 2 = 17 := by
        linear_combination hev - hcv
      have hsub2 : 2 * c ^ 2 + (17 : ℚ) = (34) * f ^ 2 := by
        rw [hfdef]
        linear_combination hf - hcv
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 17 * ((N : ℕ) : ℤ) ^ 2 =
          17 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
            (17 : ℚ) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
          (17 : ℚ) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 17 * ((N : ℕ) : ℤ) ^ 2 =
          34 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
            (34 : ℚ) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
          (34 : ℚ) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoSeventeen17 ((N : ℕ) : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuse17TwoThirtyFour (P : (FamilyFace.E (17 : ℕ)).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) (34)) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve17 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 17) * (x + 17) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 17 ∨ x = -17 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot17One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        push_cast at hval
        nlinarith [sq_nonneg c, hval]
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine ChordFace.theThirtyFourIsNotASquare ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot17One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoid17 hcurve hy
      rw [slot17One_some, if_neg hx0] at hs1
      rw [slot17Two_some, if_neg (by exact_mod_cast hxp),
        show ((17 : ℕ) : ℚ) = 17 from by norm_num] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmce : (34 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hc0) he0
      have hf : x + 17 = 17 * (y / (34 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := hcv
        have hcB : x - 17 = e ^ 2 * (34) := hev
        have hchain : (x + 17) * ((34 : ℚ) * c * e) ^ 2 = (17) * y ^ 2 := by
          have hstep1 : (x + 17) * ((34 : ℚ) * c * e) ^ 2 =
              (x + 17) * ((578) * x * e ^ 2) := by
            linear_combination (-(578 : ℚ) * (x + 17) * e ^ 2) * hcA
          have hstep2 : (x + 17) * ((578 : ℚ) * x * e ^ 2) =
              (17) * (x * (x - 17) * (x + 17)) := by
            linear_combination (-(17 : ℚ) * x * (x + 17)) * hcB
          have hstep3 : ((17 : ℚ)) * (x * (x - 17) * (x + 17)) = (17) * y ^ 2 := by
            linear_combination -(17 : ℚ) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((34 : ℚ) * c * e)) * ((y / ((34 : ℚ) * c * e)).den : ℚ) =
          (y / ((34 : ℚ) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((34 : ℚ) * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
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
      have hsub1 : 2 * c ^ 2 - (34 : ℚ) * e ^ 2 = 17 := by
        linear_combination hev - hcv
      have hsub2 : 2 * c ^ 2 + (17 : ℚ) = (17) * f ^ 2 := by
        rw [hfdef]
        linear_combination hf - hcv
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 17 * ((N : ℕ) : ℤ) ^ 2 =
          34 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
            (34 : ℚ) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 17 * ((N : ℕ) : ℚ) ^ 2 =
          (34 : ℚ) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 17 * ((N : ℕ) : ℤ) ^ 2 =
          17 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * (N : ℚ)) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
            (17 : ℚ) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 17 * ((N : ℕ) : ℚ) ^ 2 =
          (17 : ℚ) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoThirtyFour17 ((N : ℕ) : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

/-! ## 3. The support wrapper and the torsion realizers -/

private lemma support17 {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 289 * x) (hy : y ≠ 0) :
    (∃ d₁ : ℚ, (d₁ = 1 ∨ d₁ = -1 ∨ d₁ = 2 ∨ d₁ = -2 ∨ d₁ = 17 ∨ d₁ = -17 ∨
      d₁ = 34 ∨ d₁ = -34) ∧ Descent.SqCls x d₁) ∧
    (∃ d₂ : ℚ, (d₂ = 1 ∨ d₂ = -1 ∨ d₂ = 2 ∨ d₂ = -2 ∨ d₂ = 17 ∨ d₂ = -17 ∨
      d₂ = 34 ∨ d₂ = -34) ∧ Descent.SqCls (x - 17) d₂) := by
  have hcast : ((17 : ℕ) : ℚ) = 17 := by norm_num
  have hne2 : (17 : ℕ) ≠ 2 := by norm_num
  have hcurve' : y ^ 2 = x ^ 3 - ((17 : ℕ) : ℚ) ^ 2 * x := by
    rw [hcast]
    linear_combination hcurve
  obtain ⟨⟨d₁, hd₁, hc₁⟩, ⟨d₂, hd₂, hc₂⟩⟩ :=
    StratumDescent.theSlotClassesAreSupportedOnTheStratum (p := 17) hp17 hne2 hcurve' hy
  rw [hcast] at hc₂
  unfold StratumDescent.OnDiscriminantP at hd₁ hd₂
  rw [hcast] at hd₁ hd₂
  norm_num at hd₁ hd₂
  exact ⟨⟨d₁, by tauto, hc₁⟩, ⟨d₂, by tauto, hc₂⟩⟩

private lemma ns00 : (FamilyFace.E (17 : ℕ)).Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [FamilyFace.E], Or.inl ?_⟩
  simp only [FamilyFace.E]
  norm_num

private lemma ns17 : (FamilyFace.E (17 : ℕ)).Nonsingular ((17 : ℕ) : ℚ) 0 := by
  rw [nonsingular_iff, equation_iff]
  constructor
  · simp only [FamilyFace.E]
    push_cast
    ring
  · refine Or.inl ?_
    simp only [FamilyFace.E]
    push_cast
    norm_num

private def T0' : (FamilyFace.E (17 : ℕ)).Point := .some ns00

private def T17' : (FamilyFace.E (17 : ℕ)).Point := .some ns17

private lemma face_T0' :
    Descent.SqCls (FamilyFace.slotOne (17 : ℕ) T0') (-1) ∧
    Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) T0') (-17) := by
  constructor
  · rw [show T0' = Point.some ns00 from rfl, slot17One_some, if_pos rfl]
    exact ⟨17, by norm_num, by push_cast; ring⟩
  · rw [show T0' = Point.some ns00 from rfl, slot17Two_some, if_neg (by norm_num), zero_sub]
    exact ⟨1, one_ne_zero, by push_cast; ring⟩

private lemma face_T17' :
    Descent.SqCls (FamilyFace.slotOne (17 : ℕ) T17') 17 ∧
    Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) T17') 2 := by
  constructor
  · rw [show T17' = Point.some ns17 from rfl, slot17One_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by push_cast; ring⟩
  · rw [show T17' = Point.some ns17 from rfl, slot17Two_some, if_pos rfl]
    exact ⟨17, by norm_num, by push_cast; ring⟩

private lemma hom17 (P Q : (FamilyFace.E (17 : ℕ)).Point) :
    Descent.SqCls (FamilyFace.slotOne (17 : ℕ) (P + Q))
      (FamilyFace.slotOne (17 : ℕ) P * FamilyFace.slotOne (17 : ℕ) Q) ∧
    Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) (P + Q))
      (FamilyFace.slotTwo (17 : ℕ) P * FamilyFace.slotTwo (17 : ℕ) Q) :=
  FamilyFace.theFaceIsAHomomorphismOnEveryTwist (by norm_num) P Q

private lemma face_T0T17' :
    Descent.SqCls (FamilyFace.slotOne (17 : ℕ) (T0' + T17')) (-17) ∧
    Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) (T0' + T17')) (-34) := by
  obtain ⟨g₁, g₂⟩ := hom17 T0' T17'
  exact ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul face_T0'.1 face_T17'.1)
      ⟨1, one_ne_zero, by ring⟩),
    sqcls_trans g₂ (sqcls_trans (sqcls_mul face_T0'.2 face_T17'.2)
      ⟨1, one_ne_zero, by ring⟩)⟩

private lemma refuse_tr {d₁ d₂ k₁ k₂ A B : ℚ}
    (P R : (FamilyFace.E (17 : ℕ)).Point)
    (href : ∀ Q : (FamilyFace.E (17 : ℕ)).Point,
      ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) Q) A ∧
         Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) Q) B))
    (hR : Descent.SqCls (FamilyFace.slotOne (17 : ℕ) R) k₁ ∧
      Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) R) k₂)
    (hc₁ : Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) d₁)
    (hc₂ : Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) A) (ht₂ : Descent.SqCls (d₂ * k₂) B) : False := by
  obtain ⟨g₁, g₂⟩ := hom17 P R
  exact href (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

/-! ## 4. The Selmer sixteen and the image theorem -/

/-- The sixteen locally admissible classes of the seventeen twist: the four realized
torsion classes and the twelve locally invisible classes in three cosets. -/
def SelmerSixteen (d₁ d₂ : ℚ) : Prop :=
  (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = -1 ∧ d₂ = -17) ∨ (d₁ = 17 ∧ d₂ = 2) ∨ (d₁ = -17 ∧ d₂ = -34) ∨
  (d₁ = 1 ∧ d₂ = 2) ∨ (d₁ = -1 ∧ d₂ = -34) ∨ (d₁ = 17 ∧ d₂ = 1) ∨ (d₁ = -17 ∧ d₂ = -17) ∨
  (d₁ = 1 ∧ d₂ = 17) ∨ (d₁ = -1 ∧ d₂ = -1) ∨ (d₁ = 17 ∧ d₂ = 34) ∨ (d₁ = -17 ∧ d₂ = -2) ∨
  (d₁ = 1 ∧ d₂ = 34) ∨ (d₁ = -1 ∧ d₂ = -2) ∨ (d₁ = 17 ∧ d₂ = 17) ∨ (d₁ = -17 ∧ d₂ = -1)

/-- **THE FACE LIES IN THE SELMER SIXTEEN**: every point of the seventeen twist has its
face among the sixteen locally admissible classes — the thirty-two mixed-sign classes
die in the real frame and the sixteen even-part classes die at the frame of eight; the
twelve invisible classes and the four realized ones remain. -/
theorem theSeventeenFaceLiesInTheSelmerSixteen (P : (FamilyFace.E (17 : ℕ)).Point) :
    ∃ d₁ d₂ : ℚ, SelmerSixteen d₁ d₂ ∧
      Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) d₂ := by
  rcases P with _ | @⟨x, y, hP⟩
  · exact ⟨1, 1, by simp [SelmerSixteen], Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · have hcurve := onCurve17 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 17) * (x + 17) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 17 ∨ x = -17 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · refine ⟨-1, -17, by simp [SelmerSixteen], ?_, ?_⟩
        · rw [slot17One_some, if_pos rfl]
          exact ⟨17, by norm_num, by push_cast; ring⟩
        · rw [slot17Two_some, if_neg (by norm_num), zero_sub]
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
      · refine ⟨17, 2, by simp [SelmerSixteen], ?_, ?_⟩
        · rw [slot17One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by ring⟩
        · rw [slot17Two_some, if_pos (by norm_num)]
          exact ⟨17, by norm_num, by push_cast; ring⟩
      · refine ⟨-17, -34, by simp [SelmerSixteen], ?_, ?_⟩
        · rw [slot17One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by ring⟩
        · rw [slot17Two_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
    · obtain ⟨hx0, hxp, hxmp⟩ := avoid17 hcurve hy
      obtain ⟨⟨d₁, hd₁, hc₁⟩, ⟨d₂, hd₂, hc₂⟩⟩ := support17 hcurve hy
      have hsig := StratumDescent.theSignsAgreeOnTheStratum (p := 17) (x := x) (y := y)
        hp17 (by push_cast; linear_combination hcurve) hy hc₁
        (by rw [show ((17 : ℕ) : ℚ) = 17 from by norm_num]; exact hc₂)
      have hs1 : Descent.SqCls (FamilyFace.slotOne (17 : ℕ) (Point.some hP)) d₁ := by
        rw [slot17One_some, if_neg hx0]
        exact hc₁
      have hs2 : Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) (Point.some hP)) d₂ := by
        rw [slot17Two_some, if_neg (by exact_mod_cast hxp),
          show ((17 : ℕ) : ℚ) = 17 from by norm_num]
        exact hc₂
      clear hc₁ hc₂
      rcases hd₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- (1, 1): in the Selmer sixteen
        exact ⟨1, 1, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (1, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 2): in the Selmer sixteen
        exact ⟨1, 2, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (1, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 17): in the Selmer sixteen
        exact ⟨1, 17, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (1, -17): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 34): in the Selmer sixteen
        exact ⟨1, 34, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (1, -34): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-1, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -1): in the Selmer sixteen
        exact ⟨-1, -1, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-1, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -2): in the Selmer sixteen
        exact ⟨-1, -2, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-1, 17): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -17): in the Selmer sixteen
        exact ⟨-1, -17, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-1, 34): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -34): in the Selmer sixteen
        exact ⟨-1, -34, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (2, 1): refused at the frame of eight
        exact absurd ⟨hs1, hs2⟩ (refuse17TwoOne _)
      · -- (2, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 2): refused at the frame of eight
        exact absurd ⟨hs1, hs2⟩ (refuse17TwoTwo _)
      · -- (2, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 17): refused at the frame of eight
        exact absurd ⟨hs1, hs2⟩ (refuse17TwoSeventeen _)
      · -- (2, -17): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 34): refused at the frame of eight
        exact absurd ⟨hs1, hs2⟩ (refuse17TwoThirtyFour _)
      · -- (2, -34): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-2, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -1): translated and refused
        exact absurd (refuse_tr _ T0' (refuse17TwoSeventeen) face_T0' hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-2, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -2): translated and refused
        exact absurd (refuse_tr _ T0' (refuse17TwoThirtyFour) face_T0' hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-2, 17): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -17): translated and refused
        exact absurd (refuse_tr _ T0' (refuse17TwoOne) face_T0' hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (-2, 34): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -34): translated and refused
        exact absurd (refuse_tr _ T0' (refuse17TwoTwo) face_T0' hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (17, 1): in the Selmer sixteen
        exact ⟨17, 1, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (17, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 2): in the Selmer sixteen
        exact ⟨17, 2, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (17, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 17): in the Selmer sixteen
        exact ⟨17, 17, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (17, -17): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (17, 34): in the Selmer sixteen
        exact ⟨17, 34, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (17, -34): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-17, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -1): in the Selmer sixteen
        exact ⟨-17, -1, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-17, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -2): in the Selmer sixteen
        exact ⟨-17, -2, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-17, 17): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -17): in the Selmer sixteen
        exact ⟨-17, -17, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (-17, 34): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-17, -34): in the Selmer sixteen
        exact ⟨-17, -34, by simp [SelmerSixteen], hs1, hs2⟩
      · -- (34, 1): translated and refused
        exact absurd (refuse_tr _ T17' (refuse17TwoTwo) face_T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (34, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 2): translated and refused
        exact absurd (refuse_tr _ T17' (refuse17TwoOne) face_T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩) not_false
      · -- (34, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 17): translated and refused
        exact absurd (refuse_tr _ T17' (refuse17TwoThirtyFour) face_T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (34, -17): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (34, 34): translated and refused
        exact absurd (refuse_tr _ T17' (refuse17TwoSeventeen) face_T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩) not_false
      · -- (34, -34): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-34, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -1): translated and refused
        exact absurd (refuse_tr _ (T0' + T17') (refuse17TwoThirtyFour) face_T0T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-34, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -2): translated and refused
        exact absurd (refuse_tr _ (T0' + T17') (refuse17TwoSeventeen) face_T0T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩) not_false
      · -- (-34, 17): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -17): translated and refused
        exact absurd (refuse_tr _ (T0' + T17') (refuse17TwoTwo) face_T0T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨17, by norm_num, by norm_num⟩) not_false
      · -- (-34, 34): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-34, -34): translated and refused
        exact absurd (refuse_tr _ (T0' + T17') (refuse17TwoOne) face_T0T17' hs1 hs2
          ⟨17, by norm_num, by norm_num⟩ ⟨34, by norm_num, by norm_num⟩) not_false

/-- **THE REALIZED FOUR ARE IN THE IMAGE** at seventeen. -/
theorem theRealizedFourAreInTheImageAtSeventeen (d₁ d₂ : ℚ)
    (h : (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = -1 ∧ d₂ = -17) ∨ (d₁ = 17 ∧ d₂ = 2) ∨
      (d₁ = -17 ∧ d₂ = -34)) :
    ∃ P : (FamilyFace.E (17 : ℕ)).Point,
      Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) d₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · exact ⟨T0', face_T0'⟩
  · exact ⟨T17', face_T17'⟩
  · exact ⟨T0' + T17', face_T0T17'⟩

/-! ## 5. The square-lifting lemmas and the depth-universal invisibility -/

private lemma two_adic_square_lift (a : ℤ) (ha : a % 8 = 1) :
    ∀ k : ℕ, ∃ x : ℤ, ¬ 2 ∣ x ∧ (2 ^ k : ℤ) ∣ x ^ 2 - a := by
  intro k
  induction k with
  | zero => exact ⟨1, by norm_num, one_dvd _⟩
  | succ k ih =>
    by_cases hk : k + 1 ≤ 3
    · refine ⟨1, by norm_num, ?_⟩
      have h8 : (8 : ℤ) ∣ 1 ^ 2 - a := by omega
      exact dvd_trans (pow_dvd_pow 2 hk) h8
    · push_neg at hk
      have hk3 : 3 ≤ k := by omega
      obtain ⟨x, hx2, t, ht⟩ := ih
      rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact ⟨x, hx2, ⟨u, by rw [ht, hu]; ring⟩⟩
      · obtain ⟨xo, hxo⟩ : ∃ xo, x = 2 * xo + 1 := by
          rcases Int.even_or_odd x with ⟨v, hv⟩ | ⟨v, hv⟩
          · exact absurd ⟨v, by linarith⟩ hx2
          · exact ⟨v, by linarith⟩
        have hexp : (2 : ℤ) * 2 ^ (k - 1) = 2 ^ k := by
          rw [← pow_succ']
          congr 1
          omega
        have hodd : ¬ 2 ∣ (x + 2 ^ (k - 1)) := by
          intro hc
          obtain ⟨v, hv⟩ := hc
          have h2p : (2 : ℤ) * 2 ^ (k - 2) = 2 ^ (k - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          exact hx2 ⟨v - 2 ^ (k - 2), by linarith⟩
        refine ⟨x + 2 ^ (k - 1), hodd, ?_⟩
        have hsplit : (x + 2 ^ (k - 1)) ^ 2 - a =
            (x ^ 2 - a) + 2 ^ k * x + (2 ^ (k - 1)) ^ 2 := by
          rw [← hexp]
          ring
        have hpow2 : ((2 : ℤ) ^ (k - 1)) ^ 2 = 2 ^ (k + 1) * 2 ^ (k - 3) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        have htx : t + x = 2 * (u + xo + 1) := by omega
        have hstep : (2 : ℤ) ^ k * (t + x) = 2 ^ (k + 1) * (u + xo + 1) := by
          rw [htx, pow_succ]
          ring
        refine ⟨u + xo + 1 + 2 ^ (k - 3), ?_⟩
        calc (x + 2 ^ (k - 1)) ^ 2 - a
            = (x ^ 2 - a) + 2 ^ k * x + (2 ^ (k - 1)) ^ 2 := hsplit
          _ = 2 ^ k * (t + x) + (2 ^ (k - 1)) ^ 2 := by rw [ht]; ring
          _ = 2 ^ (k + 1) * (u + xo + 1) + 2 ^ (k + 1) * 2 ^ (k - 3) := by
              rw [hstep, hpow2]
          _ = 2 ^ (k + 1) * (u + xo + 1 + 2 ^ (k - 3)) := by ring

private lemma seventeen_adic_square_lift (b a : ℤ) (hb : ¬ (17 : ℤ) ∣ b)
    (ha : ¬ (17 : ℤ) ∣ a) (h0 : ∃ x₀ : ℤ, (17 : ℤ) ∣ b * x₀ ^ 2 - a) :
    ∀ k : ℕ, ∃ x : ℤ, (17 ^ k : ℤ) ∣ b * x ^ 2 - a := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hx17 : ∀ x : ℤ, (17 : ℤ) ∣ b * x ^ 2 - a → ¬ (17 : ℤ) ∣ x := by
    intro x hdvd hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨t, ht⟩ := hdvd
    refine ha ⟨b * 17 * w ^ 2 - t, ?_⟩
    rw [hw] at ht
    linarith [ht]
  intro k
  induction k with
  | zero => obtain ⟨x₀, h₀⟩ := h0; exact ⟨x₀, one_dvd _⟩
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · obtain ⟨x₀, h₀⟩ := h0
      exact ⟨x₀, by simpa using h₀⟩
    · obtain ⟨x, t, ht⟩ := ih
      have hdvd1 : (17 : ℤ) ∣ b * x ^ 2 - a := by
        refine dvd_trans (dvd_pow_self 17 (by omega : k ≠ 0)) ⟨t, ht⟩
      have hxu := hx17 x hdvd1
      have h2x : ((2 * b * x : ℤ) : ZMod 17) ≠ 0 := by
        intro hc
        have hdd : ((17 : ℕ) : ℤ) ∣ 2 * b * x :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp hc
        have hdd' : (17 : ℤ) ∣ 2 * b * x := by exact_mod_cast hdd
        have hpz : Prime (17 : ℤ) := Nat.prime_iff_prime_int.mp (by norm_num)
        rcases hpz.dvd_mul.mp hdd' with hd2 | hdx
        · rcases hpz.dvd_mul.mp hd2 with hd2' | hdb
          · have h172 : (17 : ℤ) ∣ 2 := hd2'
            omega
          · exact hb hdb
        · exact hxu hdx
      set u : ZMod 17 := -(t : ZMod 17) / ((2 * b * x : ℤ) : ZMod 17) with hu
      have hval : ((u.val : ℕ) : ZMod 17) = u := ZMod.natCast_rightInverse u
      have hkey : (17 : ℤ) ∣ t + 2 * b * x * (u.val : ℤ) := by
        have hz : ((t + 2 * b * x * (u.val : ℤ) : ℤ) : ZMod 17) = 0 := by
          push_cast
          rw [hval, hu]
          field_simp
          push_cast
          ring
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp hz
        exact_mod_cast this
      obtain ⟨s, hs⟩ := hkey
      refine ⟨x + (u.val : ℤ) * 17 ^ k, ?_⟩
      refine ⟨s + 17 ^ (k - 1) * (b * (u.val : ℤ) ^ 2), ?_⟩
      have hexpand : b * (x + (u.val : ℤ) * 17 ^ k) ^ 2 - a =
          (b * x ^ 2 - a) + 17 ^ k * (t + 2 * b * x * (u.val : ℤ)) - 17 ^ k * t +
            17 ^ k * 17 ^ k * (b * (u.val : ℤ) ^ 2) := by
        ring
      have hpow2 : (17 : ℤ) ^ k * 17 ^ k = 17 ^ (k + 1) * 17 ^ (k - 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc b * (x + (u.val : ℤ) * 17 ^ k) ^ 2 - a
          = (b * x ^ 2 - a) + 17 ^ k * (t + 2 * b * x * (u.val : ℤ)) - 17 ^ k * t +
              17 ^ k * 17 ^ k * (b * (u.val : ℤ) ^ 2) := hexpand
        _ = 17 ^ k * (17 * s) + 17 ^ (k + 1) * 17 ^ (k - 1) * (b * (u.val : ℤ) ^ 2) := by
            rw [ht, hs, hpow2]
            ring
        _ = 17 ^ (k + 1) * (s + 17 ^ (k - 1) * (b * (u.val : ℤ) ^ 2)) := by
            rw [pow_succ]
            ring

/-- **THE INVISIBLE COSETS PASS EVERY TWO-ADIC FRAME**: for each of the three coset
representatives, fixed integer data solve the class system modulo `2^k` for every `k`,
with the leading entry odd — no congruence refusal at any two-adic depth exists. -/
theorem theInvisibleCosetsPassEveryTwoAdicFrame (k : ℕ) :
    (∃ C E F N : ℤ, ¬ 2 ∣ C ∧ (2 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 2 * E ^ 2) ∧
      (2 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 2 * F ^ 2)) ∧
    (∃ C E F N : ℤ, ¬ 2 ∣ C ∧ (2 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 17 * E ^ 2) ∧
      (2 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 17 * F ^ 2)) ∧
    (∃ C E F N : ℤ, ¬ 2 ∣ C ∧ (2 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 34 * E ^ 2) ∧
      (2 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 34 * F ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF2, hFd⟩ := two_adic_square_lift 33 (by norm_num) k
    refine ⟨7, 4, F, 1, by norm_num, ⟨0, by ring⟩, ?_⟩
    obtain ⟨t, ht⟩ := hFd
    exact ⟨-2 * t, by linarith [ht]⟩
  · obtain ⟨C, hC2, hCd⟩ := two_adic_square_lift 17 (by norm_num) k
    refine ⟨C, 1, 1, 0, hC2, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hCd
      exact ⟨t, by linarith [ht]⟩
    · obtain ⟨t, ht⟩ := hCd
      exact ⟨t, by linarith [ht]⟩
  · obtain ⟨C, hC2, hCd⟩ := two_adic_square_lift 17 (by norm_num) k
    refine ⟨C, 0, 1, 1, hC2, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hCd
      exact ⟨t, by linarith [ht]⟩
    · obtain ⟨t, ht⟩ := hCd
      exact ⟨t, by linarith [ht]⟩

/-- **THE INVISIBLE COSETS PASS EVERY SEVENTEEN-ADIC FRAME**: fixed integer data solve
each class system modulo `17^k` for every `k`, with a unit entry — no congruence refusal
at any seventeen-adic depth exists either.  With the two-adic statement and the sign law
admitting both slots positive, the twelve classes are invisible to every frame the
completed descents used. -/
theorem theInvisibleCosetsPassEverySeventeenAdicFrame (k : ℕ) :
    (∃ C E F N : ℤ, ¬ (17 : ℤ) ∣ C ∧ (17 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 2 * E ^ 2) ∧
      (17 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 2 * F ^ 2)) ∧
    (∃ C E F N : ℤ, ¬ (17 : ℤ) ∣ N ∧ (17 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 17 * E ^ 2) ∧
      (17 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 17 * F ^ 2)) ∧
    (∃ C E F N : ℤ, ¬ (17 : ℤ) ∣ N ∧ (17 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 34 * E ^ 2) ∧
      (17 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 34 * F ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨E, hEd⟩ := seventeen_adic_square_lift 2 49 (by norm_num) (by norm_num)
      ⟨4, by norm_num⟩ k
    refine ⟨7, E, E, 0, by norm_num, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hEd
      exact ⟨-t, by linarith [ht]⟩
    · obtain ⟨t, ht⟩ := hEd
      exact ⟨-t, by linarith [ht]⟩
  · obtain ⟨F, hFd⟩ := seventeen_adic_square_lift 1 18 (by norm_num) (by norm_num)
      ⟨1, by norm_num⟩ k
    refine ⟨17, 4, F, 1, by norm_num, ⟨0, by ring⟩, ?_⟩
    obtain ⟨t, ht⟩ := hFd
    exact ⟨-17 * t, by linarith [ht]⟩
  · obtain ⟨F, hFd⟩ := seventeen_adic_square_lift 1 13 (by norm_num) (by norm_num)
      ⟨8, by norm_num⟩ k
    refine ⟨17, 2, F, 3, by norm_num, ⟨0, by ring⟩, ?_⟩
    obtain ⟨t, ht⟩ := hFd
    exact ⟨-34 * t, by linarith [ht]⟩

/-! ## 6. The named-open second descent, and the exhibit -/

/-- **The three invisible cosets are globally refused** — no rational point has a face
in any of them.  *Classical: seventeen is not a congruent number and the refusal is a
Lind–Reichardt-type quartic-residue second descent, possible exactly because two is a
square but not a fourth power mod seventeen.  Open here; its falsifier is a point with
such a face.* -/
def TheInvisibleCosetsAreGloballyRefused : Prop :=
  ∀ P : (FamilyFace.E (17 : ℕ)).Point,
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) 2) ∧
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) 17) ∧
    ¬ (Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) 34)

/-- **THE OBSTRUCTION IS EXHIBITED**: the face image lies in the Selmer sixteen, the
four torsion classes are realized, and the twelve remaining classes pass every two-adic
and every seventeen-adic frame — a population locally admissible at every named frame
and every depth that the realized current is classically known never to reach.  Granted
the named-open global refusal, `Sel₂/image ≅ (ℤ/2)²` is the group `Ш(E₁₇)[2]` — the
Birch–Swinnerton-Dyer obstruction object with every local ingredient kernel-checked. -/
theorem theObstructionIsExhibited :
    (∀ P : (FamilyFace.E (17 : ℕ)).Point, ∃ d₁ d₂ : ℚ, SelmerSixteen d₁ d₂ ∧
      Descent.SqCls (FamilyFace.slotOne (17 : ℕ) P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo (17 : ℕ) P) d₂) ∧
    (∀ k : ℕ, ∃ C E F N : ℤ, ¬ 2 ∣ C ∧
      (2 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 2 * E ^ 2) ∧
      (2 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 2 * F ^ 2)) ∧
    (∀ k : ℕ, ∃ C E F N : ℤ, ¬ (17 : ℤ) ∣ C ∧
      (17 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - 2 * E ^ 2) ∧
      (17 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - 2 * F ^ 2)) :=
  ⟨theSeventeenFaceLiesInTheSelmerSixteen,
   fun k => (theInvisibleCosetsPassEveryTwoAdicFrame k).1,
   fun k => (theInvisibleCosetsPassEverySeventeenAdicFrame k).1⟩

end Soma.Holonics.Millennium.SeventeenObstruction
