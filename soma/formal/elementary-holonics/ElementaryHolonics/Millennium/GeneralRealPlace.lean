import ElementaryHolonics.Millennium.GeneralTwoTorsion
import ElementaryHolonics.Millennium.SelmerCalculus

/-!
# GeneralRealPlace: the archimedean receiver, constructed

`SelmerCalculus` supplied the calculus of a receiver family and left the arithmetic
instances open.  This file constructs the **first one**, and it is the place that needs
no `ℚ_p`: the real place.

The condition is elementary and has been doing work implicitly throughout the descent.
An affine point has `y² = x(x−a)(x−b)`, so the product of the three slot values is a
square and in particular **nonnegative** — that is the whole archimedean condition.
Its bite comes from the ordering of the roots:

* **`theArchimedeanCondition`** — the product of the three slots is nonnegative.
* **`theRealPlaceCutsTheFirstSlot`** — when `0 < a < b`, every affine point off the
  two-torsion has **positive** abscissa, because a nonpositive one would make the
  product nonpositive.  So every class with a negative first slot is refused **by the
  real place alone**, before any finite prime is consulted.
* **`theFirstSlotIsPositive`** — read on the slot itself, conventions included.

This is one place of the family.  The finite places need `ℚ_p`-points of the descent
torsors and remain open.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralRealPlace

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

variable {a b : ℚ}

/-! ## 1. The archimedean condition -/

/-- **THE ARCHIMEDEAN CONDITION**: the three slot values multiply to a square, hence to
a nonnegative rational.  This is the local condition at the real place, and it is the
only one that needs no completion to state. -/
theorem theArchimedeanCondition {x y : ℚ} (h : y ^ 2 = x * (x - a) * (x - b)) :
    0 ≤ x * (x - a) * (x - b) := by
  rw [← h]
  positivity

/-- **THE REAL PLACE CUTS THE FIRST SLOT**: when the roots are ordered `0 < a < b`,
every affine point with nonzero ordinate has positive abscissa. -/
theorem theRealPlaceCutsTheFirstSlot (h0a : 0 < a) (hab : a < b) {x y : ℚ}
    (h : y ^ 2 = x * (x - a) * (x - b)) (hy : y ≠ 0) : 0 < x := by
  have hpos : 0 < x * (x - a) * (x - b) := by
    rw [← h]
    exact (sq_nonneg y).lt_of_ne fun hc =>
      hy (pow_eq_zero_iff two_ne_zero |>.mp hc.symm)
  by_contra hle
  push_neg at hle
  have h1 : x - a < 0 := by linarith
  have h2 : x - b < 0 := by linarith
  have hprod : 0 < (x - a) * (x - b) := mul_pos_of_neg_of_neg h1 h2
  have : x * ((x - a) * (x - b)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hprod.le
  nlinarith [hpos, this]

/-- **THE FIRST SLOT VALUE IS POSITIVE**: read on the slot itself, conventions
included.  At `(0,0)` the convention is `ab`, positive under the ordering. -/
theorem theFirstSlotIsPositive (h0a : 0 < a) (hab : a < b) {x y : ℚ}
    (hns : (E a b).Nonsingular x y) :
    0 < slotOne a b (Point.some _ _ hns) := by
  rw [slotOne_some]
  split_ifs with hx0
  · have hb0 : 0 < b := by linarith
    exact mul_pos h0a hb0
  · by_cases hy : y = 0
    · have hcurve := onCurve hns
      rw [hy] at hcurve
      have hroots : x * (x - a) * (x - b) = 0 := by linear_combination -hcurve
      rcases mul_eq_zero.mp hroots with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hx0
        · have hxa : x = a := by linarith [sub_eq_zero.mp h'']
          rw [hxa]
          exact h0a
      · have hxb : x = b := by linarith [sub_eq_zero.mp h']
        rw [hxb]
        linarith
    · exact theRealPlaceCutsTheFirstSlot h0a hab (onCurve hns) hy


/-! ## 2. The refusal, on classes -/

open Soma.Holonics.Millennium.GeneralSupport

/-- **THE REAL PLACE REFUSES EVERY NEGATIVE FIRST CLASS**: under the ordering
`0 < a < b`, the first slot class of every rational point is **positive**.  So a
class with a negative first component lies outside the descent image, refused by the
archimedean receiver alone — no finite prime is consulted. -/
theorem theRealPlaceRefusesEveryNegativeFirstClass {a b : ℤ}
    (h0a : (0 : ℚ) < (a : ℚ)) (hab : ((a : ℚ)) < ((b : ℚ)))
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) {d : ℤ}
    (hcls : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) ((d : ℤ) : ℚ))
    (hd : d < 0) : False := by
  rcases P with _ | @⟨x, y, hns⟩
  · -- the identity has first slot `1`
    obtain ⟨c, hc, hval⟩ := hcls
    have h1 : slotOne ((a : ℚ)) ((b : ℚ)) 0 = 1 := rfl
    rw [← Point.zero_def, h1] at hval
    have hdq : ((d : ℤ) : ℚ) < 0 := by exact_mod_cast hd
    have hcsq : 0 < c ^ 2 := by positivity
    nlinarith [hval, hdq, hcsq]
  · have hpos := theFirstSlotIsPositive h0a hab hns
    obtain ⟨c, hc, hval⟩ := hcls
    have hdq : ((d : ℤ) : ℚ) < 0 := by exact_mod_cast hd
    have hcsq : 0 < c ^ 2 := by positivity
    nlinarith [hpos, hval, hdq, hcsq]

/-- **THE ARCHIMEDEAN RECEIVER, AS A RECEIVER**: the classes the real place admits
form a set containing every realized class.  This is `SelmerCalculus`'s hypothesis
`hloc` discharged at one place — the first arithmetic instance of the family. -/
theorem theArchimedeanReceiverAdmitsTheDescentImage {a b : ℤ}
    (h0a : (0 : ℚ) < (a : ℚ)) (hab : ((a : ℚ)) < ((b : ℚ)))
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) {d : ℤ}
    (hcls : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) ((d : ℤ) : ℚ))
    (hd0 : d ≠ 0) : 0 < d := by
  rcases lt_trichotomy d 0 with h | h | h
  · exact absurd (theRealPlaceRefusesEveryNegativeFirstClass h0a hab P hcls h) (by simp)
  · exact absurd h hd0
  · exact h


/-! ## 3. The good finite places, already constructed

The support theorem is not only a finiteness statement — it **is** the collection of
local conditions at the good primes.  A prime missing the discriminant admits only
`p`-free classes, and that is exactly what `GeneralSupport` proves. -/

/-- **THE GOOD-PLACE RECEIVERS ADMIT THE DESCENT IMAGE**: at every prime missing
`a·b·(a−b)`, a realized class is a unit.  The support bound restated as a receiver. -/
theorem theGoodPlaceReceiverAdmitsTheDescentImage {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a - b ≠ 0) (P : (E ((a : ℚ)) ((b : ℚ))).Point) {l : ℕ} (hl : l.Prime)
    (hgood : ¬ (l : ℤ) ∣ a * b * (a - b)) :
    ∃ d₁ d₂ : ℤ, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      ¬ (l : ℤ) ∣ d₁ ∧ ¬ (l : ℤ) ∣ d₂ ∧
      Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) (d₁ : ℚ) ∧
      Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) P) (d₂ : ℚ) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨d₁, d₂, h10, h20, h1d, h2d, hs1, hs2⟩ :=
    theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve ha hb hab P
  refine ⟨d₁, d₂, h10, h20, ?_, ?_, hs1, hs2⟩
  · intro hc
    refine hgood ?_
    have hnat : l ∣ d₁.natAbs := by
      rwa [FamilyGenocchi.int_dvd_natAbs] at hc
    exact FamilyGenocchi.int_dvd_natAbs.mpr (Nat.dvd_trans hnat h1d)
  · intro hc
    refine hgood ?_
    have hnat : l ∣ d₂.natAbs := by
      rwa [FamilyGenocchi.int_dvd_natAbs] at hc
    exact FamilyGenocchi.int_dvd_natAbs.mpr (Nat.dvd_trans hnat h2d)

/-- **THE RECEIVER FAMILY IS COMPLETE AWAY FROM THE DISCRIMINANT**: the real place is
constructed, every prime missing `a·b·(a−b)` is constructed, and what remains is the
**finitely many** primes dividing it.  That is the exact shape of the open work: not a
family of conditions but a finite list of them. -/
theorem theReceiverFamilyIsCompleteAwayFromTheDiscriminant {a b : ℤ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ≠ 0)
    (h0a : (0 : ℚ) < (a : ℚ)) (hlt : ((a : ℚ)) < ((b : ℚ)))
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    (∀ d : ℤ, d ≠ 0 → Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) ((d : ℤ) : ℚ) →
      0 < d) ∧
    (∀ l : ℕ, l.Prime → ¬ (l : ℤ) ∣ a * b * (a - b) →
      ∃ d₁ d₂ : ℤ, ¬ (l : ℤ) ∣ d₁ ∧ ¬ (l : ℤ) ∣ d₂ ∧
        Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) (d₁ : ℚ) ∧
        Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) P) (d₂ : ℚ)) := by
  refine ⟨fun d hd0 hcls =>
    theArchimedeanReceiverAdmitsTheDescentImage h0a hlt P hcls hd0, fun l hl hgood => ?_⟩
  obtain ⟨d₁, d₂, -, -, hn1, hn2, hs1, hs2⟩ :=
    theGoodPlaceReceiverAdmitsTheDescentImage ha hb hab P hl hgood
  exact ⟨d₁, d₂, hn1, hn2, hs1, hs2⟩

end Soma.Holonics.Millennium.GeneralRealPlace
