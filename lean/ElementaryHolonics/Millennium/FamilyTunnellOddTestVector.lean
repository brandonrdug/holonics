import ElementaryHolonics.Millennium.FamilyTunnellThetaCarrier

/-!
# The complete Tunnell source is one odd-coordinate test vector

The level-four terms in the global Tunnell theta source are not independent
ternary species.  They are the even-second-coordinate slices of the thin and
thick lattices after the addressed change of variables

`(a,b,z) ↦ (b,2a,z)`.

This file constructs the finite bijections in both directions and returns the
complete level-128 coefficient as

`2 · #{Q_thick = n, y odd} - #{Q_thin = n, y odd}`.

The theorem is useful beyond a shorter formula.  It exhibits the source as one
2-adic test vector on the two ternary lattices.  Every odd-prime neighbor passage
must therefore preserve a declared parity aperture instead of transporting four
unrelated coefficient tables.  No modular-form library theorem is assumed here;
the equality is proved directly on the complete finite occurrence populations.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellOddTestVector

open Soma.Holonics.Millennium.LatticeCount
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier

/-! ## 1. The retained parity apertures -/

/-- The even second-coordinate slice of the thin lattice. -/
def evenSecondThinPopulation (n : ℕ) : Finset TernaryOccurrence :=
  (canonicalThinPopulation n).filter fun t => t.2.1 % 2 = 0

/-- The odd second-coordinate slice of the thin lattice. -/
def oddSecondThinPopulation (n : ℕ) : Finset TernaryOccurrence :=
  (canonicalThinPopulation n).filter fun t => t.2.1 % 2 ≠ 0

/-- The even second-coordinate slice of the thick lattice. -/
def evenSecondThickPopulation (n : ℕ) : Finset TernaryOccurrence :=
  (canonicalThickPopulation n).filter fun t => t.2.1 % 2 = 0

/-- The odd second-coordinate slice of the thick lattice. -/
def oddSecondThickPopulation (n : ℕ) : Finset TernaryOccurrence :=
  (canonicalThickPopulation n).filter fun t => t.2.1 % 2 ≠ 0

theorem mem_levelThinPopulation_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ levelThinPopulation n ↔
      (t.1 ∈ boxZ (Nat.sqrt n) ∧ t.2.1 ∈ boxZ (Nat.sqrt n) ∧
        t.2.2 ∈ boxZ (Nat.sqrt n)) ∧
      levelThinQuadraticForm t = (n : ℤ) := by
  simp [levelThinPopulation]

theorem mem_levelThickPopulation_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ levelThickPopulation n ↔
      (t.1 ∈ boxZ (Nat.sqrt n) ∧ t.2.1 ∈ boxZ (Nat.sqrt n) ∧
        t.2.2 ∈ boxZ (Nat.sqrt n)) ∧
      levelThickQuadraticForm t = (n : ℤ) := by
  simp [levelThickPopulation]

theorem mem_evenSecondThinPopulation_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ evenSecondThinPopulation n ↔
      t ∈ canonicalThinPopulation n ∧ t.2.1 % 2 = 0 := by
  simp [evenSecondThinPopulation]

theorem mem_evenSecondThickPopulation_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ evenSecondThickPopulation n ↔
      t ∈ canonicalThickPopulation n ∧ t.2.1 % 2 = 0 := by
  simp [evenSecondThickPopulation]

/-! ## 2. The addressed level-four/even-slice equivalences -/

private def levelToEvenSecond (t : TernaryOccurrence) : TernaryOccurrence :=
  (t.2.1, 2 * t.1, t.2.2)

private def evenSecondToLevel (t : TernaryOccurrence) : TernaryOccurrence :=
  (t.2.1 / 2, t.1, t.2.2)

/-- The level-four thin population and the even-second-coordinate thin slice are
the same addressed occurrence population after swapping the two planar axes and
doubling/halving the selected coordinate. -/
theorem levelThinPopulation_card_eq_evenSecondThinPopulation_card (n : ℕ) :
    (levelThinPopulation n).card = (evenSecondThinPopulation n).card := by
  classical
  refine Finset.card_nbij' levelToEvenSecond evenSecondToLevel ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ levelThinPopulation n at ht
    rw [mem_levelThinPopulation_iff] at ht
    change (y, 2 * x, z) ∈ evenSecondThinPopulation n
    rw [mem_evenSecondThinPopulation_iff,
      mem_thinCoefficientSourceFibre_iff]
    have hthin : 2 * y ^ 2 + (2 * x) ^ 2 + 8 * z ^ 2 = (n : ℤ) := by
      unfold levelThinQuadraticForm at ht
      nlinarith [ht.2]
    obtain ⟨hy, hx2, hz⟩ := theSolutionsAreTightlyBounded hthin
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, by simp⟩
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le,
        Int.abs_eq_natAbs]
      exact_mod_cast hy
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le,
        Int.abs_eq_natAbs]
      exact_mod_cast hx2
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le,
        Int.abs_eq_natAbs]
      exact_mod_cast hz
    · simpa [thinQuadraticForm] using hthin
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ evenSecondThinPopulation n at ht
    rw [mem_evenSecondThinPopulation_iff,
      mem_thinCoefficientSourceFibre_iff] at ht
    change (y / 2, x, z) ∈ levelThinPopulation n
    rw [mem_levelThinPopulation_iff]
    have hyMod : y % 2 = 0 := ht.2
    have hy : y = 2 * (y / 2) := by omega
    have hlevel :
        4 * (y / 2) ^ 2 + 2 * x ^ 2 + 8 * z ^ 2 = (n : ℤ) := by
      have hthin := ht.1.2
      unfold thinQuadraticForm at hthin
      rw [hy] at hthin
      nlinarith [hthin]
    refine ⟨⟨?_, ht.1.1.1, ht.1.1.2.2⟩, ?_⟩
    · have hybox : y ∈ boxZ (Nat.sqrt n) := ht.1.1.2.1
      rw [theReducibleBoxIsTheInterval, Finset.mem_Icc] at hybox ⊢
      omega
    · simpa [levelThinQuadraticForm] using hlevel
  · rintro ⟨x, y, z⟩ ht
    simp [levelToEvenSecond, evenSecondToLevel]
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ evenSecondThinPopulation n at ht
    rw [mem_evenSecondThinPopulation_iff] at ht
    have hyMod : y % 2 = 0 := ht.2
    have hy : y = 2 * (y / 2) := by omega
    simp [levelToEvenSecond, evenSecondToLevel, ← hy]

/-- The identical addressed rebase for the thick lattice. -/
theorem levelThickPopulation_card_eq_evenSecondThickPopulation_card (n : ℕ) :
    (levelThickPopulation n).card = (evenSecondThickPopulation n).card := by
  classical
  refine Finset.card_nbij' levelToEvenSecond evenSecondToLevel ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ levelThickPopulation n at ht
    rw [mem_levelThickPopulation_iff] at ht
    change (y, 2 * x, z) ∈ evenSecondThickPopulation n
    rw [mem_evenSecondThickPopulation_iff,
      mem_thickCoefficientSourceFibre_iff]
    have hthick : 2 * y ^ 2 + (2 * x) ^ 2 + 32 * z ^ 2 = (n : ℤ) := by
      unfold levelThickQuadraticForm at ht
      nlinarith [ht.2]
    have hthinAux : 2 * y ^ 2 + (2 * x) ^ 2 + 8 * (2 * z) ^ 2 = (n : ℤ) := by
      nlinarith [hthick]
    obtain ⟨hy, hx2, _hz2⟩ := theSolutionsAreTightlyBounded hthinAux
    refine ⟨⟨⟨?_, ?_, ht.1.2.2⟩, ?_⟩, by simp⟩
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le,
        Int.abs_eq_natAbs]
      exact_mod_cast hy
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le,
        Int.abs_eq_natAbs]
      exact_mod_cast hx2
    · simpa [thickQuadraticForm] using hthick
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ evenSecondThickPopulation n at ht
    rw [mem_evenSecondThickPopulation_iff,
      mem_thickCoefficientSourceFibre_iff] at ht
    change (y / 2, x, z) ∈ levelThickPopulation n
    rw [mem_levelThickPopulation_iff]
    have hyMod : y % 2 = 0 := ht.2
    have hy : y = 2 * (y / 2) := by omega
    have hlevel :
        4 * (y / 2) ^ 2 + 2 * x ^ 2 + 32 * z ^ 2 = (n : ℤ) := by
      have hthick := ht.1.2
      unfold thickQuadraticForm at hthick
      rw [hy] at hthick
      nlinarith [hthick]
    refine ⟨⟨?_, ht.1.1.1, ht.1.1.2.2⟩, ?_⟩
    · have hybox : y ∈ boxZ (Nat.sqrt n) := ht.1.1.2.1
      rw [theReducibleBoxIsTheInterval, Finset.mem_Icc] at hybox ⊢
      omega
    · simpa [levelThickQuadraticForm] using hlevel
  · rintro ⟨x, y, z⟩ ht
    simp [levelToEvenSecond, evenSecondToLevel]
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ evenSecondThickPopulation n at ht
    rw [mem_evenSecondThickPopulation_iff] at ht
    have hyMod : y % 2 = 0 := ht.2
    have hy : y = 2 * (y / 2) := by omega
    simp [levelToEvenSecond, evenSecondToLevel, ← hy]

/-! ## 3. The global source returned as one test vector -/

theorem evenSecondThin_card_add_oddSecondThin_card (n : ℕ) :
    (evenSecondThinPopulation n).card + (oddSecondThinPopulation n).card =
      (canonicalThinPopulation n).card := by
  simpa [evenSecondThinPopulation, oddSecondThinPopulation] using
    Finset.card_filter_add_card_filter_not
      (s := canonicalThinPopulation n) (fun t : TernaryOccurrence => t.2.1 % 2 = 0)

theorem evenSecondThick_card_add_oddSecondThick_card (n : ℕ) :
    (evenSecondThickPopulation n).card + (oddSecondThickPopulation n).card =
      (canonicalThickPopulation n).card := by
  simpa [evenSecondThickPopulation, oddSecondThickPopulation] using
    Finset.card_filter_add_card_filter_not
      (s := canonicalThickPopulation n) (fun t : TernaryOccurrence => t.2.1 % 2 = 0)

/-- **THE COMPLETE TUNNELL SOURCE IS ONE ODD-COORDINATE TEST VECTOR.**

The four-layer global coefficient is exactly the signed count on the retained odd
second-coordinate slices.  The discarded even slice is not forgotten: the two
explicit population bijections above are its reconstruction receipt. -/
theorem fullTunnellThetaCoefficient_eq_oddSecond_testVector (n : ℕ) :
    fullTunnellThetaCoefficient n =
      2 * ((oddSecondThickPopulation n).card : ℤ) -
        ((oddSecondThinPopulation n).card : ℤ) := by
  have hthinNat := evenSecondThin_card_add_oddSecondThin_card n
  have hthickNat := evenSecondThick_card_add_oddSecondThick_card n
  have hthin :
      ((evenSecondThinPopulation n).card : ℤ) +
          ((oddSecondThinPopulation n).card : ℤ) =
        ((canonicalThinPopulation n).card : ℤ) := by
    exact_mod_cast hthinNat
  have hthick :
      ((evenSecondThickPopulation n).card : ℤ) +
          ((oddSecondThickPopulation n).card : ℤ) =
        ((canonicalThickPopulation n).card : ℤ) := by
    exact_mod_cast hthickNat
  have hlevelThin :
      ((levelThinPopulation n).card : ℤ) =
        ((evenSecondThinPopulation n).card : ℤ) := by
    exact_mod_cast levelThinPopulation_card_eq_evenSecondThinPopulation_card n
  have hlevelThick :
      ((levelThickPopulation n).card : ℤ) =
        ((evenSecondThickPopulation n).card : ℤ) := by
    exact_mod_cast levelThickPopulation_card_eq_evenSecondThickPopulation_card n
  unfold fullTunnellThetaCoefficient tunnellThetaCoefficient
    thickThetaCoefficient thinThetaCoefficient levelThickCoefficient
    levelThinCoefficient
  rw [hlevelThin, hlevelThick]
  omega

/-- The formal source coefficient has the same exact test-vector return. -/
theorem coeff_tunnellThetaQExpansion_eq_oddSecond_testVector (n : ℕ) :
    PowerSeries.coeff n tunnellThetaQExpansion =
      2 * ((oddSecondThickPopulation n).card : ℤ) -
        ((oddSecondThinPopulation n).card : ℤ) := by
  rw [coeff_tunnellThetaQExpansion,
    fullTunnellThetaCoefficient_eq_oddSecond_testVector]

#print axioms levelThinPopulation_card_eq_evenSecondThinPopulation_card
#print axioms levelThickPopulation_card_eq_evenSecondThickPopulation_card
#print axioms fullTunnellThetaCoefficient_eq_oddSecond_testVector

end Soma.Holonics.Millennium.FamilyTunnellOddTestVector
