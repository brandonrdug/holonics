import ElementaryHolonics.Millennium.FamilyTunnellOddHeckeDoubleCount

/-!
# The two-class Brandt carrier beneath the Tunnell test vector

The odd-coordinate thin population has two exact third-coordinate charts.  Its
even-third chart is the thick diagonal lattice after `z ↦ 2z`.  Its odd-third
chart is the second lattice in the quaternionic genus, with norm form

`Q₂(x,y,z) = 2x² + 4y² + 4yz + 9z²
           = 2x² + (2y+z)² + 8z²`.

Consequently the complete integral Tunnell coefficient is the difference of two
same-genus lattice populations, rather than an unexplained difference between the
thin and thick diagonal presentations.  This is the correct two-coordinate Brandt
test vector on which the odd-prime neighbor action must be diagonalized.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector

open Finset
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier
open Soma.Holonics.Millennium.FamilyTunnellOddTestVector
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence
open Soma.Holonics.Millennium.FamilyTunnellOddHeckeDoubleCount

/-- The two parity charts inside the retained thin test-vector population. -/
def oddSecondThinEvenThirdPopulation (n : ℕ) : Finset IntTriple :=
  (oddSecondThinPopulation n).filter fun m => m.2.2 % 2 = 0

def oddSecondThinOddThirdPopulation (n : ℕ) : Finset IntTriple :=
  (oddSecondThinPopulation n).filter fun m => m.2.2 % 2 ≠ 0

theorem evenThird_card_add_oddThird_card (n : ℕ) :
    (oddSecondThinEvenThirdPopulation n).card +
      (oddSecondThinOddThirdPopulation n).card =
        (oddSecondThinPopulation n).card := by
  simpa [oddSecondThinEvenThirdPopulation, oddSecondThinOddThirdPopulation] using
    Finset.card_filter_add_card_filter_not
      (s := oddSecondThinPopulation n) (fun m : IntTriple => m.2.2 % 2 = 0)

/-- The first Brandt lattice, retained in the diagonal chart. -/
def brandtFirstQuadratic (m : IntTriple) : ℤ :=
  2 * m.1 ^ 2 + m.2.1 ^ 2 + 32 * m.2.2 ^ 2

abbrev brandtFirstPopulation := oddSecondThickPopulation

/-- The second integral ternary lattice in the same quaternionic genus. -/
def brandtSecondQuadratic (m : IntTriple) : ℤ :=
  2 * m.1 ^ 2 + 4 * m.2.1 ^ 2 + 4 * m.2.1 * m.2.2 + 9 * m.2.2 ^ 2

/-- Its completed-square chart is literally the thin diagonal form. -/
theorem brandtSecondQuadratic_completedSquare (m : IntTriple) :
    brandtSecondQuadratic m =
      2 * m.1 ^ 2 + (2 * m.2.1 + m.2.2) ^ 2 + 8 * m.2.2 ^ 2 := by
  unfold brandtSecondQuadratic
  ring

/-! ## The even-third thin chart is the first Brandt lattice -/

def thickToThinEven (m : IntTriple) : IntTriple :=
  (m.1, m.2.1, 2 * m.2.2)

def thinEvenToThick (m : IntTriple) : IntTriple :=
  (m.1, m.2.1, m.2.2 / 2)

theorem thinQuadratic_thickToThinEven (m : IntTriple) :
    intTunnellQuadratic 8 (thickToThinEven m) = intTunnellQuadratic 32 m := by
  simp [intTunnellQuadratic, thickToThinEven]
  ring

theorem thickQuadratic_thinEvenToThick {m : IntTriple} (hz : m.2.2 % 2 = 0) :
    intTunnellQuadratic 32 (thinEvenToThick m) = intTunnellQuadratic 8 m := by
  have hd : (2 : ℤ) ∣ m.2.2 := Int.dvd_iff_emod_eq_zero.mpr hz
  have hrecover : 2 * (m.2.2 / 2) = m.2.2 := by
    simpa [mul_comm] using Int.ediv_mul_cancel hd
  have hsquare := congrArg (fun z : ℤ => z ^ 2) hrecover
  simp only [intTunnellQuadratic, thinEvenToThick]
  nlinarith

theorem thinEvenToThick_thickToThinEven (m : IntTriple) :
    thinEvenToThick (thickToThinEven m) = m := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp [thinEvenToThick, thickToThinEven]

theorem thickToThinEven_thinEvenToThick {m : IntTriple} (hz : m.2.2 % 2 = 0) :
    thickToThinEven (thinEvenToThick m) = m := by
  have hd : (2 : ℤ) ∣ m.2.2 := Int.dvd_iff_emod_eq_zero.mpr hz
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simpa [thickToThinEven, thinEvenToThick, mul_comm] using Int.ediv_mul_cancel hd

/-- The first diagonal lattice is exactly the even-third thin chart, occurrence by
occurrence. -/
theorem oddSecondThinEvenThirdPopulation_eq_image_thick (n : ℕ) :
    oddSecondThinEvenThirdPopulation n =
      (oddSecondThickPopulation n).image thickToThinEven := by
  ext m
  constructor
  · intro hm
    have hm' : m ∈ oddSecondThinPopulation n ∧ m.2.2 % 2 = 0 := by
      simpa [oddSecondThinEvenThirdPopulation] using hm
    let u := thinEvenToThick m
    have huCanonical : u ∈ canonicalThickPopulation n := by
      rw [mem_canonicalThickPopulation_iff_intTunnellQuadratic,
        thickQuadratic_thinEvenToThick hm'.2]
      exact (mem_canonicalThinPopulation_iff_intTunnellQuadratic n m).mp
        ((Finset.mem_filter.mp hm'.1).1)
    have huOdd : u.2.1 % 2 ≠ 0 := by
      exact (Finset.mem_filter.mp hm'.1).2
    refine Finset.mem_image.mpr ⟨u, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨huCanonical, huOdd⟩
    · exact thickToThinEven_thinEvenToThick hm'.2
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨u, hu, rfl⟩
    have hu' : u ∈ canonicalThickPopulation n ∧ u.2.1 % 2 ≠ 0 :=
      Finset.mem_filter.mp hu
    have hthin : thickToThinEven u ∈ canonicalThinPopulation n := by
      rw [mem_canonicalThinPopulation_iff_intTunnellQuadratic,
        thinQuadratic_thickToThinEven,
        (mem_canonicalThickPopulation_iff_intTunnellQuadratic n u).mp hu'.1]
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hthin, hu'.2⟩
    · simp [thickToThinEven]

theorem thickToThinEven_injective : Function.Injective thickToThinEven := by
  intro a b hab
  have hreturn := congrArg thinEvenToThick hab
  simpa [thinEvenToThick_thickToThinEven] using hreturn

theorem oddSecondThinEvenThirdPopulation_card (n : ℕ) :
    (oddSecondThinEvenThirdPopulation n).card =
      (oddSecondThickPopulation n).card := by
  rw [oddSecondThinEvenThirdPopulation_eq_image_thick,
    Finset.card_image_of_injective _ thickToThinEven_injective]

/-! ## The odd-third thin chart is the second Brandt lattice -/

def thinOddToBrandtSecond (m : IntTriple) : IntTriple :=
  (m.1, (m.2.1 - m.2.2) / 2, m.2.2)

def brandtSecondToThin (m : IntTriple) : IntTriple :=
  (m.1, 2 * m.2.1 + m.2.2, m.2.2)

private theorem odd_difference_divisible {y z : ℤ}
    (hy : y % 2 ≠ 0) (hz : z % 2 ≠ 0) : (2 : ℤ) ∣ y - z := by
  rw [Int.dvd_iff_emod_eq_zero]
  omega

theorem brandtSecondToThin_thinOddToBrandtSecond {m : IntTriple}
    (hy : m.2.1 % 2 ≠ 0) (hz : m.2.2 % 2 ≠ 0) :
    brandtSecondToThin (thinOddToBrandtSecond m) = m := by
  have hd := odd_difference_divisible hy hz
  have hrecover : 2 * ((m.2.1 - m.2.2) / 2) + m.2.2 = m.2.1 := by
    have h := Int.ediv_mul_cancel hd
    nlinarith
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hrecover
    · rfl

theorem thinOddToBrandtSecond_brandtSecondToThin (m : IntTriple) :
    thinOddToBrandtSecond (brandtSecondToThin m) = m := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [thinOddToBrandtSecond, brandtSecondToThin]
    · rfl

theorem brandtSecondQuadratic_thinOddToBrandtSecond {m : IntTriple}
    (hy : m.2.1 % 2 ≠ 0) (hz : m.2.2 % 2 ≠ 0) :
    brandtSecondQuadratic (thinOddToBrandtSecond m) = intTunnellQuadratic 8 m := by
  have hreturn := brandtSecondToThin_thinOddToBrandtSecond hy hz
  have hcoordinate := congrArg (fun q : IntTriple => q.2.1) hreturn
  simp [brandtSecondToThin, thinOddToBrandtSecond] at hcoordinate
  have hsquare := congrArg (fun y : ℤ => y ^ 2) hcoordinate
  simp only [brandtSecondQuadratic, intTunnellQuadratic, thinOddToBrandtSecond]
  nlinarith

theorem thinQuadratic_brandtSecondToThin (m : IntTriple) :
    intTunnellQuadratic 8 (brandtSecondToThin m) = brandtSecondQuadratic m := by
  simp [intTunnellQuadratic, brandtSecondQuadratic, brandtSecondToThin]
  ring

/-- The finite second-class population is the transported odd-third chart. -/
def brandtSecondPopulation (n : ℕ) : Finset IntTriple :=
  (oddSecondThinOddThirdPopulation n).image thinOddToBrandtSecond

/-- This image definition loses no mathematical solutions: membership is exactly
the second norm equation together with the required odd local coordinate. -/
theorem mem_brandtSecondPopulation_iff (n : ℕ) (m : IntTriple) :
    m ∈ brandtSecondPopulation n ↔
      brandtSecondQuadratic m = (n : ℤ) ∧ m.2.2 % 2 ≠ 0 := by
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
    have ht' : t ∈ oddSecondThinPopulation n ∧ t.2.2 % 2 ≠ 0 := by
      simpa [oddSecondThinOddThirdPopulation] using ht
    have hty : t.2.1 % 2 ≠ 0 := (Finset.mem_filter.mp ht'.1).2
    refine ⟨?_, ht'.2⟩
    rw [brandtSecondQuadratic_thinOddToBrandtSecond hty ht'.2]
    exact (mem_canonicalThinPopulation_iff_intTunnellQuadratic n t).mp
      (Finset.mem_filter.mp ht'.1).1
  · rintro ⟨hnorm, hz⟩
    let t := brandtSecondToThin m
    have htCanonical : t ∈ canonicalThinPopulation n := by
      rw [mem_canonicalThinPopulation_iff_intTunnellQuadratic,
        thinQuadratic_brandtSecondToThin, hnorm]
    have hty : t.2.1 % 2 ≠ 0 := by
      have hmod : t.2.1 % 2 = m.2.2 % 2 := by
        simp [t, brandtSecondToThin, Int.add_emod, Int.mul_emod]
      rw [hmod]
      exact hz
    have ht : t ∈ oddSecondThinOddThirdPopulation n := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨htCanonical, hty⟩
      · simpa [t, brandtSecondToThin] using hz
    refine Finset.mem_image.mpr ⟨t, ht, ?_⟩
    exact thinOddToBrandtSecond_brandtSecondToThin m

theorem thinOddToBrandtSecond_injective_on (n : ℕ) :
    Set.InjOn thinOddToBrandtSecond (oddSecondThinOddThirdPopulation n : Set IntTriple) := by
  intro a ha b hb hab
  have ha' : a ∈ oddSecondThinPopulation n ∧ a.2.2 % 2 ≠ 0 := by
    simpa [oddSecondThinOddThirdPopulation] using ha
  have hb' : b ∈ oddSecondThinPopulation n ∧ b.2.2 % 2 ≠ 0 := by
    simpa [oddSecondThinOddThirdPopulation] using hb
  have hay : a.2.1 % 2 ≠ 0 := (Finset.mem_filter.mp ha'.1).2
  have hby : b.2.1 % 2 ≠ 0 := (Finset.mem_filter.mp hb'.1).2
  have hreturn := congrArg brandtSecondToThin hab
  simpa [brandtSecondToThin_thinOddToBrandtSecond hay ha'.2,
    brandtSecondToThin_thinOddToBrandtSecond hby hb'.2] using hreturn

theorem brandtSecondPopulation_card (n : ℕ) :
    (brandtSecondPopulation n).card =
      (oddSecondThinOddThirdPopulation n).card := by
  unfold brandtSecondPopulation
  exact Finset.card_image_iff.mpr (thinOddToBrandtSecond_injective_on n)

/-- The thin test-vector population is the disjoint union of the two Brandt
classes. -/
theorem oddSecondThin_card_eq_brandt_classes (n : ℕ) :
    (oddSecondThinPopulation n).card =
      (brandtFirstPopulation n).card + (brandtSecondPopulation n).card := by
  rw [← oddSecondThinEvenThirdPopulation_card n,
    brandtSecondPopulation_card, evenThird_card_add_oddThird_card]

/-- **THE TUNNELL COEFFICIENT IS THE TWO-CLASS BRANDT DIFFERENCE.** -/
theorem fullTunnellThetaCoefficient_eq_brandtDifference (n : ℕ) :
    fullTunnellThetaCoefficient n =
      ((brandtFirstPopulation n).card : ℤ) -
        ((brandtSecondPopulation n).card : ℤ) := by
  rw [fullTunnellThetaCoefficient_eq_oddSecond_testVector]
  have hsplit := oddSecondThin_card_eq_brandt_classes n
  have hsplitZ :
      ((oddSecondThinPopulation n).card : ℤ) =
        ((brandtFirstPopulation n).card : ℤ) +
          ((brandtSecondPopulation n).card : ℤ) := by
    exact_mod_cast hsplit
  rw [hsplitZ]
  ring

#print axioms oddSecondThinEvenThirdPopulation_card
#print axioms mem_brandtSecondPopulation_iff
#print axioms brandtSecondPopulation_card
#print axioms fullTunnellThetaCoefficient_eq_brandtDifference

end Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
