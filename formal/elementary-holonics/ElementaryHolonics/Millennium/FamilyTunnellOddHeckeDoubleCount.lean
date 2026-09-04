import ElementaryHolonics.Millennium.FamilyTunnellHeckeDoubleCount
import ElementaryHolonics.Millennium.FamilyTunnellOddTestVector
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The odd-coordinate Tunnell test vector under the neighbor double count

The complete Tunnell coefficient is not the unfiltered representation number of a
single ternary lattice.  It is the signed local test vector

`2 · #{thick : second coordinate odd} - #{thin : second coordinate odd}`.

This file retains that local aperture throughout the odd-prime neighbor
correspondence.  Coordinatewise multiplication by an odd prime preserves the
aperture exactly, so the zero-residue fibre reconstructs the odd-coordinate
quotient population rather than merely the unfiltered quotient population.  The
upper and lower branches are then reassembled into actual addressed neighbor
points and counted without assuming a modular-form eigenlaw.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellOddHeckeDoubleCount

open Finset
open NumberTheorySymbols
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier
open Soma.Holonics.Millennium.FamilyTunnellOddTestVector
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence
open Soma.Holonics.Millennium.FamilyTunnellHeckeDoubleCount

variable {p : ℕ} [Fact p.Prime]

/-- The retained two-adic aperture on an integral ternary occurrence. -/
def SecondCoordinateOdd (m : IntTriple) : Prop := m.2.1 % 2 ≠ 0

/-- Multiplication by an odd prime preserves, rather than approximates, the
second-coordinate aperture. -/
theorem secondCoordinateOdd_scale_iff (hp2 : p ≠ 2) (m : IntTriple) :
    SecondCoordinateOdd (scaleTripleByPrime (p := p) m) ↔
      SecondCoordinateOdd m := by
  have hpmod : (p : ℤ) % 2 = 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    rw [hk]
    push_cast
    simp [Int.add_emod]
  simp only [SecondCoordinateOdd, scaleTripleByPrime]
  rw [Int.mul_emod, hpmod, one_mul, Int.emod_emod]

private theorem mem_oddSecondThinPopulation_iff (n : ℕ) (m : IntTriple) :
    m ∈ oddSecondThinPopulation n ↔
      m ∈ canonicalThinPopulation n ∧ SecondCoordinateOdd m := by
  simp [oddSecondThinPopulation, SecondCoordinateOdd]

private theorem mem_oddSecondThickPopulation_iff (n : ℕ) (m : IntTriple) :
    m ∈ oddSecondThickPopulation n ↔
      m ∈ canonicalThickPopulation n ∧ SecondCoordinateOdd m := by
  simp [oddSecondThickPopulation, SecondCoordinateOdd]

/-- Exact quotient reconstruction on the thin odd-coordinate population. -/
theorem scalePredecessor_oddSecondThinPopulation (hp2 : p ≠ 2) (n : ℕ) :
    scalePredecessorPopulation (p := p)
        (oddSecondThinPopulation (p ^ 2 * n)) =
      oddSecondThinPopulation n := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨v, hv, hvm⟩
    have hv' : v ∈ oddSecondThinPopulation (p ^ 2 * n) ∧
        reduceTriple (p := p) v = 0 := by
      simpa [zeroResiduePopulation] using hv
    have hscale : scaleTripleByPrime (p := p) m = v := by
      rw [← hvm, scale_divideTripleByPrime (p := p) hv'.2]
    have hmCanonical : m ∈ canonicalThinPopulation n := by
      have hpred : m ∈ scalePredecessorPopulation (p := p)
          (canonicalThinPopulation (p ^ 2 * n)) := by
        refine Finset.mem_image.mpr ⟨v, ?_, hvm⟩
        simpa [zeroResiduePopulation] using
          And.intro ((mem_oddSecondThinPopulation_iff _ _).mp hv'.1).1 hv'.2
      simpa [scalePredecessor_canonicalThinPopulation (p := p) n] using hpred
    have hmOdd : SecondCoordinateOdd m := by
      apply (secondCoordinateOdd_scale_iff (p := p) hp2 m).mp
      rw [hscale]
      exact ((mem_oddSecondThinPopulation_iff _ _).mp hv'.1).2
    exact (mem_oddSecondThinPopulation_iff _ _).mpr ⟨hmCanonical, hmOdd⟩
  · intro hm
    have hm' := (mem_oddSecondThinPopulation_iff _ _).mp hm
    refine Finset.mem_image.mpr
      ⟨scaleTripleByPrime (p := p) m, ?_, divide_scaleTripleByPrime (p := p) m⟩
    simp only [zeroResiduePopulation, Finset.mem_filter]
    refine ⟨(mem_oddSecondThinPopulation_iff _ _).mpr ⟨?_, ?_⟩,
      reduce_scaleTripleByPrime (p := p) m⟩
    · rw [mem_canonicalThinPopulation_iff_intTunnellQuadratic,
        intTunnellQuadratic_scaleTripleByPrime,
        (mem_canonicalThinPopulation_iff_intTunnellQuadratic n m).mp hm'.1]
      norm_cast
    · exact (secondCoordinateOdd_scale_iff (p := p) hp2 m).mpr hm'.2

/-- Thick analogue of exact aperture-preserving quotient reconstruction. -/
theorem scalePredecessor_oddSecondThickPopulation (hp2 : p ≠ 2) (n : ℕ) :
    scalePredecessorPopulation (p := p)
        (oddSecondThickPopulation (p ^ 2 * n)) =
      oddSecondThickPopulation n := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨v, hv, hvm⟩
    have hv' : v ∈ oddSecondThickPopulation (p ^ 2 * n) ∧
        reduceTriple (p := p) v = 0 := by
      simpa [zeroResiduePopulation] using hv
    have hscale : scaleTripleByPrime (p := p) m = v := by
      rw [← hvm, scale_divideTripleByPrime (p := p) hv'.2]
    have hmCanonical : m ∈ canonicalThickPopulation n := by
      have hpred : m ∈ scalePredecessorPopulation (p := p)
          (canonicalThickPopulation (p ^ 2 * n)) := by
        refine Finset.mem_image.mpr ⟨v, ?_, hvm⟩
        simpa [zeroResiduePopulation] using
          And.intro ((mem_oddSecondThickPopulation_iff _ _).mp hv'.1).1 hv'.2
      simpa [scalePredecessor_canonicalThickPopulation (p := p) n] using hpred
    have hmOdd : SecondCoordinateOdd m := by
      apply (secondCoordinateOdd_scale_iff (p := p) hp2 m).mp
      rw [hscale]
      exact ((mem_oddSecondThickPopulation_iff _ _).mp hv'.1).2
    exact (mem_oddSecondThickPopulation_iff _ _).mpr ⟨hmCanonical, hmOdd⟩
  · intro hm
    have hm' := (mem_oddSecondThickPopulation_iff _ _).mp hm
    refine Finset.mem_image.mpr
      ⟨scaleTripleByPrime (p := p) m, ?_, divide_scaleTripleByPrime (p := p) m⟩
    simp only [zeroResiduePopulation, Finset.mem_filter]
    refine ⟨(mem_oddSecondThickPopulation_iff _ _).mpr ⟨?_, ?_⟩,
      reduce_scaleTripleByPrime (p := p) m⟩
    · rw [mem_canonicalThickPopulation_iff_intTunnellQuadratic,
        intTunnellQuadratic_scaleTripleByPrime,
        (mem_canonicalThickPopulation_iff_intTunnellQuadratic n m).mp hm'.1]
      norm_cast
    · exact (secondCoordinateOdd_scale_iff (p := p) hp2 m).mpr hm'.2

theorem zeroResidue_oddSecondThinPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (zeroResiduePopulation (p := p)
      (oddSecondThinPopulation (p ^ 2 * n))).card =
        (oddSecondThinPopulation n).card := by
  rw [← scalePredecessorPopulation_card,
    scalePredecessor_oddSecondThinPopulation (p := p) hp2]

theorem zeroResidue_oddSecondThickPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (zeroResiduePopulation (p := p)
      (oddSecondThickPopulation (p ^ 2 * n))).card =
        (oddSecondThickPopulation n).card := by
  rw [← scalePredecessorPopulation_card,
    scalePredecessor_oddSecondThickPopulation (p := p) hp2]

/-- The thin odd-coordinate zero fibre is present exactly on the divisible branch. -/
theorem zeroResidue_oddSecondThinPopulation_card_eq (hp2 : p ≠ 2) (n : ℕ) :
    (zeroResiduePopulation (p := p) (oddSecondThinPopulation n)).card =
      if p ^ 2 ∣ n then (oddSecondThinPopulation (n / p ^ 2)).card else 0 := by
  by_cases hdiv : p ^ 2 ∣ n
  · rw [if_pos hdiv]
    have hreturn : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
    have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    rw [← hreturn, zeroResidue_oddSecondThinPopulation_card (p := p) hp2,
      Nat.mul_div_cancel_left (n / p ^ 2) hp2pos]
  · rw [if_neg hdiv]
    have hcanonical := zeroResidue_canonicalThinPopulation_card_eq (p := p) n
    rw [if_neg hdiv] at hcanonical
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hm' : m ∈ oddSecondThinPopulation n ∧ reduceTriple (p := p) m = 0 := by
      simpa [zeroResiduePopulation] using hm
    have hmCanonical : m ∈ zeroResiduePopulation (p := p)
        (canonicalThinPopulation n) := by
      simpa [zeroResiduePopulation] using
        And.intro ((mem_oddSecondThinPopulation_iff _ _).mp hm'.1).1 hm'.2
    have hempty : zeroResiduePopulation (p := p) (canonicalThinPopulation n) = ∅ :=
      Finset.card_eq_zero.mp hcanonical
    rw [hempty] at hmCanonical
    simpa using hmCanonical

/-- Thick analogue of the exact odd-coordinate quotient branch. -/
theorem zeroResidue_oddSecondThickPopulation_card_eq (hp2 : p ≠ 2) (n : ℕ) :
    (zeroResiduePopulation (p := p) (oddSecondThickPopulation n)).card =
      if p ^ 2 ∣ n then (oddSecondThickPopulation (n / p ^ 2)).card else 0 := by
  by_cases hdiv : p ^ 2 ∣ n
  · rw [if_pos hdiv]
    have hreturn : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
    have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    rw [← hreturn, zeroResidue_oddSecondThickPopulation_card (p := p) hp2,
      Nat.mul_div_cancel_left (n / p ^ 2) hp2pos]
  · rw [if_neg hdiv]
    have hcanonical := zeroResidue_canonicalThickPopulation_card_eq (p := p) n
    rw [if_neg hdiv] at hcanonical
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hm' : m ∈ oddSecondThickPopulation n ∧ reduceTriple (p := p) m = 0 := by
      simpa [zeroResiduePopulation] using hm
    have hmCanonical : m ∈ zeroResiduePopulation (p := p)
        (canonicalThickPopulation n) := by
      simpa [zeroResiduePopulation] using
        And.intro ((mem_oddSecondThickPopulation_iff _ _).mp hm'.1).1 hm'.2
    have hempty : zeroResiduePopulation (p := p) (canonicalThickPopulation n) = ∅ :=
      Finset.card_eq_zero.mp hcanonical
    rw [hempty] at hmCanonical
    simpa using hmCanonical

private theorem zero_add_nonzero_card (s : Finset IntTriple) :
    (zeroResiduePopulation (p := p) s).card +
      (nonzeroResiduePopulation (p := p) s).card = s.card := by
  simpa [zeroResiduePopulation, nonzeroResiduePopulation] using
    Finset.card_filter_add_card_filter_not
      (s := s) (fun m : IntTriple => reduceTriple (p := p) m = 0)

/-- The lower incidence plate retains the thin odd-coordinate aperture. -/
theorem oddSecondThin_incidence_defect (hp2 : p ≠ 2) (n : ℕ) :
    ((integralOrthogonalIncidencePopulation (p := p) 8
        (oddSecondThinPopulation n)).card : ℤ) -
        ((oddSecondThinPopulation n).card : ℤ) =
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((oddSecondThinPopulation n).card : ℤ) +
        (p : ℤ) *
          (if p ^ 2 ∣ n then
            ((oddSecondThinPopulation (n / p ^ 2)).card : ℤ) else 0) := by
  have hnorm : ∀ m ∈ oddSecondThinPopulation n,
      intTunnellQuadratic 8 m = (n : ℤ) := by
    intro m hm
    exact (mem_canonicalThinPopulation_iff_intTunnellQuadratic n m).mp
      ((mem_oddSecondThinPopulation_iff _ _).mp hm).1
  have hinc := thin_incidence_middle_quotient_split (p := p) hp2
    (oddSecondThinPopulation n) (n : ℤ) hnorm
  have hpart := zero_add_nonzero_card (p := p) (oddSecondThinPopulation n)
  have hpartCast :
      ((zeroResiduePopulation (p := p) (oddSecondThinPopulation n)).card : ℤ) +
        ((nonzeroResiduePopulation (p := p) (oddSecondThinPopulation n)).card : ℤ) =
          ((oddSecondThinPopulation n).card : ℤ) := by
    exact_mod_cast hpart
  have hpartZ :
      ((nonzeroResiduePopulation (p := p) (oddSecondThinPopulation n)).card : ℤ) =
        ((oddSecondThinPopulation n).card : ℤ) -
          ((zeroResiduePopulation (p := p) (oddSecondThinPopulation n)).card : ℤ) := by
    omega
  rw [hinc, hpartZ, zeroResidue_oddSecondThinPopulation_card_eq (p := p) hp2]
  by_cases hdiv : p ^ 2 ∣ n
  · have hn0 : (n : ZMod p) = 0 := by
      obtain ⟨k, hk⟩ := hdiv
      rw [hk]
      simp
    simp [hdiv, hn0]
    ring
  · simp [hdiv]
    ring

/-- The lower incidence plate retains the thick odd-coordinate aperture. -/
theorem oddSecondThick_incidence_defect (hp2 : p ≠ 2) (n : ℕ) :
    ((integralOrthogonalIncidencePopulation (p := p) 32
        (oddSecondThickPopulation n)).card : ℤ) -
        ((oddSecondThickPopulation n).card : ℤ) =
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((oddSecondThickPopulation n).card : ℤ) +
        (p : ℤ) *
          (if p ^ 2 ∣ n then
            ((oddSecondThickPopulation (n / p ^ 2)).card : ℤ) else 0) := by
  have hnorm : ∀ m ∈ oddSecondThickPopulation n,
      intTunnellQuadratic 32 m = (n : ℤ) := by
    intro m hm
    exact (mem_canonicalThickPopulation_iff_intTunnellQuadratic n m).mp
      ((mem_oddSecondThickPopulation_iff _ _).mp hm).1
  have hinc := thick_incidence_middle_quotient_split (p := p) hp2
    (oddSecondThickPopulation n) (n : ℤ) hnorm
  have hpart := zero_add_nonzero_card (p := p) (oddSecondThickPopulation n)
  have hpartCast :
      ((zeroResiduePopulation (p := p) (oddSecondThickPopulation n)).card : ℤ) +
        ((nonzeroResiduePopulation (p := p) (oddSecondThickPopulation n)).card : ℤ) =
          ((oddSecondThickPopulation n).card : ℤ) := by
    exact_mod_cast hpart
  have hpartZ :
      ((nonzeroResiduePopulation (p := p) (oddSecondThickPopulation n)).card : ℤ) =
        ((oddSecondThickPopulation n).card : ℤ) -
          ((zeroResiduePopulation (p := p) (oddSecondThickPopulation n)).card : ℤ) := by
    omega
  rw [hinc, hpartZ, zeroResidue_oddSecondThickPopulation_card_eq (p := p) hp2]
  by_cases hdiv : p ^ 2 ∣ n
  · have hn0 : (n : ZMod p) = 0 := by
      obtain ⟨k, hk⟩ := hdiv
      rw [hk]
      simp
    simp [hdiv, hn0]
    ring
  · simp [hdiv]
    ring

/-! ## The upper line address with the aperture retained -/

abbrev OddSecondThinUpperOccurrence (n : ℕ) :=
  {m // m ∈ nonzeroResiduePopulation (p := p)
    (oddSecondThinPopulation (p ^ 2 * n))}

abbrev OddSecondThickUpperOccurrence (n : ℕ) :=
  {m // m ∈ nonzeroResiduePopulation (p := p)
    (oddSecondThickPopulation (p ^ 2 * n))}

def oddSecondThinUpperAsThin (n : ℕ)
    (m : OddSecondThinUpperOccurrence (p := p) n) :
    ThinUpperOccurrence (p := p) n := by
  refine ⟨m.1, ?_⟩
  have hm' : m.1 ∈ oddSecondThinPopulation (p ^ 2 * n) ∧
      reduceTriple (p := p) m.1 ≠ 0 := by
    simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
  simpa [nonzeroResiduePopulation] using
    And.intro ((mem_oddSecondThinPopulation_iff _ _).mp hm'.1).1 hm'.2

def oddSecondThickUpperAsThick (n : ℕ)
    (m : OddSecondThickUpperOccurrence (p := p) n) :
    ThickUpperOccurrence (p := p) n := by
  refine ⟨m.1, ?_⟩
  have hm' : m.1 ∈ oddSecondThickPopulation (p ^ 2 * n) ∧
      reduceTriple (p := p) m.1 ≠ 0 := by
    simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
  simpa [nonzeroResiduePopulation] using
    And.intro ((mem_oddSecondThickPopulation_iff _ _).mp hm'.1).1 hm'.2

def oddSecondThinUpperDirectedPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ProjectiveConicDirection ((8 : ℤ) : ZMod p) × IntTriple) :=
  (nonzeroResiduePopulation (p := p)
      (oddSecondThinPopulation (p ^ 2 * n))).attach.image fun m =>
    (thinUpperDirection hp2 n (oddSecondThinUpperAsThin n m), m.1)

def oddSecondThickUpperDirectedPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ProjectiveConicDirection ((32 : ℤ) : ZMod p) × IntTriple) :=
  (nonzeroResiduePopulation (p := p)
      (oddSecondThickPopulation (p ^ 2 * n))).attach.image fun m =>
    (thickUpperDirection hp2 n (oddSecondThickUpperAsThick n m), m.1)

theorem oddSecondThinUpperDirectedPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (oddSecondThinUpperDirectedPopulation (p := p) hp2 n).card =
      (nonzeroResiduePopulation (p := p)
        (oddSecondThinPopulation (p ^ 2 * n))).card := by
  unfold oddSecondThinUpperDirectedPopulation
  calc
    ((nonzeroResiduePopulation (p := p)
        (oddSecondThinPopulation (p ^ 2 * n))).attach.image fun m =>
          (thinUpperDirection hp2 n (oddSecondThinUpperAsThin n m), m.1)).card =
        (nonzeroResiduePopulation (p := p)
          (oddSecondThinPopulation (p ^ 2 * n))).attach.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      apply Subtype.ext
      exact congrArg Prod.snd hab
    _ = (nonzeroResiduePopulation (p := p)
          (oddSecondThinPopulation (p ^ 2 * n))).card := Finset.card_attach

theorem oddSecondThickUpperDirectedPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (oddSecondThickUpperDirectedPopulation (p := p) hp2 n).card =
      (nonzeroResiduePopulation (p := p)
        (oddSecondThickPopulation (p ^ 2 * n))).card := by
  unfold oddSecondThickUpperDirectedPopulation
  calc
    ((nonzeroResiduePopulation (p := p)
        (oddSecondThickPopulation (p ^ 2 * n))).attach.image fun m =>
          (thickUpperDirection hp2 n (oddSecondThickUpperAsThick n m), m.1)).card =
        (nonzeroResiduePopulation (p := p)
          (oddSecondThickPopulation (p ^ 2 * n))).attach.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      apply Subtype.ext
      exact congrArg Prod.snd hab
    _ = (nonzeroResiduePopulation (p := p)
          (oddSecondThickPopulation (p ^ 2 * n))).card := Finset.card_attach

private theorem upper_nonzero_card_oddSecondThin (hp2 : p ≠ 2) (n : ℕ) :
    ((nonzeroResiduePopulation (p := p)
      (oddSecondThinPopulation (p ^ 2 * n))).card : ℤ) =
      ((oddSecondThinPopulation (p ^ 2 * n)).card : ℤ) -
        ((oddSecondThinPopulation n).card : ℤ) := by
  have hpart := zero_add_nonzero_card (p := p)
    (oddSecondThinPopulation (p ^ 2 * n))
  have hpartZ :
      ((zeroResiduePopulation (p := p)
          (oddSecondThinPopulation (p ^ 2 * n))).card : ℤ) +
        ((nonzeroResiduePopulation (p := p)
          (oddSecondThinPopulation (p ^ 2 * n))).card : ℤ) =
        ((oddSecondThinPopulation (p ^ 2 * n)).card : ℤ) := by
    exact_mod_cast hpart
  rw [zeroResidue_oddSecondThinPopulation_card (p := p) hp2] at hpartZ
  omega

private theorem upper_nonzero_card_oddSecondThick (hp2 : p ≠ 2) (n : ℕ) :
    ((nonzeroResiduePopulation (p := p)
      (oddSecondThickPopulation (p ^ 2 * n))).card : ℤ) =
      ((oddSecondThickPopulation (p ^ 2 * n)).card : ℤ) -
        ((oddSecondThickPopulation n).card : ℤ) := by
  have hpart := zero_add_nonzero_card (p := p)
    (oddSecondThickPopulation (p ^ 2 * n))
  have hpartZ :
      ((zeroResiduePopulation (p := p)
          (oddSecondThickPopulation (p ^ 2 * n))).card : ℤ) +
        ((nonzeroResiduePopulation (p := p)
          (oddSecondThickPopulation (p ^ 2 * n))).card : ℤ) =
        ((oddSecondThickPopulation (p ^ 2 * n)).card : ℤ) := by
    exact_mod_cast hpart
  rw [zeroResidue_oddSecondThickPopulation_card (p := p) hp2] at hpartZ
  omega

abbrev OddSecondThinNeighborOccurrence := ThinNeighborNumeratorOccurrence (p := p)
abbrev OddSecondThickNeighborOccurrence := ThickNeighborNumeratorOccurrence (p := p)

/-- The complete aperture-preserving thin numerator carrier. -/
def oddSecondThinNeighborPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (OddSecondThinNeighborOccurrence (p := p)) :=
  (oddSecondThinUpperDirectedPopulation (p := p) hp2 n).disjSum
    (integralOrthogonalIncidencePopulation (p := p) 8 (oddSecondThinPopulation n))

/-- The complete aperture-preserving thick numerator carrier. -/
def oddSecondThickNeighborPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (OddSecondThickNeighborOccurrence (p := p)) :=
  (oddSecondThickUpperDirectedPopulation (p := p) hp2 n).disjSum
    (integralOrthogonalIncidencePopulation (p := p) 32 (oddSecondThickPopulation n))

/-! ## Every retained occurrence is still an actual neighbor point -/

def oddSecondThinNumeratorDirection (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThinNeighborPopulation (p := p) hp2 n}) :
    ProjectiveConicDirection ((8 : ℤ) : ZMod p) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper => exact upper.1
  | inr lower =>
      apply incidenceProjectiveDirection (p := p) 8 (oddSecondThinPopulation n)
      exact ⟨lower, by simpa [oddSecondThinNeighborPopulation] using hq⟩

def oddSecondThickNumeratorDirection (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThickNeighborPopulation (p := p) hp2 n}) :
    ProjectiveConicDirection ((32 : ℤ) : ZMod p) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper => exact upper.1
  | inr lower =>
      apply incidenceProjectiveDirection (p := p) 32 (oddSecondThickPopulation n)
      exact ⟨lower, by simpa [oddSecondThickNeighborPopulation] using hq⟩

def oddSecondThinNumeratorPoint (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThinNeighborPopulation (p := p) hp2 n}) : RatTriple :=
  match q.1 with
  | .inl upper =>
      ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)
  | .inr lower => intTripleToRat lower.1

def oddSecondThickNumeratorPoint (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThickNeighborPopulation (p := p) hp2 n}) : RatTriple :=
  match q.1 with
  | .inl upper =>
      ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)
  | .inr lower => intTripleToRat lower.1

theorem oddSecondThinNumeratorPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThinNeighborPopulation (p := p) hp2 n}) :
    oddSecondThinNumeratorPoint hp2 n q ∈
      integralNeighbor (p := p) 8 (oddSecondThinNumeratorDirection hp2 n q) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ oddSecondThinUpperDirectedPopulation (p := p) hp2 n := by
        simpa [oddSecondThinNeighborPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      subst upper
      simpa [oddSecondThinNumeratorPoint, oddSecondThinNumeratorDirection, oddSecondThinUpperAsThin] using
        thinUpperScaledPoint_mem_integralNeighbor hp2 n
          (oddSecondThinUpperAsThin n m)
  | inr lower =>
      apply incidenceVector_mem_integralNeighbor hp2 8 (oddSecondThinPopulation n)
        ⟨lower, by simpa [oddSecondThinNeighborPopulation] using hq⟩

theorem oddSecondThickNumeratorPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThickNeighborPopulation (p := p) hp2 n}) :
    oddSecondThickNumeratorPoint hp2 n q ∈
      integralNeighbor (p := p) 32 (oddSecondThickNumeratorDirection hp2 n q) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ oddSecondThickUpperDirectedPopulation (p := p) hp2 n := by
        simpa [oddSecondThickNeighborPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      subst upper
      simpa [oddSecondThickNumeratorPoint, oddSecondThickNumeratorDirection, oddSecondThickUpperAsThick] using
        thickUpperScaledPoint_mem_integralNeighbor hp2 n
          (oddSecondThickUpperAsThick n m)
  | inr lower =>
      apply incidenceVector_mem_integralNeighbor hp2 32 (oddSecondThickPopulation n)
        ⟨lower, by simpa [oddSecondThickNeighborPopulation] using hq⟩

theorem oddSecondThinNumeratorPoint_norm (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThinNeighborPopulation (p := p) hp2 n}) :
    ratTunnellQuadratic 8 (oddSecondThinNumeratorPoint hp2 n q) = (n : ℚ) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ oddSecondThinUpperDirectedPopulation (p := p) hp2 n := by
        simpa [oddSecondThinNeighborPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      have hmOdd : m.1 ∈ oddSecondThinPopulation (p ^ 2 * n) := by
        have hm' : m.1 ∈ oddSecondThinPopulation (p ^ 2 * n) ∧
            reduceTriple (p := p) m.1 ≠ 0 := by
          simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
        exact hm'.1
      have hnorm := (mem_canonicalThinPopulation_iff_intTunnellQuadratic
        (p ^ 2 * n) m.1).mp ((mem_oddSecondThinPopulation_iff _ _).mp hmOdd).1
      change ratTunnellQuadratic 8
        (ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)) = (n : ℚ)
      rw [← hmu, ratTunnellQuadratic_scaled_intTriple, hnorm]
      have hpQ : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      push_cast
      field_simp [hpQ]
  | inr lower =>
      have hl : lower ∈ integralOrthogonalIncidencePopulation (p := p) 8
          (oddSecondThinPopulation n) := by
        simpa [oddSecondThinNeighborPopulation] using hq
      have hl' := hl
      simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
        Finset.mem_product] at hl'
      change ratTunnellQuadratic 8 (intTripleToRat lower.1) = (n : ℚ)
      rw [ratTunnellQuadratic_intTripleToRat,
        (mem_canonicalThinPopulation_iff_intTunnellQuadratic n lower.1).mp
          ((mem_oddSecondThinPopulation_iff _ _).mp hl'.1.1).1]
      norm_cast

theorem oddSecondThickNumeratorPoint_norm (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ oddSecondThickNeighborPopulation (p := p) hp2 n}) :
    ratTunnellQuadratic 32 (oddSecondThickNumeratorPoint hp2 n q) = (n : ℚ) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ oddSecondThickUpperDirectedPopulation (p := p) hp2 n := by
        simpa [oddSecondThickNeighborPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      have hmOdd : m.1 ∈ oddSecondThickPopulation (p ^ 2 * n) := by
        have hm' : m.1 ∈ oddSecondThickPopulation (p ^ 2 * n) ∧
            reduceTriple (p := p) m.1 ≠ 0 := by
          simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
        exact hm'.1
      have hnorm := (mem_canonicalThickPopulation_iff_intTunnellQuadratic
        (p ^ 2 * n) m.1).mp ((mem_oddSecondThickPopulation_iff _ _).mp hmOdd).1
      change ratTunnellQuadratic 32
        (ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)) = (n : ℚ)
      rw [← hmu, ratTunnellQuadratic_scaled_intTriple, hnorm]
      have hpQ : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      push_cast
      field_simp [hpQ]
  | inr lower =>
      have hl : lower ∈ integralOrthogonalIncidencePopulation (p := p) 32
          (oddSecondThickPopulation n) := by
        simpa [oddSecondThickNeighborPopulation] using hq
      have hl' := hl
      simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
        Finset.mem_product] at hl'
      change ratTunnellQuadratic 32 (intTripleToRat lower.1) = (n : ℚ)
      rw [ratTunnellQuadratic_intTripleToRat,
        (mem_canonicalThickPopulation_iff_intTunnellQuadratic n lower.1).mp
          ((mem_oddSecondThickPopulation_iff _ _).mp hl'.1.1).1]
      norm_cast

/-- Exact thin three-term Hecke count with the two-adic aperture retained. -/
theorem oddSecondThinNeighborPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    ((oddSecondThinNeighborPopulation (p := p) hp2 n).card : ℤ) =
      ((oddSecondThinPopulation (p ^ 2 * n)).card : ℤ) +
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((oddSecondThinPopulation n).card : ℤ) +
      (p : ℤ) *
        (if p ^ 2 ∣ n then
          ((oddSecondThinPopulation (n / p ^ 2)).card : ℤ) else 0) := by
  rw [oddSecondThinNeighborPopulation, Finset.card_disjSum, Int.natCast_add,
    oddSecondThinUpperDirectedPopulation_card,
    upper_nonzero_card_oddSecondThin (p := p) hp2]
  have hinc := oddSecondThin_incidence_defect (p := p) hp2 n
  linear_combination hinc

/-- Exact thick three-term Hecke count with the two-adic aperture retained. -/
theorem oddSecondThickNeighborPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    ((oddSecondThickNeighborPopulation (p := p) hp2 n).card : ℤ) =
      ((oddSecondThickPopulation (p ^ 2 * n)).card : ℤ) +
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((oddSecondThickPopulation n).card : ℤ) +
      (p : ℤ) *
        (if p ^ 2 ∣ n then
          ((oddSecondThickPopulation (n / p ^ 2)).card : ℤ) else 0) := by
  rw [oddSecondThickNeighborPopulation, Finset.card_disjSum, Int.natCast_add,
    oddSecondThickUpperDirectedPopulation_card,
    upper_nonzero_card_oddSecondThick (p := p) hp2]
  have hinc := oddSecondThick_incidence_defect (p := p) hp2 n
  linear_combination hinc

/-- The signed neighbor return of the actual Tunnell test vector. -/
def oddTunnellNeighborReturn (hp2 : p ≠ 2) (n : ℕ) : ℤ :=
  2 * (oddSecondThickNeighborPopulation (p := p) hp2 n).card -
    (oddSecondThinNeighborPopulation (p := p) hp2 n).card

/-- **THE COMPLETE TUNNELL TEST VECTOR RETURNS THE EXACT THREE-TERM SOURCE
CURRENT.**  This is the source half of the Hecke eigenlaw, before identifying the
returned neighbor class current with the Gaussian eigenvalue. -/
theorem oddTunnellNeighborReturn_eq_threeTerm (hp2 : p ≠ 2) (n : ℕ) :
    oddTunnellNeighborReturn (p := p) hp2 n =
      fullTunnellThetaCoefficient (p ^ 2 * n) +
      quadraticChar (ZMod p) (-(n : ZMod p)) * fullTunnellThetaCoefficient n +
      (p : ℤ) *
        (if p ^ 2 ∣ n then fullTunnellThetaCoefficient (n / p ^ 2) else 0) := by
  rw [oddTunnellNeighborReturn,
    oddSecondThinNeighborPopulation_card (p := p) hp2,
    oddSecondThickNeighborPopulation_card (p := p) hp2]
  simp only [fullTunnellThetaCoefficient_eq_oddSecond_testVector]
  by_cases hdiv : p ^ 2 ∣ n <;> simp [hdiv] <;> ring

/-- At a prime denominator the finite-field quadratic character is exactly the
Jacobi symbol used by the half-integral Hecke operator. -/
theorem quadraticChar_eq_jacobiSym (a : ℤ) :
    quadraticChar (ZMod p) (a : ZMod p) = jacobiSym a p := by
  rw [← jacobiSym.legendreSym.to_jacobiSym p a]
  rfl

theorem oddTunnellNeighborReturn_eq_integralHeckeSource (hp2 : p ≠ 2) (n : ℕ) :
    oddTunnellNeighborReturn (p := p) hp2 n =
      fullTunnellThetaCoefficient (p ^ 2 * n) +
      jacobiSym (-(n : ℤ)) p * fullTunnellThetaCoefficient n +
      (p : ℤ) *
        (if p ^ 2 ∣ n then fullTunnellThetaCoefficient (n / p ^ 2) else 0) := by
  rw [oddTunnellNeighborReturn_eq_threeTerm]
  have hchar := quadraticChar_eq_jacobiSym (p := p) (-(n : ℤ))
  have hchar' : quadraticChar (ZMod p) (-(n : ZMod p)) =
      jacobiSym (-(n : ℤ)) p := by simpa using hchar
  rw [hchar']

#print axioms secondCoordinateOdd_scale_iff
#print axioms scalePredecessor_oddSecondThinPopulation
#print axioms scalePredecessor_oddSecondThickPopulation
#print axioms oddSecondThinNeighborPopulation_card
#print axioms oddSecondThickNeighborPopulation_card
#print axioms oddTunnellNeighborReturn_eq_integralHeckeSource
#print axioms oddSecondThinNumeratorPoint_mem_integralNeighbor
#print axioms oddSecondThickNumeratorPoint_norm

end Soma.Holonics.Millennium.FamilyTunnellOddHeckeDoubleCount
