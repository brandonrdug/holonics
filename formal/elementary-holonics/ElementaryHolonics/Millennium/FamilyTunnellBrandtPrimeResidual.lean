import ElementaryHolonics.Millennium.FamilyTunnellMiddleZeroDirections
import ElementaryHolonics.Millennium.FamilyTunnellHeckeDoubleCount

/-!
# The exact odd-prime residual of the Tunnell--Brandt eigenlaw

The preceding constructions have reduced the odd-prime Brandt action to two
finite populations belonging to the first lattice:

* primitive integral vectors with `Q₁(m)=p²`, and
* projective neighbor directions with zero middle coordinate.

The latter population has already been proved to have signed cardinality
`1 + χ(-1)`.  This file performs the exact composition.  It identifies the
Brandt eigenvalue statement with one, and only one, remaining primitive census
identity and then replaces the Hecke coordinate by the already proved
Frobenius trace of `y²=x³-x`.

No theorem is postulated here.  In particular `primitiveTraceDefect` is the
retained obstruction, not a Boolean promise that the missing correspondence
exists.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual

open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
open Soma.Holonics.Millennium.FamilyTunnellMiddleZeroDirections
open Soma.Holonics.Millennium.FamilyTunnellHeckeDoubleCount
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.GaussCoefficient

variable {p : ℕ} [Fact p.Prime]

/-! ## The signed expression is the face of an actual neighbor population -/

/-- The first Brandt lattice has exactly its two oriented middle-axis points at
norm one, now as an equality of complete finite populations. -/
theorem canonicalThickPopulation_one_eq_pair :
    canonicalThickPopulation 1 = {(0, 1, 0), (0, -1, 0)} := by
  ext m
  rw [mem_canonicalThickPopulation_iff_intTunnellQuadratic]
  change brandtFirstQuadratic m = 1 ↔ _
  rw [brandtFirstQuadratic_eq_one_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem canonicalThickPopulation_one_card :
    (canonicalThickPopulation 1).card = 2 := by
  rw [canonicalThickPopulation_one_eq_pair]
  norm_num

/-- The complete addressed norm-one numerator population across all first-lattice
`p`-neighbors.  Its upper branch consists of primitive `Q₁=p²` numerators; its
lower branch consists of the original two units paired with every admitted
orthogonal direction. -/
def firstNormOneNeighborPopulation (hp2 : p ≠ 2) :=
  thickNeighborNumeratorPopulation (p := p) hp2 1

/-- The actual norm-one neighbor population has exactly the primitive sheets plus
twice the middle-zero boundary. -/
theorem firstNormOneNeighborPopulation_card (hp2 : p ≠ 2) :
    ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) =
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) +
        2 * ((middleZeroDirections (p := p)).card : ℤ) := by
  have hnot : ¬p ^ 2 ∣ 1 := by
    intro h
    have hp2one : p ^ 2 = 1 := Nat.eq_one_of_dvd_one h
    have hpgt : 1 < p := (Fact.out : p.Prime).one_lt
    nlinarith
  have hcount := thickNeighborNumeratorPopulation_card (p := p) hp2 1
  rw [Nat.mul_one, if_neg hnot, canonicalThickPopulation_one_card] at hcount
  have hcount' :
      ((thickNeighborNumeratorPopulation (p := p) hp2 1).card : ℤ) =
        ((canonicalThickPopulation (p ^ 2)).card : ℤ) +
          quadraticChar (ZMod p) (-1) * 2 := by
    simpa using hcount
  have hpartNat := primitive_card_add_two_eq_complete_card (p := p)
  have hpart :
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) + 2 =
        ((canonicalThickPopulation (p ^ 2)).card : ℤ) := by
    exact_mod_cast hpartNat
  have hmiddle := middleZeroDirections_card_cast (p := p) hp2
  unfold firstNormOneNeighborPopulation
  linear_combination hcount' - hpart - 2 * hmiddle

/-- The signed two-class Brandt census: primitive numerator sheets, twice the
pre-existing norm-one boundary, and the complete `p+1` neighbor aperture. -/
def brandtPrimeSignedCensus : ℤ :=
  ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) +
    2 * ((middleZeroDirections (p := p)).card : ℤ) - ((p : ℤ) + 1)

/-- The exact failure of the census to return the odd Hecke coefficient. -/
def brandtPrimeEigenDefect : ℤ :=
  brandtPrimeSignedCensus (p := p) - heckeCoeff p

/-- The source census after the middle-zero boundary has been completely
evaluated. -/
theorem brandtPrimeSignedCensus_eq_primitive_character (hp2 : p ≠ 2) :
    brandtPrimeSignedCensus (p := p) =
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) +
        2 * (quadraticChar (ZMod p) (-1) + 1) - ((p : ℤ) + 1) := by
  unfold brandtPrimeSignedCensus
  rw [middleZeroDirections_card_cast (p := p) hp2]

/-- The signed census is not merely a formula: it is the actual complete
norm-one neighbor population minus the complete `p+1` neighbor aperture. -/
theorem brandtPrimeSignedCensus_eq_neighbor_population_sub_aperture
    (hp2 : p ≠ 2) :
    brandtPrimeSignedCensus (p := p) =
      ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) -
        ((p : ℤ) + 1) := by
  unfold brandtPrimeSignedCensus
  rw [firstNormOneNeighborPopulation_card (p := p) hp2]

/-- **THE BRANDT EIGENLAW IS EXACTLY ONE PRIMITIVE PRIME-SQUARE CENSUS
IDENTITY.**  Both implications are integer algebra after the finite boundary
equivalence; no estimate or asymptotic statement occurs. -/
theorem brandtPrimeSignedCensus_eq_heckeCoeff_iff (hp2 : p ≠ 2) :
    brandtPrimeSignedCensus (p := p) = heckeCoeff p ↔
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
        (p : ℤ) + 1 + heckeCoeff p -
          2 * (quadraticChar (ZMod p) (-1) + 1) := by
  rw [brandtPrimeSignedCensus_eq_primitive_character (p := p) hp2]
  constructor <;> intro h <;> linarith

/-- The same residual in the source-specific elliptic-curve receiver. -/
theorem brandtPrimeSignedCensus_eq_trace_iff (hp2 : p ≠ 2) :
    brandtPrimeSignedCensus (p := p) = traceOfFrobenius 1 p ↔
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
        (p : ℤ) + 1 + traceOfFrobenius 1 p -
          2 * (quadraticChar (ZMod p) (-1) + 1) := by
  constructor <;> intro h
  · rw [brandtPrimeSignedCensus_eq_primitive_character (p := p) hp2] at h
    linarith
  · rw [brandtPrimeSignedCensus_eq_primitive_character (p := p) hp2]
    linarith

/-- The primitive census obstruction after transport to the Frobenius chart. -/
def primitiveTraceDefect : ℤ :=
  ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) -
    ((p : ℤ) + 1 + traceOfFrobenius 1 p -
      2 * (quadraticChar (ZMod p) (-1) + 1))

/-- The Brandt eigen-defect and primitive Frobenius-defect are the same returned
difference at every odd prime. -/
theorem brandtPrimeEigenDefect_eq_primitiveTraceDefect (hp2 : p ≠ 2) :
    brandtPrimeEigenDefect (p := p) = primitiveTraceDefect (p := p) := by
  unfold brandtPrimeEigenDefect primitiveTraceDefect
  rw [brandtPrimeSignedCensus_eq_primitive_character (p := p) hp2,
    theCoefficientsAgreeAtEveryOddPrime (p := p) hp2]
  ring

/-- Vanishing of the retained primitive defect is equivalent to the desired
Brandt eigenvalue return. -/
theorem brandtPrimeEigenDefect_eq_zero_iff (hp2 : p ≠ 2) :
    brandtPrimeEigenDefect (p := p) = 0 ↔
      primitiveTraceDefect (p := p) = 0 := by
  rw [brandtPrimeEigenDefect_eq_primitiveTraceDefect (p := p) hp2]

#print axioms brandtPrimeSignedCensus_eq_primitive_character
#print axioms canonicalThickPopulation_one_eq_pair
#print axioms firstNormOneNeighborPopulation_card
#print axioms brandtPrimeSignedCensus_eq_neighbor_population_sub_aperture
#print axioms brandtPrimeSignedCensus_eq_heckeCoeff_iff
#print axioms brandtPrimeSignedCensus_eq_trace_iff
#print axioms brandtPrimeEigenDefect_eq_primitiveTraceDefect
#print axioms brandtPrimeEigenDefect_eq_zero_iff

end Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual
