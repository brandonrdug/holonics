import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborRankThree
import ElementaryHolonics.Millennium.FamilyTunnellBrandtGenusInvariants
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Integral full-polar Gram data on an actual Brandt quotient

An integral quadratic reading first returns an integer, then its two-point
difference returns the full polar form.  Keeping the full polar form avoids an
unjustified division by two; the half-polar target Gram matrices are recovered
only after an evenness theorem.  This file constructs the exact integer-valued
quadratic and full-polar receivers on every actual cyclic quotient and records
their symmetry and diagonal law.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants

variable {p : ℕ} [Fact p.Prime]

abbrev OccurrenceQuotient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :=
  NeighborCoordinates ⧸ AddSubgroup.zmultiples
    (occurrenceRelationGenerator hp2 occurrence)

/-- The exact integer coordinate returned by the integral quotient receiver. -/
def occurrenceQuotientIntegerQuadratic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : OccurrenceQuotient hp2 occurrence) : ℤ :=
  Classical.choose (occurrenceQuotientQuadratic_is_integer hp2 occurrence x)

theorem occurrenceQuotientIntegerQuadratic_cast (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : OccurrenceQuotient hp2 occurrence) :
    (occurrenceQuotientIntegerQuadratic hp2 occurrence x : ℚ) =
      occurrenceQuotientQuadratic hp2 occurrence x := by
  exact (Classical.choose_spec
    (occurrenceQuotientQuadratic_is_integer hp2 occurrence x)).symm

/-- Quadratic scaling by the doubled occurrence, proved in the actual quotient
receiver rather than assumed as an abstract law. -/
theorem occurrenceQuotientQuadratic_add_self (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientQuadratic hp2 occurrence (x + x) =
      4 * occurrenceQuotientQuadratic hp2 occurrence x := by
  change occurrence.quadraticReceiver
      ((occurrenceQuotientEquivNeighbor hp2 occurrence (x + x) :
        occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) = _
  rw [map_add]
  cases occurrence with
  | inl d =>
      simp [occurrenceQuotientQuadratic,
        BrandtNeighborOccurrence.quadraticReceiver, ratTunnellQuadratic]
      ring
  | inr d =>
      simp [occurrenceQuotientQuadratic,
        BrandtNeighborOccurrence.quadraticReceiver, ratBrandtSecondQuadratic]
      ring

/-- The integer full polar return `Q(x+y)-Q(x)-Q(y)`. -/
def occurrenceQuotientFullPolar (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) : ℤ :=
  occurrenceQuotientIntegerQuadratic hp2 occurrence (x + y) -
    occurrenceQuotientIntegerQuadratic hp2 occurrence x -
    occurrenceQuotientIntegerQuadratic hp2 occurrence y

theorem occurrenceQuotientFullPolar_cast (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    (occurrenceQuotientFullPolar hp2 occurrence x y : ℚ) =
      occurrenceQuotientQuadratic hp2 occurrence (x + y) -
        occurrenceQuotientQuadratic hp2 occurrence x -
        occurrenceQuotientQuadratic hp2 occurrence y := by
  simp only [occurrenceQuotientFullPolar, Int.cast_sub]
  rw [occurrenceQuotientIntegerQuadratic_cast,
    occurrenceQuotientIntegerQuadratic_cast,
    occurrenceQuotientIntegerQuadratic_cast]

theorem occurrenceQuotientFullPolar_symmetric (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientFullPolar hp2 occurrence x y =
      occurrenceQuotientFullPolar hp2 occurrence y x := by
  unfold occurrenceQuotientFullPolar
  rw [add_comm x y]
  ring

/-- The full polar return is additive in its first current.  The proof descends
to the two source quadratic receivers and uses the actual quotient transport;
bilinearity is not installed as an abstract assumption. -/
theorem occurrenceQuotientFullPolar_add_left (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y z : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientFullPolar hp2 occurrence (x + y) z =
      occurrenceQuotientFullPolar hp2 occurrence x z +
        occurrenceQuotientFullPolar hp2 occurrence y z := by
  have hcast :
      (occurrenceQuotientFullPolar hp2 occurrence (x + y) z : ℚ) =
        ((occurrenceQuotientFullPolar hp2 occurrence x z +
          occurrenceQuotientFullPolar hp2 occurrence y z : ℤ) : ℚ) := by
    rw [occurrenceQuotientFullPolar_cast]
    push_cast
    rw [occurrenceQuotientFullPolar_cast,
      occurrenceQuotientFullPolar_cast]
    change occurrence.quadraticReceiver
        ((occurrenceQuotientEquivNeighbor hp2 occurrence ((x + y) + z) :
          occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) -
          occurrence.quadraticReceiver
            ((occurrenceQuotientEquivNeighbor hp2 occurrence (x + y) :
              occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) -
          occurrence.quadraticReceiver
            ((occurrenceQuotientEquivNeighbor hp2 occurrence z :
              occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) = _
    simp only [map_add]
    cases occurrence with
    | inl d =>
        simp [occurrenceQuotientQuadratic,
          BrandtNeighborOccurrence.quadraticReceiver, ratTunnellQuadratic]
        ring
    | inr d =>
        simp [occurrenceQuotientQuadratic,
          BrandtNeighborOccurrence.quadraticReceiver, ratBrandtSecondQuadratic]
        ring
  exact_mod_cast hcast

theorem occurrenceQuotientFullPolar_add_right (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y z : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientFullPolar hp2 occurrence x (y + z) =
      occurrenceQuotientFullPolar hp2 occurrence x y +
        occurrenceQuotientFullPolar hp2 occurrence x z := by
  rw [occurrenceQuotientFullPolar_symmetric hp2 occurrence x (y + z),
    occurrenceQuotientFullPolar_add_left hp2 occurrence y z x,
    occurrenceQuotientFullPolar_symmetric hp2 occurrence y x,
    occurrenceQuotientFullPolar_symmetric hp2 occurrence z x]

/-- The diagonal of the full polar form is exactly twice the integer quadratic
reading. -/
theorem occurrenceQuotientFullPolar_self (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientFullPolar hp2 occurrence x x =
      2 * occurrenceQuotientIntegerQuadratic hp2 occurrence x := by
  have hcast :
      (occurrenceQuotientFullPolar hp2 occurrence x x : ℚ) =
        ((2 * occurrenceQuotientIntegerQuadratic hp2 occurrence x : ℤ) : ℚ) := by
    rw [occurrenceQuotientFullPolar_cast]
    push_cast
    rw [occurrenceQuotientIntegerQuadratic_cast,
      occurrenceQuotientQuadratic_add_self]
    ring
  exact_mod_cast hcast

/-- Full-polar Gram data in any chosen integral basis of the actual quotient. -/
def occurrenceQuotientFullGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (basis : Module.Basis ι ℤ (OccurrenceQuotient hp2 occurrence)) : Matrix ι ι ℤ :=
  fun i j => occurrenceQuotientFullPolar hp2 occurrence (basis i) (basis j)

theorem occurrenceQuotientFullGram_transpose {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (basis : Module.Basis ι ℤ (OccurrenceQuotient hp2 occurrence)) :
    (occurrenceQuotientFullGram hp2 occurrence basis).transpose =
      occurrenceQuotientFullGram hp2 occurrence basis := by
  ext i j
  exact occurrenceQuotientFullPolar_symmetric hp2 occurrence (basis j) (basis i)

theorem occurrenceQuotientFullGram_diagonal {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (basis : Module.Basis ι ℤ (OccurrenceQuotient hp2 occurrence)) (i : ι) :
    occurrenceQuotientFullGram hp2 occurrence basis i i =
      2 * occurrenceQuotientIntegerQuadratic hp2 occurrence (basis i) :=
  occurrenceQuotientFullPolar_self hp2 occurrence (basis i)

/-- The rank-three basis on the actual neighbor transported back through the
exact cyclic quotient equivalence.  This makes the full-polar Gram carrier
unconditional for every source occurrence. -/
def occurrenceQuotientRankThreeBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℤ (OccurrenceQuotient hp2 occurrence) :=
  (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence).map
    (occurrenceQuotientEquivNeighbor hp2 occurrence).symm.toIntLinearEquiv

/-- The actual source-addressed full-polar `3 × 3` Gram matrix. -/
def occurrenceRankThreeFullGram (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  occurrenceQuotientFullGram hp2 occurrence
    (occurrenceQuotientRankThreeBasis hp2 occurrence)

theorem occurrenceRankThreeFullGram_transpose (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceRankThreeFullGram hp2 occurrence).transpose =
      occurrenceRankThreeFullGram hp2 occurrence :=
  occurrenceQuotientFullGram_transpose hp2 occurrence
    (occurrenceQuotientRankThreeBasis hp2 occurrence)

theorem occurrenceRankThreeFullGram_diagonal (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    occurrenceRankThreeFullGram hp2 occurrence i i =
      2 * occurrenceQuotientIntegerQuadratic hp2 occurrence
        (occurrenceQuotientRankThreeBasis hp2 occurrence i) :=
  occurrenceQuotientFullGram_diagonal hp2 occurrence
    (occurrenceQuotientRankThreeBasis hp2 occurrence) i

/-- The two target full-polar matrices have determinant `2³·64 = 512`. -/
def brandtFirstFullGram : Matrix (Fin 3) (Fin 3) ℤ :=
  2 • brandtFirstGram

def brandtSecondFullGram : Matrix (Fin 3) (Fin 3) ℤ :=
  2 • brandtSecondGram

theorem brandtFirstFullGram_det : brandtFirstFullGram.det = 512 := by
  decide

theorem brandtSecondFullGram_det : brandtSecondFullGram.det = 512 := by
  decide

#print axioms occurrenceQuotientIntegerQuadratic_cast
#print axioms occurrenceQuotientQuadratic_add_self
#print axioms occurrenceQuotientFullPolar_add_left
#print axioms occurrenceQuotientFullPolar_self
#print axioms occurrenceQuotientFullGram_transpose
#print axioms occurrenceRankThreeFullGram_transpose
#print axioms brandtFirstFullGram_det
#print axioms brandtSecondFullGram_det

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
