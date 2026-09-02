import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborRankThree
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborGram
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Discriminant transport for every actual Brandt neighbor

The destination class of a Brandt neighbor is not needed in order to compare
its discriminant with that of its source.  This file fixes the exact
rank-three quotient basis already returned by the occurrence, places that
basis in the common rational three-coordinate receiver, and proves the exact
change-of-coordinates formula for its full-polar Gram determinant.

The remaining arithmetic statement is thereby isolated to one scalar:
the square of the rational covolume of the actual neighbor basis.  Proving
that scalar is one closes determinant `512` without first classifying the
neighbor as either global target form.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants

variable {p : ℕ} [Fact p.Prime]

/-- The exact quotient basis obtained by transporting the returned basis of
the actual rational neighbor back through quotient reconstruction. -/
def occurrenceQuotientRankThreeBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℤ (OccurrenceQuotient hp2 occurrence) :=
  (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence).map
    (occurrenceQuotientEquivNeighbor hp2 occurrence).toIntLinearEquiv.symm

/-- The rational ambient point presented by one vector of the chosen quotient
basis. -/
def occurrenceBasisPoint (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) : RatTriple :=
  (((occurrenceQuotientEquivNeighbor hp2 occurrence)
      (occurrenceQuotientRankThreeBasis hp2 occurrence i) :
        occurrenceNeighborSubgroup hp2 occurrence) : RatTriple)

/-- A coordinate receiver for the common rational ternary ambient space. -/
def ratTripleCoordinate (i : Fin 3) (x : RatTriple) : ℚ :=
  Fin.cases x.1 (fun j => Fin.cases x.2.1 (fun _ => x.2.2) j) i

/-- Columns are the actual source-addressed neighbor basis vectors in the
common rational receiver.  Its determinant is the exact oriented covolume
ratio, not a numerical approximation. -/
def occurrenceBasisCoordinateMatrix (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => ratTripleCoordinate i (occurrenceBasisPoint hp2 occurrence j)

/-- The rational full-polar source matrix selected by the retained source
class. -/
def occurrenceSourceFullGram
    (occurrence : BrandtNeighborOccurrence (p := p)) : Matrix (Fin 3) (Fin 3) ℚ :=
  match occurrence with
  | .inl _ => (brandtFirstFullGram.map (Int.castRingHom ℚ))
  | .inr _ => (brandtSecondFullGram.map (Int.castRingHom ℚ))

theorem occurrenceSourceFullGram_det
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceSourceFullGram occurrence).det = 512 := by
  cases occurrence with
  | inl d =>
      change ((Int.castRingHom ℚ).mapMatrix brandtFirstFullGram).det = 512
      rw [← RingHom.map_det]
      norm_num [brandtFirstFullGram_det]
  | inr d =>
      change ((Int.castRingHom ℚ).mapMatrix brandtSecondFullGram).det = 512
      rw [← RingHom.map_det]
      norm_num [brandtSecondFullGram_det]

/-- The chosen quotient basis reconstructs exactly the chosen actual-neighbor
basis. -/
theorem occurrenceBasisPoint_eq_rankThreeBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    occurrenceBasisPoint hp2 occurrence i =
      ((BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence i :
          occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) := by
  simp [occurrenceBasisPoint, occurrenceQuotientRankThreeBasis]

/-- The rational cast of the actual full-polar Gram matrix is exactly the
source form pulled back along its ambient coordinate matrix. -/
theorem occurrenceFullGram_cast_eq_coordinate_pullback (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceQuotientFullGram hp2 occurrence
        (occurrenceQuotientRankThreeBasis hp2 occurrence)).map
        (Int.castRingHom ℚ) =
      (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
        occurrenceSourceFullGram occurrence *
          occurrenceBasisCoordinateMatrix hp2 occurrence := by
  ext i j
  rw [Matrix.map_apply]
  change ((occurrenceQuotientFullPolar hp2 occurrence
    (occurrenceQuotientRankThreeBasis hp2 occurrence i)
    (occurrenceQuotientRankThreeBasis hp2 occurrence j) : ℤ) : ℚ) = _
  rw [occurrenceQuotientFullPolar_cast]
  simp only [occurrenceQuotientQuadratic]
  rw [map_add]
  change occurrence.quadraticReceiver
        (occurrenceBasisPoint hp2 occurrence i +
          occurrenceBasisPoint hp2 occurrence j) -
      occurrence.quadraticReceiver (occurrenceBasisPoint hp2 occurrence i) -
      occurrence.quadraticReceiver (occurrenceBasisPoint hp2 occurrence j) = _
  cases occurrence with
  | inl d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver,
        occurrenceSourceFullGram, occurrenceBasisCoordinateMatrix,
        ratTripleCoordinate, ratTunnellQuadratic, Matrix.mul_apply,
        Matrix.transpose_apply]
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_succ, brandtFirstFullGram, brandtFirstGram] <;> ring
  | inr d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver,
        occurrenceSourceFullGram, occurrenceBasisCoordinateMatrix,
        ratTripleCoordinate, ratBrandtSecondQuadratic, Matrix.mul_apply,
        Matrix.transpose_apply]
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_succ, brandtSecondFullGram, brandtSecondGram] <;> ring

/-- Exact source-specific discriminant formula for every actual Brandt
neighbor.  No destination-class hypothesis occurs: the only residual factor
is the squared rational covolume of the returned actual-neighbor basis. -/
theorem occurrenceFullGram_det_eq_source_det_mul_covolume_sq (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (((occurrenceQuotientFullGram hp2 occurrence
        (occurrenceQuotientRankThreeBasis hp2 occurrence)).det : ℤ) : ℚ) =
      512 * (occurrenceBasisCoordinateMatrix hp2 occurrence).det ^ 2 := by
  change (Int.castRingHom ℚ)
      (occurrenceQuotientFullGram hp2 occurrence
        (occurrenceQuotientRankThreeBasis hp2 occurrence)).det = _
  rw [RingHom.map_det]
  have hmatrix :
      (Int.castRingHom ℚ).mapMatrix
          (occurrenceQuotientFullGram hp2 occurrence
            (occurrenceQuotientRankThreeBasis hp2 occurrence)) =
        (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
          occurrenceSourceFullGram occurrence *
            occurrenceBasisCoordinateMatrix hp2 occurrence := by
    exact occurrenceFullGram_cast_eq_coordinate_pullback hp2 occurrence
  rw [hmatrix]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    occurrenceSourceFullGram_det]
  ring

/-- The exact covolume-one lemma is sufficient to close the desired full
discriminant, independently of destination classification. -/
theorem occurrenceFullGram_det_of_covolume_sq_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (hcovolume : (occurrenceBasisCoordinateMatrix hp2 occurrence).det ^ 2 = 1) :
    (occurrenceQuotientFullGram hp2 occurrence
      (occurrenceQuotientRankThreeBasis hp2 occurrence)).det = 512 := by
  have h := occurrenceFullGram_det_eq_source_det_mul_covolume_sq hp2 occurrence
  rw [hcovolume, mul_one] at h
  exact_mod_cast h

/-- Conversely, determinant `512` forces the complete squared-covolume
condition.  Thus this condition is not a stronger proxy: it is the exact
remaining separator after the already-proved rank and Gram passages. -/
theorem occurrenceFullGram_det_eq_512_iff_covolume_sq_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceQuotientFullGram hp2 occurrence
        (occurrenceQuotientRankThreeBasis hp2 occurrence)).det = 512 ↔
      (occurrenceBasisCoordinateMatrix hp2 occurrence).det ^ 2 = 1 := by
  constructor
  · intro hdet
    have h := occurrenceFullGram_det_eq_source_det_mul_covolume_sq hp2 occurrence
    rw [hdet] at h
    apply mul_left_cancel₀ (show (512 : ℚ) ≠ 0 by norm_num)
    simpa [mul_one] using h.symm
  · exact occurrenceFullGram_det_of_covolume_sq_one hp2 occurrence

#print axioms occurrenceSourceFullGram_det
#print axioms occurrenceBasisPoint_eq_rankThreeBasis
#print axioms occurrenceFullGram_cast_eq_coordinate_pullback
#print axioms occurrenceFullGram_det_eq_source_det_mul_covolume_sq
#print axioms occurrenceFullGram_det_eq_512_iff_covolume_sq_one

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant
