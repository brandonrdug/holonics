import ElementaryHolonics.Millennium.FamilyTunnellBrandtJonesPallReduction

/-!
# Jones--Pall source normal forms for the determinant-64 Brandt genus

Jones and Pall write

`a*x^2 + b*y^2 + c*z^2 + 2*r*y*z + 2*s*x*z + 2*t*x*y`

as `(a,b,c,r,s,t)`.  This file retains that convention exactly, identifies
their companion `(2,4,9,-2,0,0)` with the repository second receiver by a
proper unimodular sign change, and records the determinant-`64` source and
reciprocal faces used in their proof.

The paper's genus criterion is represented by explicit rational transport
data with denominator prime to twice the determinant.  Eisenstein reduction
is a decidable coefficient predicate, not a destination label.  No assertion
that the source genus has only two classes occurs here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtJonesPallNormalForm

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
open Soma.Holonics.Millennium.FamilyTunnellBrandtModFourReceiver
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex

/-- The six integral coefficients in the Jones--Pall convention. -/
structure SixCoefficients where
  a : ℤ
  b : ℤ
  c : ℤ
  r : ℤ
  s : ℤ
  t : ℤ
  deriving DecidableEq

/-- The quadratic receiver represented by six Jones--Pall coefficients. -/
def SixCoefficients.quadratic (F : SixCoefficients) (v : IntTriple) : ℤ :=
  F.a * v.1 ^ 2 + F.b * v.2.1 ^ 2 + F.c * v.2.2 ^ 2 +
    2 * F.r * v.2.1 * v.2.2 + 2 * F.s * v.1 * v.2.2 +
    2 * F.t * v.1 * v.2.1

/-- The half-polar Gram matrix corresponding to the six coefficients. -/
def SixCoefficients.gram (F : SixCoefficients) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![F.a, F.t, F.s;
     F.t, F.b, F.r;
     F.s, F.r, F.c]

/-- The exact six-coordinate determinant polynomial. -/
theorem SixCoefficients.gram_det (F : SixCoefficients) :
    F.gram.det =
      F.a * F.b * F.c + 2 * F.r * F.s * F.t -
        F.a * F.r ^ 2 - F.b * F.s ^ 2 - F.c * F.t ^ 2 := by
  simp [SixCoefficients.gram, Matrix.det_fin_three]
  ring

/-- Jones--Pall's diagonal source, coordinate-swapped from repository `Q₁`. -/
def source : SixCoefficients := ⟨1, 2, 32, 0, 0, 0⟩

/-- The reciprocal face used in their class-number argument. -/
def sourceReciprocal : SixCoefficients := ⟨1, 16, 32, 0, 0, 0⟩

/-- The one-class auxiliary face used for the mod-eight split. -/
def auxiliary : SixCoefficients := ⟨1, 4, 8, 0, 0, 0⟩

/-- The second reduced form displayed by Jones--Pall. -/
def companion : SixCoefficients := ⟨2, 4, 9, -2, 0, 0⟩

theorem source_det : source.gram.det = 64 := by decide
theorem sourceReciprocal_det : sourceReciprocal.gram.det = 512 := by decide
theorem auxiliary_det : auxiliary.gram.det = 32 := by decide
theorem companion_det : companion.gram.det = 64 := by decide

/-- A proper source rebase: swap `x,y` and reverse `z`.  Its two sign changes
give determinant one. -/
def sourceProperRebase : IntTriple ≃+ IntTriple where
  toFun v := (v.2.1, v.1, -v.2.2)
  invFun v := (v.2.1, v.1, -v.2.2)
  left_inv := by rintro ⟨x, y, z⟩; simp
  right_inv := by rintro ⟨x, y, z⟩; simp
  map_add' := by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩
    ext <;> simp <;> abel

def sourceProperRebaseMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, -1]

theorem sourceProperRebaseMatrix_det : sourceProperRebaseMatrix.det = 1 := by
  decide

theorem sourceProperRebase_preserves (v : IntTriple) :
    brandtFirstQuadratic (sourceProperRebase v) = source.quadratic v := by
  simp [sourceProperRebase, source, SixCoefficients.quadratic,
    brandtFirstQuadratic]
  ring

/-- A proper sign change carrying the Jones--Pall companion to repository
`Q₂`: reverse both `x` and `z`. -/
def companionProperRebase : IntTriple ≃+ IntTriple where
  toFun v := (-v.1, v.2.1, -v.2.2)
  invFun v := (-v.1, v.2.1, -v.2.2)
  left_inv := by rintro ⟨x, y, z⟩; simp
  right_inv := by rintro ⟨x, y, z⟩; simp
  map_add' := by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩
    ext <;> simp <;> abel

def companionProperRebaseMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 0, 0;
      0, 1, 0;
      0, 0, -1]

theorem companionProperRebaseMatrix_det : companionProperRebaseMatrix.det = 1 := by
  decide

theorem companionProperRebase_preserves (v : IntTriple) :
    brandtSecondQuadratic (companionProperRebase v) = companion.quadratic v := by
  simp [companionProperRebase, companion, SixCoefficients.quadratic,
    brandtSecondQuadratic]
  ring

theorem companion_gram_rebase :
    companionProperRebaseMatrix.transpose * brandtSecondGram *
        companionProperRebaseMatrix = companion.gram := by
  decide

/-! ## Exact certificates used by the remaining reduction -/

/-- The coefficient conditions of Eisenstein reduction, translated to the
Jones--Pall half-cross-term convention.  This is executable data; existence
and uniqueness of such a representative are separate theorem obligations. -/
def SixCoefficients.IsEisensteinReduced (F : SixCoefficients) : Prop :=
  F.a ≤ F.b ∧ F.b ≤ F.c ∧
  ((0 < F.r ∧ 0 < F.s ∧ 0 < F.t) ∨
    (F.r ≤ 0 ∧ F.s ≤ 0 ∧ F.t ≤ 0)) ∧
  2 * |F.t| ≤ F.a ∧ 2 * |F.s| ≤ F.a ∧ 2 * |F.r| ≤ F.b ∧
  0 ≤ F.a + F.b + 2 * (F.r + F.s + F.t) ∧
  (F.a = 2 * F.t → F.s ≤ 2 * F.r) ∧
  (F.a = 2 * F.s → F.t ≤ 2 * F.r) ∧
  (F.b = 2 * F.r → F.t ≤ 2 * F.s) ∧
  (F.a = -2 * F.t → F.s = 0) ∧
  (F.a = -2 * F.s → F.t = 0) ∧
  (F.b = -2 * F.r → F.t = 0) ∧
  (F.a + F.b + 2 * (F.r + F.s + F.t) = 0 →
    2 * F.a + 4 * F.s + 2 * F.t ≤ 0) ∧
  (F.a = F.b → |F.r| ≤ |F.s|) ∧
  (F.b = F.c → |F.s| ≤ |F.t|)

instance (F : SixCoefficients) : Decidable F.IsEisensteinReduced :=
  by
    unfold SixCoefficients.IsEisensteinReduced
    infer_instance

theorem source_isEisensteinReduced : source.IsEisensteinReduced := by decide
theorem companion_isEisensteinReduced : companion.IsEisensteinReduced := by decide

def rationalMatrix (d : ℕ) (U : Matrix (Fin 3) (Fin 3) ℤ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => (U i j : ℚ) / d

/-- A rational genus transport in the exact Smith/Jones--Pall chart: the
denominator is prime to twice the determinant and the rational transformation
has determinant one. -/
structure RationalGenusTransport (F G : SixCoefficients) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator : Matrix (Fin 3) (Fin 3) ℤ
  denominator_coprime :
    denominator.Coprime (2 * F.gram.det.natAbs)
  same_determinant : F.gram.det = G.gram.det
  determinant_one : (rationalMatrix denominator numerator).det = 1
  carries_gram :
    (rationalMatrix denominator numerator).transpose *
      F.gram.map (Int.castRingHom ℚ) *
      rationalMatrix denominator numerator =
        G.gram.map (Int.castRingHom ℚ)

/-- An exact determinant-one, odd-denominator rational transport from the
Jones--Pall source to its companion.  The denominator `3` is prime to
`2 * 64`; this is the explicit genus witness needed when an occurrence starts
from the repository's second Brandt class. -/
def sourceToCompanionNumerator : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -2, -7;
     -3, 0, 0;
     0, 1, -1]

theorem sourceToCompanionNumerator_det :
    sourceToCompanionNumerator.det = 27 := by decide

theorem sourceToCompanion_det_one :
    (rationalMatrix 3 sourceToCompanionNumerator).det = 1 := by
  simp [rationalMatrix, Matrix.det_fin_three, sourceToCompanionNumerator]
  norm_num

theorem sourceToCompanion_carries :
    (rationalMatrix 3 sourceToCompanionNumerator).transpose *
      source.gram.map (Int.castRingHom ℚ) *
      rationalMatrix 3 sourceToCompanionNumerator =
        companion.gram.map (Int.castRingHom ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalMatrix, sourceToCompanionNumerator,
      source, companion, SixCoefficients.gram, Matrix.mul_apply,
      Fin.sum_univ_succ]

def sourceToCompanionTransport : RationalGenusTransport source companion where
  denominator := 3
  denominator_pos := by decide
  numerator := sourceToCompanionNumerator
  denominator_coprime := by norm_num [source_det]
  same_determinant := by rw [source_det, companion_det]
  determinant_one := sourceToCompanion_det_one
  carries_gram := sourceToCompanion_carries

/-- The exact finite-table certificate still required from reduction theory. -/
structure ReducedGenusRepresentative (F G : SixCoefficients) where
  representative : SixCoefficients
  genusTransport : RationalGenusTransport F representative
  reduced : representative.IsEisensteinReduced
  equivalentNumerator : Matrix (Fin 3) (Fin 3) ℤ
  equivalentDeterminant :
    equivalentNumerator.det = 1 ∨ equivalentNumerator.det = -1
  equivalentCarries :
    equivalentNumerator.transpose * representative.gram * equivalentNumerator =
      G.gram

/-! ## Every actual neighbor returns a determinant-64 Jones--Pall carrier -/

variable {p : ℕ} [Fact p.Prime]

/-- One addressed coordinate of an integral triple. -/
def intTripleCoordinate (i : Fin 3) (x : IntTriple) : ℤ :=
  Fin.cases x.1 (fun j => Fin.cases x.2.1 (fun _ => x.2.2) j) i

/-- The integral numerator matrix of the actual neighbor basis after its one
complete defining-prime scale. -/
def occurrenceBasisNumeratorMatrix (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => intTripleCoordinate i
    (BrandtNeighborOccurrence.integralPScale hp2 occurrence
      (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j))

/-- Dividing the integral numerator by the exact defining prime reconstructs
the rational occurrence basis matrix point-for-point. -/
theorem rationalMatrix_occurrenceBasisNumerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    rationalMatrix p (occurrenceBasisNumeratorMatrix hp2 occurrence) =
      occurrenceBasisCoordinateMatrix hp2 occurrence := by
  ext i j
  have h := BrandtNeighborOccurrence.intTripleInclusion_integralPScale
    hp2 occurrence (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)
  rw [← occurrenceBasisPoint_eq_rankThreeBasis hp2 occurrence j] at h
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  fin_cases i
  · have hc := congrArg (fun q : RatTriple => q.1) h
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).1 : ℚ) =
        (p : ℚ) * (occurrenceBasisPoint hp2 occurrence j).1 at hc
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).1 : ℚ) /
        (p : ℚ) = (occurrenceBasisPoint hp2 occurrence j).1
    field_simp [hpQ]
    simpa [mul_comm] using hc
  · have hc := congrArg (fun q : RatTriple => q.2.1) h
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).2.1 : ℚ) =
        (p : ℚ) * (occurrenceBasisPoint hp2 occurrence j).2.1 at hc
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).2.1 : ℚ) /
        (p : ℚ) = (occurrenceBasisPoint hp2 occurrence j).2.1
    field_simp [hpQ]
    simpa [mul_comm] using hc
  · have hc := congrArg (fun q : RatTriple => q.2.2) h
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).2.2 : ℚ) =
        (p : ℚ) * (occurrenceBasisPoint hp2 occurrence j).2.2 at hc
    change
      ((BrandtNeighborOccurrence.integralPScale hp2 occurrence
        (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence j)).2.2 : ℚ) /
        (p : ℚ) = (occurrenceBasisPoint hp2 occurrence j).2.2
    field_simp [hpQ]
    simpa [mul_comm] using hc

/-- Multiplying two actual-neighbor currents by the defining odd prime puts
them in the integral source lattice.  Their source full-polar return is exactly
`p²` times the quotient full-polar return. -/
theorem occurrenceScaledSourceFullPolar (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceSourceQuadratic occurrence
        (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
          (occurrenceQuotientEquivNeighbor hp2 occurrence x) +
         BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
          (occurrenceQuotientEquivNeighbor hp2 occurrence y)) -
      occurrenceSourceQuadratic occurrence
        (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
          (occurrenceQuotientEquivNeighbor hp2 occurrence x)) -
      occurrenceSourceQuadratic occurrence
        (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
          (occurrenceQuotientEquivNeighbor hp2 occurrence y)) =
      (p : ℤ) ^ 2 * occurrenceQuotientFullPolar hp2 occurrence x y := by
  have hcast :
      ((occurrenceSourceQuadratic occurrence
          (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
              (occurrenceQuotientEquivNeighbor hp2 occurrence x) +
            BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
              (occurrenceQuotientEquivNeighbor hp2 occurrence y)) -
        occurrenceSourceQuadratic occurrence
          (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
            (occurrenceQuotientEquivNeighbor hp2 occurrence x)) -
        occurrenceSourceQuadratic occurrence
          (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
            (occurrenceQuotientEquivNeighbor hp2 occurrence y)) : ℤ) : ℚ) =
        (((p : ℤ) ^ 2 * occurrenceQuotientFullPolar hp2 occurrence x y : ℤ) :
          ℚ) := by
    push_cast
    rw [← map_add]
    simp only [BrandtNeighborOccurrence.neighborToIntegral,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [occurrenceSourceQuadratic_integralPScale,
      occurrenceSourceQuadratic_integralPScale,
      occurrenceSourceQuadratic_integralPScale]
    rw [occurrenceQuotientFullPolar_cast]
    simp only [map_add, occurrenceQuotientQuadratic]
    ring
  exact_mod_cast hcast

private theorem occurrenceSourceFullPolar_even
    (occurrence : BrandtNeighborOccurrence (p := p)) (x y : IntTriple) :
    Even (occurrenceSourceQuadratic occurrence (x + y) -
      occurrenceSourceQuadratic occurrence x -
      occurrenceSourceQuadratic occurrence y) := by
  rcases x with ⟨xx, xy, xz⟩
  rcases y with ⟨yx, yy, yz⟩
  cases occurrence with
  | inl d =>
      refine ⟨2 * xx * yx + xy * yy + 32 * xz * yz, ?_⟩
      simp [occurrenceSourceQuadratic, brandtFirstQuadratic]
      ring
  | inr d =>
      refine ⟨2 * xx * yx + 4 * xy * yy +
        2 * (xy * yz + xz * yy) + 9 * xz * yz, ?_⟩
      simp [occurrenceSourceQuadratic, brandtSecondQuadratic]
      ring

/-- The actual neighbor remains an even lattice.  The proof does not assume a
destination class: source evenness is transported through the odd `p²` scale,
and odd multiplication is cancelled exactly. -/
theorem occurrenceQuotientFullPolar_even (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    Even (occurrenceQuotientFullPolar hp2 occurrence x y) := by
  let X := BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
    (occurrenceQuotientEquivNeighbor hp2 occurrence x)
  let Y := BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence
    (occurrenceQuotientEquivNeighbor hp2 occurrence y)
  have hscaled :
      occurrenceSourceQuadratic occurrence (X + Y) -
        occurrenceSourceQuadratic occurrence X -
        occurrenceSourceQuadratic occurrence Y =
      (p : ℤ) ^ 2 * occurrenceQuotientFullPolar hp2 occurrence x y := by
    exact occurrenceScaledSourceFullPolar hp2 occurrence x y
  have heven :
      Even ((p : ℤ) ^ 2 * occurrenceQuotientFullPolar hp2 occurrence x y) := by
    rw [← hscaled]
    exact occurrenceSourceFullPolar_even occurrence X Y
  have hpoddNat : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hpoddNat
  have hp : (p : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  rcases heven with ⟨c, hc⟩
  let A : ℤ := 2 * (k : ℤ) ^ 2 + 2 * (k : ℤ)
  refine ⟨c - A * occurrenceQuotientFullPolar hp2 occurrence x y, ?_⟩
  calc
    occurrenceQuotientFullPolar hp2 occurrence x y =
        (c + c) - 2 * A * occurrenceQuotientFullPolar hp2 occurrence x y := by
      rw [← hc, hp]
      simp only [A]
      ring
    _ = (c - A * occurrenceQuotientFullPolar hp2 occurrence x y) +
        (c - A * occurrenceQuotientFullPolar hp2 occurrence x y) := by ring

/-- The unique integral half-polar coordinate returned by source evenness. -/
def occurrenceQuotientHalfPolar (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) : ℤ :=
  Classical.choose (occurrenceQuotientFullPolar_even hp2 occurrence x y)

theorem occurrenceQuotientFullPolar_eq_two_mul_half (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientFullPolar hp2 occurrence x y =
      2 * occurrenceQuotientHalfPolar hp2 occurrence x y := by
  have h := Classical.choose_spec
    (occurrenceQuotientFullPolar_even hp2 occurrence x y)
  change occurrenceQuotientFullPolar hp2 occurrence x y =
    occurrenceQuotientHalfPolar hp2 occurrence x y +
      occurrenceQuotientHalfPolar hp2 occurrence x y at h
  nlinarith

theorem occurrenceQuotientHalfPolar_symmetric (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence x y =
      occurrenceQuotientHalfPolar hp2 occurrence y x := by
  have hxy := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence x y
  have hyx := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence y x
  rw [occurrenceQuotientFullPolar_symmetric hp2 occurrence x y] at hxy
  omega

theorem occurrenceQuotientHalfPolar_add_left (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y z : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence (x + y) z =
      occurrenceQuotientHalfPolar hp2 occurrence x z +
        occurrenceQuotientHalfPolar hp2 occurrence y z := by
  have hsum := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence (x + y) z
  have hx := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence x z
  have hy := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence y z
  rw [occurrenceQuotientFullPolar_add_left hp2 occurrence x y z, hx, hy] at hsum
  omega

theorem occurrenceQuotientHalfPolar_zero_left (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence 0 y = 0 := by
  have h := occurrenceQuotientHalfPolar_add_left hp2 occurrence 0 0 y
  simp only [zero_add] at h
  omega

/-- One current slot of the half-polar return, retained as an additive map so
all signed integral repetitions are inherited rather than re-proved. -/
def occurrenceQuotientHalfPolarLeft (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : OccurrenceQuotient hp2 occurrence) :
    OccurrenceQuotient hp2 occurrence →+ ℤ where
  toFun x := occurrenceQuotientHalfPolar hp2 occurrence x y
  map_zero' := occurrenceQuotientHalfPolar_zero_left hp2 occurrence y
  map_add' := fun x z =>
    occurrenceQuotientHalfPolar_add_left hp2 occurrence x z y

theorem occurrenceQuotientHalfPolar_zsmul_left (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (a : ℤ) (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence (a • x) y =
      a * occurrenceQuotientHalfPolar hp2 occurrence x y := by
  exact map_zsmul (occurrenceQuotientHalfPolarLeft hp2 occurrence y) a x

theorem occurrenceQuotientHalfPolar_add_right (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y z : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence x (y + z) =
      occurrenceQuotientHalfPolar hp2 occurrence x y +
        occurrenceQuotientHalfPolar hp2 occurrence x z := by
  rw [occurrenceQuotientHalfPolar_symmetric hp2 occurrence x (y + z),
    occurrenceQuotientHalfPolar_add_left hp2 occurrence y z x,
    occurrenceQuotientHalfPolar_symmetric hp2 occurrence y x,
    occurrenceQuotientHalfPolar_symmetric hp2 occurrence z x]

theorem occurrenceQuotientHalfPolar_zsmul_right (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (a : ℤ) (x y : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence x (a • y) =
      a * occurrenceQuotientHalfPolar hp2 occurrence x y := by
  rw [occurrenceQuotientHalfPolar_symmetric hp2 occurrence x (a • y),
    occurrenceQuotientHalfPolar_zsmul_left hp2 occurrence a y x,
    occurrenceQuotientHalfPolar_symmetric hp2 occurrence y x]

theorem occurrenceQuotientHalfPolar_self (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : OccurrenceQuotient hp2 occurrence) :
    occurrenceQuotientHalfPolar hp2 occurrence x x =
      occurrenceQuotientIntegerQuadratic hp2 occurrence x := by
  have hhalf := occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence x x
  have hfull := occurrenceQuotientFullPolar_self hp2 occurrence x
  omega

/-- The actual half-polar Gram matrix in the retained quotient basis. -/
def occurrenceJonesPallHalfGram (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => occurrenceQuotientHalfPolar hp2 occurrence
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence i)
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence j)

theorem occurrenceFullGram_eq_two_smul_halfGram (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceQuotientFullGram hp2 occurrence
        (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
          hp2 occurrence) =
      (2 : ℤ) • occurrenceJonesPallHalfGram hp2 occurrence := by
  ext i j
  change occurrenceQuotientFullPolar hp2 occurrence _ _ =
    2 * occurrenceQuotientHalfPolar hp2 occurrence _ _
  exact occurrenceQuotientFullPolar_eq_two_mul_half hp2 occurrence _ _

theorem occurrenceJonesPallHalfGram_det (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceJonesPallHalfGram hp2 occurrence).det = 64 := by
  have hdet := occurrenceFullGram_det_eq_512 hp2 occurrence
  rw [occurrenceFullGram_eq_two_smul_halfGram hp2 occurrence,
    Matrix.det_smul] at hdet
  norm_num at hdet
  omega

/-- The actual neighbor, now in the exact six-coordinate convention consumed
by Jones--Pall reduction. -/
def occurrenceJonesPallCoefficients (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : SixCoefficients :=
  let G := occurrenceJonesPallHalfGram hp2 occurrence
  ⟨G 0 0, G 1 1, G 2 2, G 1 2, G 0 2, G 0 1⟩

theorem occurrenceJonesPallCoefficients_gram (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceJonesPallCoefficients hp2 occurrence).gram =
      occurrenceJonesPallHalfGram hp2 occurrence := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [occurrenceJonesPallCoefficients, SixCoefficients.gram,
      occurrenceJonesPallHalfGram]
  all_goals apply occurrenceQuotientHalfPolar_symmetric

/-- Every actual odd-prime Brandt occurrence has half-polar determinant
exactly `64`; no destination form has been presumed. -/
theorem occurrenceJonesPallCoefficients_det (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceJonesPallCoefficients hp2 occurrence).gram.det = 64 := by
  rw [occurrenceJonesPallCoefficients_gram]
  exact occurrenceJonesPallHalfGram_det hp2 occurrence

/-- Integral coordinates interpreted in the actual quotient basis. -/
def occurrenceJonesPallCoordinatePoint (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : IntTriple) : OccurrenceQuotient hp2 occurrence :=
  let b :=
    FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence
  v.1 • b 0 + v.2.1 • b 1 + v.2.2 • b 2

/-- The six coefficients are not merely a matrix extraction: their quadratic
reading is exactly the integer quadratic reading on the corresponding actual
quotient current. -/
theorem occurrenceJonesPallCoefficients_quadratic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) :
    (occurrenceJonesPallCoefficients hp2 occurrence).quadratic v =
      occurrenceQuotientIntegerQuadratic hp2 occurrence
        (occurrenceJonesPallCoordinatePoint hp2 occurrence v) := by
  rw [← occurrenceQuotientHalfPolar_self hp2 occurrence]
  rcases v with ⟨x, y, z⟩
  simp only [occurrenceJonesPallCoordinatePoint, SixCoefficients.quadratic,
    occurrenceJonesPallCoefficients, occurrenceJonesPallHalfGram]
  simp only [occurrenceQuotientHalfPolar_add_left,
    occurrenceQuotientHalfPolar_add_right,
    occurrenceQuotientHalfPolar_zsmul_left,
    occurrenceQuotientHalfPolar_zsmul_right]
  rw [occurrenceQuotientHalfPolar_symmetric hp2 occurrence
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 1)
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 0)]
  rw [occurrenceQuotientHalfPolar_symmetric hp2 occurrence
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 2)
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 0)]
  rw [occurrenceQuotientHalfPolar_symmetric hp2 occurrence
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 2)
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence 1)]
  ring

/-- The retained quotient basis gives a genuine additive coordinate
equivalence, not merely a surjective presentation. -/
def occurrenceJonesPallCoordinateEquiv (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    IntTriple ≃+ OccurrenceQuotient hp2 occurrence :=
  (intTripleBasis.equiv
    (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence) (Equiv.refl (Fin 3))).toAddEquiv

theorem occurrenceJonesPallCoordinateEquiv_apply (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) :
    occurrenceJonesPallCoordinateEquiv hp2 occurrence v =
      occurrenceJonesPallCoordinatePoint hp2 occurrence v := by
  rcases v with ⟨x, y, z⟩
  let b :=
    FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
      hp2 occurrence
  change (intTripleBasis.equiv b (Equiv.refl (Fin 3))) (x, y, z) =
    x • b 0 + y • b 1 + z • b 2
  rw [show (x, y, z) =
      x • intTripleBasis 0 + y • intTripleBasis 1 + z • intTripleBasis 2 by
    simp only [FamilyTunnellBrandtNeighborRankThree.intTripleBasis_zero,
      FamilyTunnellBrandtNeighborRankThree.intTripleBasis_one,
      FamilyTunnellBrandtNeighborRankThree.intTripleBasis_two, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul]
    ext <;> simp]
  simp only [map_add, map_zsmul, Module.Basis.equiv_apply, Equiv.refl_apply]

/-- The coefficient-level depth-four receiver used by the finite reduction. -/
def CoefficientsRepresentModSixteen (F : SixCoefficients) (r : ℤ) : Prop :=
  ∃ v : IntTriple, F.quadratic v % 16 = r % 16

/-- Coefficient representation and actual-neighbor representation are the
same receiver through the complete quotient coordinate equivalence. -/
theorem occurrenceJonesPallCoefficients_neighbor_profile (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) :
    CoefficientsRepresentModSixteen
        (occurrenceJonesPallCoefficients hp2 occurrence) r ↔
      NeighborRepresentsModSixteen hp2 occurrence r := by
  constructor
  · rintro ⟨v, hv⟩
    let q := occurrenceJonesPallCoordinateEquiv hp2 occurrence v
    let x := occurrenceQuotientEquivNeighbor hp2 occurrence q
    refine ⟨x, occurrenceQuotientIntegerQuadratic hp2 occurrence q, ?_, ?_⟩
    · exact (occurrenceQuotientIntegerQuadratic_cast hp2 occurrence q).symm
    · rw [← hv]
      have hquad := occurrenceJonesPallCoefficients_quadratic hp2 occurrence v
      rw [← occurrenceJonesPallCoordinateEquiv_apply hp2 occurrence v] at hquad
      change occurrenceQuotientIntegerQuadratic hp2 occurrence q % 16 = _
      rw [← hquad]
  · rintro ⟨x, N, hN, hmod⟩
    let q := (occurrenceQuotientEquivNeighbor hp2 occurrence).symm x
    let v := (occurrenceJonesPallCoordinateEquiv hp2 occurrence).symm q
    refine ⟨v, ?_⟩
    have hq : occurrenceQuotientIntegerQuadratic hp2 occurrence q = N := by
      have hcast := occurrenceQuotientIntegerQuadratic_cast hp2 occurrence q
      change (occurrenceQuotientIntegerQuadratic hp2 occurrence q : ℚ) =
        occurrence.quadraticReceiver
          ((occurrenceQuotientEquivNeighbor hp2 occurrence q :
            occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) at hcast
      rw [show occurrenceQuotientEquivNeighbor hp2 occurrence q = x by
        simp [q]] at hcast
      rw [hN] at hcast
      exact_mod_cast hcast
    rw [occurrenceJonesPallCoefficients_quadratic,
      ← occurrenceJonesPallCoordinateEquiv_apply]
    simp only [v, AddEquiv.apply_symm_apply, hq]
    exact hmod

/-- The constructed Jones--Pall carrier has exactly the retained source
class's complete modulo-sixteen representation profile. -/
theorem occurrenceJonesPallCoefficients_source_profile (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) :
    CoefficientsRepresentModSixteen
        (occurrenceJonesPallCoefficients hp2 occurrence) r ↔
      SourceRepresentsModSixteen occurrence r :=
  (occurrenceJonesPallCoefficients_neighbor_profile hp2 occurrence r).trans
    (source_neighbor_mod_sixteen_profile_equivalence hp2 occurrence r).symm

/-! ## The actual source-to-occurrence rational genus transport -/

private theorem brandtFirstFullGram_entry (i j : Fin 3) :
    brandtFirstFullGram i j = 2 * brandtFirstGram i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem brandtSecondFullGram_entry (i j : Fin 3) :
    brandtSecondFullGram i j = 2 * brandtSecondGram i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The source half-polar chart retained by an actual occurrence before its
returned basis is applied. -/
def occurrenceSourceHalfGram
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  match occurrence with
  | .inl _ => brandtFirstGram.map (Int.castRingHom ℚ)
  | .inr _ => brandtSecondGram.map (Int.castRingHom ℚ)

/-- Cancelling the exact factor two in the full-polar pullback returns the
half-polar Jones--Pall matrix in the actual occurrence basis. -/
theorem occurrenceHalfGram_cast_eq_pullback (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceJonesPallHalfGram hp2 occurrence).map (Int.castRingHom ℚ) =
      (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
        occurrenceSourceHalfGram occurrence *
          occurrenceBasisCoordinateMatrix hp2 occurrence := by
  have h := occurrenceFullGram_cast_eq_coordinate_pullback hp2 occurrence
  cases occurrence with
  | inl d =>
      ext i j
      have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => A i j) h
      change
        ((occurrenceQuotientFullPolar hp2 (Sum.inl d)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (Sum.inl d) i)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (Sum.inl d) j) : ℤ) : ℚ) = _ at hij
      rw [occurrenceQuotientFullPolar_eq_two_mul_half] at hij
      simp only [occurrenceSourceFullGram, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.map_apply] at hij
      simp_rw [brandtFirstFullGram_entry] at hij
      push_cast at hij
      simp [occurrenceSourceHalfGram, occurrenceJonesPallHalfGram,
        Matrix.mul_apply, Fin.sum_univ_succ]
      simp [Fin.sum_univ_succ] at hij
      linarith
  | inr d =>
      ext i j
      have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => A i j) h
      change
        ((occurrenceQuotientFullPolar hp2 (Sum.inr d)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (Sum.inr d) i)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (Sum.inr d) j) : ℤ) : ℚ) = _ at hij
      rw [occurrenceQuotientFullPolar_eq_two_mul_half] at hij
      simp only [occurrenceSourceFullGram, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.map_apply] at hij
      simp_rw [brandtSecondFullGram_entry] at hij
      push_cast at hij
      simp [occurrenceSourceHalfGram, occurrenceJonesPallHalfGram,
        Matrix.mul_apply, Fin.sum_univ_succ]
      simp [Fin.sum_univ_succ] at hij
      linarith

/-- The proper source prefix: the first Brandt chart is an integral proper
rebase; the second first crosses the explicit denominator-three companion
transport and then applies its proper rebase. -/
def occurrenceSourcePrefixMatrix
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  match occurrence with
  | .inl _ => sourceProperRebaseMatrix.map (Int.castRingHom ℚ)
  | .inr _ =>
      rationalMatrix 3 sourceToCompanionNumerator *
        companionProperRebaseMatrix.map (Int.castRingHom ℚ)

theorem occurrenceSourcePrefixMatrix_det
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceSourcePrefixMatrix occurrence).det = 1 := by
  cases occurrence with
  | inl d =>
      change (sourceProperRebaseMatrix.map (Int.castRingHom ℚ)).det = 1
      change ((Int.castRingHom ℚ).mapMatrix sourceProperRebaseMatrix).det = 1
      rw [← RingHom.map_det, sourceProperRebaseMatrix_det]
      norm_num
  | inr d =>
      rw [show occurrenceSourcePrefixMatrix (Sum.inr d) =
        rationalMatrix 3 sourceToCompanionNumerator *
          companionProperRebaseMatrix.map (Int.castRingHom ℚ) by rfl,
        Matrix.det_mul, sourceToCompanion_det_one]
      rw [show (companionProperRebaseMatrix.map (Int.castRingHom ℚ)).det = 1 by
        change ((Int.castRingHom ℚ).mapMatrix companionProperRebaseMatrix).det = 1
        rw [← RingHom.map_det, companionProperRebaseMatrix_det]
        norm_num]
      norm_num

theorem occurrenceSourcePrefixMatrix_carries
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceSourcePrefixMatrix occurrence).transpose *
        source.gram.map (Int.castRingHom ℚ) *
        occurrenceSourcePrefixMatrix occurrence =
      occurrenceSourceHalfGram occurrence := by
  cases occurrence with
  | inl d =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [occurrenceSourcePrefixMatrix, occurrenceSourceHalfGram,
          sourceProperRebaseMatrix, source, SixCoefficients.gram,
          brandtFirstGram, Matrix.mul_apply, Fin.sum_univ_succ]
  | inr d =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [occurrenceSourcePrefixMatrix, occurrenceSourceHalfGram,
          rationalMatrix, sourceToCompanionNumerator,
          companionProperRebaseMatrix, source, SixCoefficients.gram,
          brandtSecondGram, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The source prefix followed by the actual occurrence basis. -/
def occurrenceRawGenusMatrix (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  occurrenceSourcePrefixMatrix occurrence *
    occurrenceBasisCoordinateMatrix hp2 occurrence

theorem occurrenceRawGenusMatrix_det_abs (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    |(occurrenceRawGenusMatrix hp2 occurrence).det| = 1 := by
  rw [occurrenceRawGenusMatrix, Matrix.det_mul,
    occurrenceSourcePrefixMatrix_det, one_mul]
  exact occurrenceBasisCoordinateMatrix_det_abs_eq_one hp2 occurrence

theorem occurrenceRawGenusMatrix_carries (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceRawGenusMatrix hp2 occurrence).transpose *
        source.gram.map (Int.castRingHom ℚ) *
        occurrenceRawGenusMatrix hp2 occurrence =
      (occurrenceJonesPallCoefficients hp2 occurrence).gram.map
        (Int.castRingHom ℚ) := by
  rw [occurrenceJonesPallCoefficients_gram,
    occurrenceRawGenusMatrix, Matrix.transpose_mul]
  calc
    (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
          (occurrenceSourcePrefixMatrix occurrence).transpose *
          source.gram.map (Int.castRingHom ℚ) *
          (occurrenceSourcePrefixMatrix occurrence *
            occurrenceBasisCoordinateMatrix hp2 occurrence) =
        (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
          ((occurrenceSourcePrefixMatrix occurrence).transpose *
            source.gram.map (Int.castRingHom ℚ) *
            occurrenceSourcePrefixMatrix occurrence) *
          occurrenceBasisCoordinateMatrix hp2 occurrence := by
      noncomm_ring
    _ = (occurrenceBasisCoordinateMatrix hp2 occurrence).transpose *
          occurrenceSourceHalfGram occurrence *
          occurrenceBasisCoordinateMatrix hp2 occurrence := by
      rw [occurrenceSourcePrefixMatrix_carries]
    _ = (occurrenceJonesPallHalfGram hp2 occurrence).map
          (Int.castRingHom ℚ) :=
      (occurrenceHalfGram_cast_eq_pullback hp2 occurrence).symm

private theorem rationalMatrix_integral_mul (d : ℕ) (hd : d ≠ 0)
    (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    rationalMatrix d (A * B) =
      A.map (Int.castRingHom ℚ) * rationalMatrix d B := by
  ext i j
  simp [rationalMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp

private theorem rationalMatrix_mul (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0)
    (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    rationalMatrix (d * e) (A * B) =
      rationalMatrix d A * rationalMatrix e B := by
  ext i j
  simp [rationalMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp

/-- The exact common denominator of the raw source-to-occurrence chart.  The
second source branch retains the independent denominator-three companion
crossing instead of erasing it into rational entries. -/
def occurrenceGenusDenominator
    (occurrence : BrandtNeighborOccurrence (p := p)) : ℕ :=
  match occurrence with
  | .inl _ => p
  | .inr _ => 3 * p

/-- The integral numerator obtained by composing the proper source prefix
with the actual denominator-`p` occurrence basis numerator. -/
def occurrenceRawGenusNumerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  match occurrence with
  | .inl _ =>
      sourceProperRebaseMatrix * occurrenceBasisNumeratorMatrix hp2 occurrence
  | .inr _ =>
      sourceToCompanionNumerator *
        (companionProperRebaseMatrix *
          occurrenceBasisNumeratorMatrix hp2 occurrence)

theorem rationalMatrix_occurrenceRawGenusNumerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    rationalMatrix (occurrenceGenusDenominator occurrence)
        (occurrenceRawGenusNumerator hp2 occurrence) =
      occurrenceRawGenusMatrix hp2 occurrence := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  cases occurrence with
  | inl d =>
      rw [show occurrenceGenusDenominator (Sum.inl d) = p by rfl]
      rw [show occurrenceRawGenusNumerator hp2 (Sum.inl d) =
        sourceProperRebaseMatrix *
          occurrenceBasisNumeratorMatrix hp2 (Sum.inl d) by rfl]
      rw [rationalMatrix_integral_mul p hp0,
        rationalMatrix_occurrenceBasisNumerator]
      rfl
  | inr d =>
      rw [show occurrenceGenusDenominator (Sum.inr d) = 3 * p by rfl]
      rw [show occurrenceRawGenusNumerator hp2 (Sum.inr d) =
        sourceToCompanionNumerator *
          (companionProperRebaseMatrix *
            occurrenceBasisNumeratorMatrix hp2 (Sum.inr d)) by rfl]
      rw [rationalMatrix_mul 3 p (by decide) hp0,
        rationalMatrix_integral_mul p hp0,
        rationalMatrix_occurrenceBasisNumerator]
      simp [occurrenceRawGenusMatrix, occurrenceSourcePrefixMatrix,
        Matrix.mul_assoc]

private theorem rationalMatrix_neg (d : ℕ)
    (U : Matrix (Fin 3) (Fin 3) ℤ) :
    rationalMatrix d (-U) = -rationalMatrix d U := by
  ext i j
  simp [rationalMatrix]
  ring

/-- Orient all three numerator columns together.  If the actual retained
basis has negative orientation, this flips determinant sign while leaving
the quadratic pullback unchanged. -/
def occurrenceGenusNumerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  if (occurrenceRawGenusMatrix hp2 occurrence).det = 1 then
    occurrenceRawGenusNumerator hp2 occurrence
  else
    -occurrenceRawGenusNumerator hp2 occurrence

theorem rationalMatrix_occurrenceGenusNumerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    rationalMatrix (occurrenceGenusDenominator occurrence)
        (occurrenceGenusNumerator hp2 occurrence) =
      if (occurrenceRawGenusMatrix hp2 occurrence).det = 1 then
        occurrenceRawGenusMatrix hp2 occurrence
      else
        -occurrenceRawGenusMatrix hp2 occurrence := by
  by_cases h : (occurrenceRawGenusMatrix hp2 occurrence).det = 1
  · simp [occurrenceGenusNumerator, h,
      rationalMatrix_occurrenceRawGenusNumerator]
  · simp [occurrenceGenusNumerator, h, rationalMatrix_neg,
      rationalMatrix_occurrenceRawGenusNumerator]

theorem occurrenceGenusMatrix_det_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (rationalMatrix (occurrenceGenusDenominator occurrence)
      (occurrenceGenusNumerator hp2 occurrence)).det = 1 := by
  rw [rationalMatrix_occurrenceGenusNumerator]
  by_cases h : (occurrenceRawGenusMatrix hp2 occurrence).det = 1
  · simp [h]
  · simp only [h, ↓reduceIte, Matrix.det_neg]
    have habs := occurrenceRawGenusMatrix_det_abs hp2 occurrence
    have hnonpos : (occurrenceRawGenusMatrix hp2 occurrence).det ≤ 0 := by
      by_contra hn
      have hpos : 0 < (occurrenceRawGenusMatrix hp2 occurrence).det :=
        lt_of_not_ge hn
      rw [abs_of_pos hpos] at habs
      exact h habs
    rw [abs_of_nonpos hnonpos] at habs
    norm_num
    linarith

theorem occurrenceGenusMatrix_carries (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (rationalMatrix (occurrenceGenusDenominator occurrence)
      (occurrenceGenusNumerator hp2 occurrence)).transpose *
        source.gram.map (Int.castRingHom ℚ) *
      rationalMatrix (occurrenceGenusDenominator occurrence)
        (occurrenceGenusNumerator hp2 occurrence) =
      (occurrenceJonesPallCoefficients hp2 occurrence).gram.map
        (Int.castRingHom ℚ) := by
  rw [rationalMatrix_occurrenceGenusNumerator]
  by_cases h : (occurrenceRawGenusMatrix hp2 occurrence).det = 1
  · simpa [h] using occurrenceRawGenusMatrix_carries hp2 occurrence
  · simp only [h, ↓reduceIte, Matrix.transpose_neg]
    calc
      (-occurrenceRawGenusMatrix hp2 occurrence).transpose *
            source.gram.map (Int.castRingHom ℚ) *
            -occurrenceRawGenusMatrix hp2 occurrence =
          (occurrenceRawGenusMatrix hp2 occurrence).transpose *
            source.gram.map (Int.castRingHom ℚ) *
            occurrenceRawGenusMatrix hp2 occurrence := by
        simp only [Matrix.transpose_neg, neg_mul, mul_neg, neg_neg]
      _ = _ := occurrenceRawGenusMatrix_carries hp2 occurrence

private theorem prime_coprime_128 (hp2 : p ≠ 2) : p.Coprime 128 := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro h
  have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
  rw [h128] at h
  have hpdiv2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow h
  rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv2 with hp1 | hp2'
  · exact (Fact.out : p.Prime).ne_one hp1
  · exact hp2 hp2'

theorem occurrenceGenusDenominator_pos
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    0 < occurrenceGenusDenominator occurrence := by
  cases occurrence <;>
    simp [occurrenceGenusDenominator, (Fact.out : p.Prime).pos]

theorem occurrenceGenusDenominator_coprime (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceGenusDenominator occurrence).Coprime
      (2 * source.gram.det.natAbs) := by
  have hsource : 2 * source.gram.det.natAbs = 128 := by
    rw [source_det]
    norm_num
  rw [hsource]
  cases occurrence with
  | inl d =>
      change p.Coprime 128
      exact prime_coprime_128 hp2
  | inr d =>
      change (3 * p).Coprime 128
      exact (by norm_num : Nat.Coprime 3 128).mul_left
        (prime_coprime_128 hp2)

/-- Every actual odd-prime Brandt occurrence now returns the precise
Jones--Pall genus witness: an integral numerator, a denominator prime to
twice the source determinant, determinant one, and the exact Gram pullback. -/
def occurrenceRationalGenusTransport (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    RationalGenusTransport source
      (occurrenceJonesPallCoefficients hp2 occurrence) where
  denominator := occurrenceGenusDenominator occurrence
  denominator_pos := occurrenceGenusDenominator_pos occurrence
  numerator := occurrenceGenusNumerator hp2 occurrence
  denominator_coprime := occurrenceGenusDenominator_coprime hp2 occurrence
  same_determinant := by
    rw [source_det, occurrenceJonesPallCoefficients_det]
  determinant_one := occurrenceGenusMatrix_det_one hp2 occurrence
  carries_gram := occurrenceGenusMatrix_carries hp2 occurrence

/-! ## The exact mod-eight branch in Jones--Pall's source argument -/

private theorem square_emod_eight (x : ℤ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have hnonneg : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
  have hlt : x % 8 < 8 := by
    simpa using Int.emod_lt_abs x (by norm_num : (8 : ℤ) ≠ 0)
  have hs := (Int.mod_modEq x 8).pow 2
  interval_cases x % 8 <;> simp [Int.ModEq] at hs <;> omega

private theorem square_emod_eight_eq_one_iff (x : ℤ) :
    x ^ 2 % 8 = 1 ↔ x % 2 = 1 := by
  have hnonneg : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
  have hlt : x % 8 < 8 := by
    simpa using Int.emod_lt_abs x (by norm_num : (8 : ℤ) ≠ 0)
  have hs := (Int.mod_modEq x 8).pow 2
  have hp : (x % 8) % 2 = x % 2 :=
    Int.emod_emod_of_dvd x (by norm_num)
  interval_cases x % 8 <;> simp [Int.ModEq] at hs hp <;> omega

/-- Jones--Pall's exact two-adic split for
`f=x^2+4y^2+8z^2`: on the residue-one fibre, `y` is even and the remaining
branch is precisely the parity of `z` (with `x` odd). -/
theorem auxiliary_modEight_dichotomy (v : IntTriple)
    (h : auxiliary.quadratic v % 8 = 1) :
    (v.2.1 % 2 = 0 ∧ v.2.2 % 2 = 0) ∨
      (v.1 % 2 = 1 ∧ v.2.1 % 2 = 0 ∧ v.2.2 % 2 = 1) := by
  have hx := square_emod_eight v.1
  have hy := square_emod_eight v.2.1
  have h' : (v.1 ^ 2 % 8 + 4 * (v.2.1 ^ 2 % 8)) % 8 = 1 := by
    simpa [auxiliary, SixCoefficients.quadratic, Int.add_emod,
      Int.mul_emod] using h
  have hxone : v.1 ^ 2 % 8 = 1 := by
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
      simp [hx, hy] at h' <;> omega
  have hynot : v.2.1 ^ 2 % 8 ≠ 1 := by
    intro hyone
    rw [hxone, hyone] at h'
    norm_num at h'
  have hxodd : v.1 % 2 = 1 :=
    (square_emod_eight_eq_one_iff v.1).mp hxone
  have hyeven : v.2.1 % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one v.2.1 with h0 | h1
    · exact h0
    · exact False.elim
        (hynot ((square_emod_eight_eq_one_iff v.2.1).mpr h1))
  rcases Int.emod_two_eq_zero_or_one v.2.2 with hz | hz
  · exact Or.inl ⟨hyeven, hz⟩
  · exact Or.inr ⟨hxodd, hyeven, hz⟩

#print axioms SixCoefficients.gram_det
#print axioms sourceProperRebase_preserves
#print axioms companionProperRebase_preserves
#print axioms companion_gram_rebase
#print axioms source_isEisensteinReduced
#print axioms companion_isEisensteinReduced
#print axioms sourceToCompanionTransport
#print axioms occurrenceScaledSourceFullPolar
#print axioms rationalMatrix_occurrenceBasisNumerator
#print axioms occurrenceQuotientFullPolar_even
#print axioms occurrenceJonesPallCoefficients_gram
#print axioms occurrenceJonesPallCoefficients_det
#print axioms occurrenceJonesPallCoefficients_quadratic
#print axioms occurrenceJonesPallCoordinateEquiv_apply
#print axioms occurrenceJonesPallCoefficients_source_profile
#print axioms occurrenceHalfGram_cast_eq_pullback
#print axioms occurrenceRawGenusMatrix_carries
#print axioms occurrenceRationalGenusTransport
#print axioms auxiliary_modEight_dichotomy

end Soma.Holonics.Millennium.FamilyTunnellBrandtJonesPallNormalForm
