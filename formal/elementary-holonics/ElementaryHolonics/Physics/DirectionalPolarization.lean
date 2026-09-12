import ElementaryHolonics.Computation.HolonicPolarizedCrystalTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Frame-relative directional polarization and its density receiver

The arrows name rays in a declared transverse polarization chart. They do not name absolute
spatial locations or the direction in which a photon propagates. Existing Jones sections and
the analyzer covector are reused. Coherent superposition and an incoherent density mixture are
different constructions even when one analyzer returns the same intensity.
-/

noncomputable section

namespace Soma.Holonics.Physics.DirectionalPolarization

open scoped BigOperators ComplexConjugate Matrix
open Soma.Holonics.Computation.HolonicPolarizedCrystalTransport

abbrev Density := Matrix JonesPolarization JonesPolarization ℂ

def linearDirection (horizontalPart verticalPart : ℝ) : JonesSection :=
  ![(horizontalPart : ℂ), (verticalPart : ℂ)]

def angleDirection (angle : ℝ) : JonesSection :=
  linearDirection (Real.cos angle) (Real.sin angle)

def diagonal : JonesSection := angleDirection (Real.pi / 4)
def antidiagonal : JonesSection := linearDirection (-(Real.sqrt 2 / 2)) (Real.sqrt 2 / 2)

scoped notation "∣↔⟩" => horizontal
scoped notation "∣↕⟩" => vertical
scoped notation "∣↗⟩" => diagonal
scoped notation "∣↖⟩" => antidiagonal

/-- A supplied local frame transports the direction as an existing Jones section. -/
def inFrame (frame : Matrix JonesPolarization JonesPolarization ℂ) (direction : JonesSection) :
    JonesSection := frame *ᵥ direction

def projector (direction : JonesSection) : Density :=
  fun i j => direction i * conj (direction j)

def mixed : Density := (1 / 2 : ℂ) • (1 : Density)

def densityReceiver (density : Density) (analyzer : JonesSection) : ℂ :=
  FiniteCoherentPathFamily.analyze analyzer (density *ᵥ analyzer)

theorem angle_overlap (source analyzer : ℝ) :
    FiniteCoherentPathFamily.analyze (angleDirection analyzer) (angleDirection source) =
      (Real.cos (source - analyzer) : ℂ) := by
  simp only [FiniteCoherentPathFamily.analyze, angleDirection, linearDirection,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.conj_ofReal, Real.cos_sub, Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem malus_relative_angle (source analyzer : ℝ) :
    Complex.normSq (FiniteCoherentPathFamily.analyze
      (angleDirection analyzer) (angleDirection source)) = Real.cos (source - analyzer) ^ 2 := by
  rw [angle_overlap, Complex.normSq_ofReal]
  ring

/-- Every real orthonormal pair gives the same unpolarized density. -/
theorem rotated_pair_same_mixture (c s : ℝ) (unit : c ^ 2 + s ^ 2 = 1) :
    (1 / 2 : ℂ) • (projector (linearDirection c s) + projector (linearDirection (-s) c)) = mixed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, linearDirection, mixed, Matrix.one_apply, smul_eq_mul]
  all_goals try ring
  all_goals
    have unitC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast unit
    linear_combination unitC

theorem mixed_receiver_half (c s : ℝ) (unit : c ^ 2 + s ^ 2 = 1) :
    densityReceiver mixed (linearDirection c s) = 1 / 2 := by
  simp [densityReceiver, FiniteCoherentPathFamily.analyze, mixed, linearDirection,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul]
  have unitC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast unit
  linear_combination (1 / 2 : ℂ) * unitC

/-- The off-diagonal coherence is information that the H/V intensity receiver discards. -/
def diagonalDensity : Density := (1 / 2 : ℂ) • !![1, 1; 1, 1]

theorem equal_horizontal_distinct_diagonal :
    densityReceiver diagonalDensity horizontal = 1 / 2 ∧
      densityReceiver mixed horizontal = 1 / 2 ∧
      densityReceiver diagonalDensity (linearDirection 1 1) = 2 ∧
      densityReceiver mixed (linearDirection 1 1) = 1 := by
  norm_num [densityReceiver, diagonalDensity, mixed, horizontal, linearDirection,
    FiniteCoherentPathFamily.analyze, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, smul_eq_mul]

/-- Conventional Stokes normalization: S0 is the trace, with S1 the H/V contrast. -/
def stokesMatrix (s0 s1 s2 s3 : ℝ) : Density :=
  !![((s0 + s1 : ℝ) : ℂ) / 2, ((s2 : ℂ) - Complex.I * s3) / 2;
     ((s2 : ℂ) + Complex.I * s3) / 2, ((s0 - s1 : ℝ) : ℂ) / 2]

theorem stokes_determinant (s0 s1 s2 s3 : ℝ) :
    (stokesMatrix s0 s1 s2 s3).det =
      (((s0 ^ 2 - s1 ^ 2 - s2 ^ 2 - s3 ^ 2) / 4 : ℝ) : ℂ) := by
  simp only [stokesMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  have imaginary : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (s3 : ℂ) ^ 2 / 4 * imaginary

/-- Unimodular Jones congruence preserves the Stokes quadratic form through the determinant.
It may change the trace/intensity, unlike a unitary polarization rotation. -/
theorem determinant_unimodular_transport (jones density : Density) (unitDet : jones.det = 1) :
    (jones * density * jones.conjTranspose).det = density.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, unitDet]
  simp

/-- The alternating pairing of two Jones directions, used before any scalar intensity quotient. -/
def wedge (left right : JonesSection) : ℂ :=
  left 0 * right 1 - left 1 * right 0

@[simp] theorem wedge_self (direction : JonesSection) : wedge direction direction = 0 := by
  simp [wedge, mul_comm]

theorem wedge_transport (frame : Density) (left right : JonesSection) :
    wedge (frame *ᵥ left) (frame *ᵥ right) = frame.det * wedge left right := by
  simp [wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- A four-ray projective receiver. Its use requires the two denominator pairings to be nonzero. -/
def rayCrossRatio (a b c d : JonesSection) : ℂ :=
  wedge a c * wedge b d / (wedge a d * wedge b c)

/-- The projective four-ray relation is invariant under a common invertible local frame.
The rays themselves and their cross-ratio may still change under physical evolution. -/
theorem rayCrossRatio_transport (frame : Density) (invertible : frame.det ≠ 0)
    (a b c d : JonesSection) (ad : wedge a d ≠ 0) (bc : wedge b c ≠ 0) :
    rayCrossRatio (frame *ᵥ a) (frame *ᵥ b) (frame *ᵥ c) (frame *ᵥ d) =
      rayCrossRatio a b c d := by
  simp only [rayCrossRatio, wedge_transport]
  field_simp [invertible, ad, bc]

theorem rayCrossRatio_rescale (a b c d : JonesSection) (ka kb kc kd : ℂ)
    (ha : ka ≠ 0) (hb : kb ≠ 0) (hc : kc ≠ 0) (hd : kd ≠ 0)
    (ad : wedge a d ≠ 0) (bc : wedge b c ≠ 0) :
    rayCrossRatio (ka • a) (kb • b) (kc • c) (kd • d) = rayCrossRatio a b c d := by
  have scale (u v : JonesSection) (x y : ℂ) : wedge (x • u) (y • v) = x * y * wedge u v := by
    simp [wedge, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [rayCrossRatio, scale]
  field_simp [ha, hb, hc, hd, ad, bc]

#print axioms malus_relative_angle
#print axioms rotated_pair_same_mixture
#print axioms mixed_receiver_half
#print axioms equal_horizontal_distinct_diagonal
#print axioms stokes_determinant
#print axioms determinant_unimodular_transport
#print axioms rayCrossRatio_transport
#print axioms rayCrossRatio_rescale

end Soma.Holonics.Physics.DirectionalPolarization
