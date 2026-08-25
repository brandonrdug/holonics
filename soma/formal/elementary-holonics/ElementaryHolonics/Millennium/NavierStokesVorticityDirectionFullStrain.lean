import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailDecay
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge

/-!
# Full periodic strain as finite direction depletion plus the exact Fourier tail

**[proved-derived]** Complete Jacobian Fourier reconstruction was already present in the tree.
This owner composes it with the actual finite-band direction-remainder bound.  The full pointwise
strain reading splits exactly into the finite depleted return and the addressed infinite
coefficient tail.  A matrix-action estimate bounds the tail, and the existing weighted `H³` law
supplies its explicit reciprocal scale.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge

/-- One matrix row acting on a vector is controlled by the complete matrix norm and the explicit
coordinate `L¹` receiver. -/
theorem norm_complexMatrixAction_apply_le
    (J : ComplexJacobianArray) (v : ComplexVector) (component : Fin 3) :
    ‖complexMatrixAction J v component‖ ≤ ‖J‖ * complexVectorL1 v := by
  rw [complexMatrixAction, Matrix.mulVec, dotProduct]
  calc
    ‖∑ coordinate : Fin 3, J component coordinate * v coordinate‖ ≤
        ∑ coordinate : Fin 3, ‖J component coordinate * v coordinate‖ := norm_sum_le _ _
    _ = ∑ coordinate : Fin 3, ‖J component coordinate‖ * ‖v coordinate‖ := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      rw [norm_mul]
    _ ≤ ∑ coordinate : Fin 3, ‖J‖ * ‖v coordinate‖ := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact mul_le_mul_of_nonneg_right
        ((norm_le_pi_norm (J component) coordinate).trans (norm_le_pi_norm J component))
        (norm_nonneg _)
    _ = ‖J‖ * complexVectorL1 v := by
      simp [complexVectorL1, Fin.sum_univ_succ]
      ring

/-- The quadratic stretching receiver is controlled by the matrix norm and two copies of the
receiving-vector `L¹` face. -/
theorem norm_complexStretchingReading_le
    (receiver : ComplexVector) (J : ComplexJacobianArray) :
    ‖complexStretchingReading receiver J‖ ≤
      ‖J‖ * complexVectorL1 receiver ^ 2 := by
  rw [complexStretchingReading, complexDot, dotProduct]
  calc
    ‖∑ component : Fin 3,
        receiver component * complexMatrixAction J receiver component‖ ≤
      ∑ component : Fin 3,
        ‖receiver component * complexMatrixAction J receiver component‖ := norm_sum_le _ _
    _ = ∑ component : Fin 3,
        ‖receiver component‖ * ‖complexMatrixAction J receiver component‖ := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      rw [norm_mul]
    _ ≤ ∑ component : Fin 3,
        ‖receiver component‖ * (‖J‖ * complexVectorL1 receiver) := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact mul_le_mul_of_nonneg_left
        (norm_complexMatrixAction_apply_le J receiver component) (norm_nonneg _)
    _ = ‖J‖ * complexVectorL1 receiver ^ 2 := by
      simp [complexVectorL1, Fin.sum_univ_succ]
      ring

/-- The literal full symmetric-strain reading of an admitted periodic solution occurrence. -/
def openPeriodicFullStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℂ :=
  complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (openPeriodicTorusJacobianArraySlice solution t q))

/-- The full strain return is exactly its finite depleted population plus the addressed
complementary Fourier tail. -/
theorem openPeriodicFullStrainReading_eq_finite_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    openPeriodicFullStrainReading solution t q =
      openPeriodicFiniteHodgeStrainReading solution t q modes +
        complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicJacobianArrayFourierTail solution t modes q)) := by
  rw [openPeriodicFullStrainReading,
    openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail,
    symmetricComplexJacobianPart_add, complexStretchingReading_add,
    ← openPeriodicFiniteHodgeStrainReading_eq_symmetricActualJacobianBand]

/-- The full strain is bounded by the exact finite direction-remainder population plus the exact
coefficient reconstruction fibre. -/
theorem norm_openPeriodicFullStrainReading_le_remainder_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          finiteDirectionRemainderMass modes
            (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicTransportedVorticityMode solution t q) +
        openPeriodicJacobianCoefficientTailMass solution t modes *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  rw [openPeriodicFullStrainReading_eq_finite_add_tail]
  refine (norm_add_le _ _).trans (add_le_add
    (norm_openPeriodicFiniteHodgeStrainReading_le_directionRemainderMass
      solution t q modes) ?_)
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  exact (norm_complexStretchingReading_le
      (openPeriodicComplexVorticityAt solution t q)
      (openPeriodicJacobianArrayFourierTail solution t modes q)).trans
    (mul_le_mul_of_nonneg_right
      (norm_openPeriodicJacobianArrayFourierTail_le solution t modes q)
      (sq_nonneg _))

/-- **[proved-derived; formal-checked]** On a frequency cube, the complete reconstruction tail
has the explicit reciprocal weighted-`H³` scale already proved for the actual solution slice. -/
theorem norm_openPeriodicFullStrainReading_frequencyCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          finiteDirectionRemainderMass (frequencyCube radius)
            (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicTransportedVorticityMode solution t q) +
        ((2 * Real.pi) *
            Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  refine (norm_openPeriodicFullStrainReading_le_remainder_add_tail
    solution t q (frequencyCube radius)).trans ?_
  have htail :
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 ≤
        ((2 * Real.pi) *
            Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 :=
    mul_le_mul_of_nonneg_right
      (openPeriodicJacobianCoefficientTailMass_frequencyCube_le solution t radius)
      (sq_nonneg _)
  exact add_le_add_right htail _

section Audit

#print axioms norm_complexMatrixAction_apply_le
#print axioms norm_complexStretchingReading_le
#print axioms openPeriodicFullStrainReading_eq_finite_add_tail
#print axioms norm_openPeriodicFullStrainReading_le_remainder_add_tail
#print axioms norm_openPeriodicFullStrainReading_frequencyCube_le

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
