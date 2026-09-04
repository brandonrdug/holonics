import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-!
# Gluing the direction-remainder return to the actual finite Jacobian band

**[proved-derived]** The direction-remainder line was constructed mode by mode from the same exact
Hodge ascent used by the existing finite Jacobian projector.  This owner proves the missing gluing
receipt: Hodge ascent, symmetrization, matrix action, and the quadratic stretching receiver commute
with the complete addressed finite sum.  The resulting scalar is exactly the symmetric-strain
reading of the actual finite Jacobian band, not a parallel Fourier expression.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-- Hodge Jacobian ascent is complex-linear in its vorticity source. -/
theorem hodgeJacobianMode_smul
    (frequency : SpatialFrequency) (amplitude : ℂ) (source : ComplexVector) :
    hodgeJacobianMode frequency (amplitude • source) =
      amplitude • hodgeJacobianMode frequency source := by
  have hreconstruction :
      nonzeroModeHodgeReconstruction frequency (amplitude • source) =
        amplitude • nonzeroModeHodgeReconstruction frequency source := by
    unfold nonzeroModeHodgeReconstruction complexCross
    rw [map_smul]
    simp only [smul_smul]
    congr 1
    ring
  funext component coordinate
  let multiplier : ℂ :=
    2 * (Real.pi : ℂ) * Complex.I * (frequency coordinate : ℂ)
  change multiplier *
      nonzeroModeHodgeReconstruction frequency (amplitude • source) component =
    amplitude *
      (multiplier * nonzeroModeHodgeReconstruction frequency source component)
  rw [hreconstruction]
  change multiplier * (amplitude * _) = amplitude * (multiplier * _)
  ring

/-- Symmetrization preserves the zero matrix. -/
@[simp]
theorem symmetricComplexJacobianPart_zero :
    symmetricComplexJacobianPart (0 : ComplexMatrix3) = 0 := by
  ext component coordinate
  simp [symmetricComplexJacobianPart]

/-- Symmetrization preserves additive incidence. -/
theorem symmetricComplexJacobianPart_add (A B : ComplexMatrix3) :
    symmetricComplexJacobianPart (A + B) =
      symmetricComplexJacobianPart A + symmetricComplexJacobianPart B := by
  ext component coordinate
  simp [symmetricComplexJacobianPart]
  ring

/-- The complex quadratic stretching receiver preserves additive Jacobian incidence. -/
theorem complexStretchingReading_add
    (receiver : ComplexVector) (A B : ComplexMatrix3) :
    complexStretchingReading receiver (A + B) =
      complexStretchingReading receiver A + complexStretchingReading receiver B := by
  simp [complexStretchingReading, complexMatrixAction, complexDot, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The quadratic receiver of a zero Jacobian is zero. -/
@[simp]
theorem complexStretchingReading_zero (receiver : ComplexVector) :
    complexStretchingReading receiver (0 : ComplexMatrix3) = 0 := by
  simp [complexStretchingReading, complexMatrixAction, complexDot]

/-- Symmetric quadratic reading commutes with an arbitrary finite addressed matrix population. -/
theorem complexStretchingReading_symmetric_sum
    (receiver : ComplexVector) (modes : Finset SpatialFrequency)
    (J : SpatialFrequency → ComplexMatrix3) :
    complexStretchingReading receiver
        (symmetricComplexJacobianPart (∑ frequency ∈ modes, J frequency)) =
      ∑ frequency ∈ modes,
        complexStretchingReading receiver
          (symmetricComplexJacobianPart (J frequency)) := by
  classical
  induction modes using Finset.induction_on with
  | empty => simp
  | @insert frequency modes hfrequency ih =>
      rw [Finset.sum_insert hfrequency, Finset.sum_insert hfrequency,
        symmetricComplexJacobianPart_add, complexStretchingReading_add, ih]

/-- A transported source coefficient may be moved through Hodge ascent before symmetrization. -/
theorem symmetricComplexJacobianPart_smul_hodgeJacobianMode
    (frequency : SpatialFrequency) (amplitude : ℂ) (source : ComplexVector) :
    symmetricComplexJacobianPart (amplitude • hodgeJacobianMode frequency source) =
      hodgeStrainMode frequency (amplitude • source) := by
  rw [hodgeStrainMode, hodgeJacobianMode_smul]
  apply congrArg symmetricComplexJacobianPart
  ext component coordinate
  rfl

/-- **Exact finite-band bridge.**  The modewise direction carrier is the symmetric-strain
quadratic reading of the existing Hodge-reconstructed finite Jacobian projector. -/
theorem openPeriodicFiniteHodgeStrainReading_eq_symmetricHodgeBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    openPeriodicFiniteHodgeStrainReading solution t q modes =
      complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicHodgeJacobianBandProjector solution t modes q)) := by
  rw [openPeriodicFiniteHodgeStrainReading, finiteHodgeStrainReading,
    openPeriodicHodgeJacobianBandProjector, finiteFourierSynthesis]
  unfold openPeriodicTransportedVorticityMode
  change
    (∑ frequency ∈ modes,
      hodgeStrainModeReading frequency (openPeriodicComplexVorticityAt solution t q)
        (UnitAddTorus.mFourier frequency q •
          openPeriodicVorticityFourierMode solution t frequency)) =
      complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (Matrix.of fun component coordinate ↦
            (∑ frequency ∈ modes,
              UnitAddTorus.mFourier frequency q •
                hodgeJacobianMode frequency
                  (openPeriodicVorticityFourierMode solution t frequency))
              component coordinate))
  have hmatrixSum :
      (Matrix.of fun component coordinate ↦
        (∑ frequency ∈ modes,
          UnitAddTorus.mFourier frequency q •
            hodgeJacobianMode frequency
              (openPeriodicVorticityFourierMode solution t frequency))
          component coordinate) =
        ∑ frequency ∈ modes,
          Matrix.of fun component coordinate ↦
            (UnitAddTorus.mFourier frequency q •
              hodgeJacobianMode frequency
                (openPeriodicVorticityFourierMode solution t frequency))
              component coordinate := by
    ext component coordinate
    simp only [Matrix.of_apply, Matrix.sum_apply, Finset.sum_apply]
  rw [hmatrixSum, complexStretchingReading_symmetric_sum]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [hodgeStrainModeReading]
  apply congrArg (complexStretchingReading (openPeriodicComplexVorticityAt solution t q))
  rw [← symmetricComplexJacobianPart_smul_hodgeJacobianMode]
  apply congrArg symmetricComplexJacobianPart
  ext component coordinate
  rfl

/-- **[proved-derived; formal-checked]** The same scalar is the symmetric-strain reading of the
actual finite Jacobian band, using the checked equality between Hodge reconstruction and the
solution's derivative coefficients. -/
theorem openPeriodicFiniteHodgeStrainReading_eq_symmetricActualJacobianBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    openPeriodicFiniteHodgeStrainReading solution t q modes =
      complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicJacobianBandProjector solution t modes q)) := by
  rw [openPeriodicFiniteHodgeStrainReading_eq_symmetricHodgeBand,
    openPeriodicHodgeJacobianBandProjector_eq_actual]

/-- The canonical direction-remainder bound therefore controls the actual finite Jacobian
strain receiver itself. -/
theorem norm_symmetricActualJacobianBand_reading_le_directionRemainderMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicJacobianBandProjector solution t modes q))‖ ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
        finiteDirectionRemainderMass modes
          (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicTransportedVorticityMode solution t q) := by
  rw [← openPeriodicFiniteHodgeStrainReading_eq_symmetricActualJacobianBand]
  exact norm_openPeriodicFiniteHodgeStrainReading_le_directionRemainderMass
    solution t q modes

section Audit

#print axioms hodgeJacobianMode_smul
#print axioms complexStretchingReading_symmetric_sum
#print axioms openPeriodicFiniteHodgeStrainReading_eq_symmetricHodgeBand
#print axioms openPeriodicFiniteHodgeStrainReading_eq_symmetricActualJacobianBand
#print axioms norm_symmetricActualJacobianBand_reading_le_directionRemainderMass

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
