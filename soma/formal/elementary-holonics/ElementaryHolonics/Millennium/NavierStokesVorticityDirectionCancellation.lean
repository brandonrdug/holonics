import ElementaryHolonics.Millennium.NavierStokesHodgeBandReconstruction
import ElementaryHolonics.Millennium.NavierStokesVorticityStrainDifference

/-!
# Exact vorticity-direction cancellation in the torus Hodge carrier

**[proved-derived]** The genuine-torus Fourier owner already reconstructs every nonzero velocity
mode from the actual vorticity mode.  This file takes the symmetric face of that reconstruction
and evaluates it through a fixed vorticity receiver.  The result is an exact scalar-triple-product
law: a source component aligned with the receiving vorticity contributes zero stretching.

Consequently every finite Hodge population may subtract an arbitrary receiver-aligned component
from every addressed source mode without changing its stretching return.  This is the algebraic
direction-difference cancellation behind the Constantin--Fefferman geometric route.  No angular
regularity, singular-integral estimate, or global regularity conclusion is assumed here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## The symmetric complex Hodge face -/

/-- Matrix action on the complex three-coordinate Fourier receiver. -/
def complexMatrixAction (J : ComplexMatrix3) (v : ComplexVector) : ComplexVector :=
  Matrix.mulVec J v

/-- The transpose-symmetric face of one complex Fourier Jacobian. -/
def symmetricComplexJacobianPart (J : ComplexMatrix3) : ComplexMatrix3 :=
  (2 : ℂ)⁻¹ • (J + J.transpose)

/-- The complex bilinear stretching reading at a fixed receiving vorticity. -/
def complexStretchingReading
    (receiver : ComplexVector) (J : ComplexMatrix3) : ℂ :=
  complexDot receiver (complexMatrixAction J receiver)

/-- Symmetrizing a Jacobian does not alter its quadratic stretching reading. -/
theorem complexStretchingReading_symmetricComplexJacobianPart
    (receiver : ComplexVector) (J : ComplexMatrix3) :
    complexStretchingReading receiver (symmetricComplexJacobianPart J) =
      complexStretchingReading receiver J := by
  simp [complexStretchingReading, symmetricComplexJacobianPart,
    complexMatrixAction, complexDot, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The symmetric strain coefficient reconstructed from one addressed vorticity coefficient. -/
def hodgeStrainMode
    (frequency : SpatialFrequency) (source : ComplexVector) : ComplexMatrix3 :=
  symmetricComplexJacobianPart (hodgeJacobianMode frequency source)

/-- One addressed source-to-receiver stretching occurrence. -/
def hodgeStrainModeReading
    (frequency : SpatialFrequency) (receiver source : ComplexVector) : ℂ :=
  complexStretchingReading receiver (hodgeStrainMode frequency source)

/-- **Exact scalar-triple-product law.**  At a nonzero frequency, stretching is the product of
the receiver's longitudinal frequency face and its oriented cross face with the source, divided
by the exact squared-frequency modulus. -/
theorem hodgeStrainModeReading_eq_scalarTriple
    {frequency : SpatialFrequency} (hfrequency : frequency ≠ 0)
    (receiver source : ComplexVector) :
    hodgeStrainModeReading frequency receiver source =
      -(complexDot receiver (complexFrequencyVector frequency) *
          complexDot receiver
            (complexCross (complexFrequencyVector frequency) source)) /
        (frequencySquared frequency : ℂ) := by
  rw [hodgeStrainModeReading, hodgeStrainMode,
    complexStretchingReading_symmetricComplexJacobianPart]
  have hs : (frequencySquared frequency : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (frequencySquared_pos hfrequency).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp [complexStretchingReading, complexMatrixAction, complexDot,
    hodgeJacobianMode, nonzeroModeHodgeReconstruction, fourierJacobianMode,
    complexCross, complexFrequencyVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  field_simp [hs, hpi]
  rw [Complex.I_sq]
  ring

/-- A source vorticity component parallel to the receiving vorticity contributes no stretching. -/
theorem hodgeStrainModeReading_aligned_eq_zero
    (frequency : SpatialFrequency) (receiver : ComplexVector) (amplitude : ℂ) :
    hodgeStrainModeReading frequency receiver (amplitude • receiver) = 0 := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [hodgeStrainModeReading, hodgeStrainMode, hodgeJacobianMode_zero]
    simp [symmetricComplexJacobianPart, complexStretchingReading, complexMatrixAction,
      complexDot]
  · rw [hodgeStrainModeReading_eq_scalarTriple hfrequency]
    have hcross : complexDot receiver
        (complexCross (complexFrequencyVector frequency) (amplitude • receiver)) = 0 := by
      simp [complexDot, complexCross, complexFrequencyVector, crossProduct, dotProduct,
        Fin.sum_univ_succ]
      ring
    rw [hcross]
    ring

/-- **Exact direction-difference cancellation.**  Removing any receiver-aligned component from
an addressed source leaves the stretching occurrence unchanged. -/
theorem hodgeStrainModeReading_sub_aligned
    (frequency : SpatialFrequency) (receiver source : ComplexVector) (amplitude : ℂ) :
    hodgeStrainModeReading frequency receiver (source - amplitude • receiver) =
      hodgeStrainModeReading frequency receiver source := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [hodgeStrainModeReading, hodgeStrainMode, hodgeJacobianMode_zero,
      hodgeStrainModeReading, hodgeStrainMode, hodgeJacobianMode_zero]
  · rw [hodgeStrainModeReading_eq_scalarTriple hfrequency,
      hodgeStrainModeReading_eq_scalarTriple hfrequency]
    have hcross : complexDot receiver
        (complexCross (complexFrequencyVector frequency)
          (source - amplitude • receiver)) =
        complexDot receiver (complexCross (complexFrequencyVector frequency) source) := by
      simp [complexDot, complexCross, complexFrequencyVector, crossProduct, dotProduct,
        Fin.sum_univ_succ]
      ring
    rw [hcross]

/-! ## Finite addressed populations and the actual solution carrier -/

/-- Stretching returned by a declared finite population of reconstructed vorticity sources. -/
def finiteHodgeStrainReading
    (modes : Finset SpatialFrequency) (receiver : ComplexVector)
    (source : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ frequency ∈ modes, hodgeStrainModeReading frequency receiver (source frequency)

/-- Every addressed source in a finite population may be replaced by its direction remainder. -/
theorem finiteHodgeStrainReading_sub_aligned
    (modes : Finset SpatialFrequency) (receiver : ComplexVector)
    (source : SpatialFrequency → ComplexVector) (amplitude : SpatialFrequency → ℂ) :
    finiteHodgeStrainReading modes receiver
        (fun frequency ↦ source frequency - amplitude frequency • receiver) =
      finiteHodgeStrainReading modes receiver source := by
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  exact hodgeStrainModeReading_sub_aligned frequency receiver
    (source frequency) (amplitude frequency)

/-- The actual pointwise vorticity of an admitted solution slice, embedded in the complex Fourier
receiver at one genuine torus point. -/
def openPeriodicComplexVorticityAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ComplexVector :=
  fun component ↦
    (vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) component : ℝ)

/-- Each actual source coefficient is transported to the receiver point by its torus character. -/
def openPeriodicTransportedVorticityMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) : ComplexVector :=
  UnitAddTorus.mFourier frequency q •
    openPeriodicVorticityFourierMode solution t frequency

/-- The exact finite Hodge-strain reading of an admitted periodic solution occurrence. -/
def openPeriodicFiniteHodgeStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) : ℂ :=
  finiteHodgeStrainReading modes (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q)

/-- **[proved-derived; formal-checked]** On the actual periodic solution carrier, every finite
Hodge-strain population factors exactly through source vorticity after subtracting an arbitrary
component aligned with the receiving pointwise vorticity.  The returned remainder retains the
frequency, character transport, receiver, and orientation of every occurrence. -/
theorem openPeriodicFiniteHodgeStrainReading_eq_directionRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency)
    (amplitude : SpatialFrequency → ℂ) :
    finiteHodgeStrainReading modes (openPeriodicComplexVorticityAt solution t q)
        (fun frequency ↦
          openPeriodicTransportedVorticityMode solution t q frequency -
            amplitude frequency • openPeriodicComplexVorticityAt solution t q) =
      openPeriodicFiniteHodgeStrainReading solution t q modes := by
  exact finiteHodgeStrainReading_sub_aligned modes
    (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q) amplitude

section Audit

#print axioms complexStretchingReading_symmetricComplexJacobianPart
#print axioms hodgeStrainModeReading_eq_scalarTriple
#print axioms hodgeStrainModeReading_aligned_eq_zero
#print axioms hodgeStrainModeReading_sub_aligned
#print axioms finiteHodgeStrainReading_sub_aligned
#print axioms openPeriodicFiniteHodgeStrainReading_eq_directionRemainder

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
