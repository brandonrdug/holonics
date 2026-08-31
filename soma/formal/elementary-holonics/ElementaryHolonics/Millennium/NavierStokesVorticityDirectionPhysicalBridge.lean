import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionFullStrain

/-!
# The direction-depleted Fourier receiver is the physical vortex-stretching occurrence

**[proved-derived]** The complete direction-remainder estimate already reaches the literal
complexified Jacobian on the spatial torus.  This owner removes the remaining codec seam: real
continuous-linear action, Euclidean inner product, vorticity, and the pointwise vortex-stretching
integrand commute exactly with coordinatewise complexification.  The Fourier inequality therefore
lands on the physical real receiver used by the periodic enstrophy law.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain

/-- Complexifying every addressed matrix entry commutes exactly with the real
continuous-linear action. -/
theorem complexMatrixAction_complexJacobianArrayOfCLM
    (D : Space →L[ℝ] Space) (v : Space) :
    complexMatrixAction (complexJacobianArrayOfCLM D) (complexOfRealSpace v) =
      complexOfRealSpace (D v) := by
  ext component
  change
    (∑ coordinate : Fin 3,
      complexJacobianArrayOfCLM D component coordinate *
        (v coordinate : ℂ)) = (D v component : ℂ)
  calc
    _ = ∑ coordinate : Fin 3,
        ((jacobianMatrix D component coordinate * v coordinate : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      simp only [complexJacobianArrayOfCLM]
      rw [jacobianMatrix_apply]
      unfold spatialBasisVector
      push_cast
      rfl
    _ = ((∑ coordinate : Fin 3,
        jacobianMatrix D component coordinate * v coordinate : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = (D v component : ℂ) := by
      rw [← continuousLinearMap_apply_coordinate D v component]

/-- The bilinear complex coordinate receiver restricts to the real Euclidean inner product on
the real complexification locus. -/
theorem complexDot_complexOfRealSpace
    (u v : Space) :
    complexDot (complexOfRealSpace u) (complexOfRealSpace v) =
      ((inner ℝ u v : ℝ) : ℂ) := by
  simp [complexDot, complexOfRealSpace, dotProduct, PiLp.inner_apply,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  ring

/-- The symmetric complex strain reading of a complexified real Jacobian is exactly the
complexification of real vortex-stretching work. -/
theorem complexStretchingReading_complexifiedJacobian
    (D : Space →L[ℝ] Space) (v : Space) :
    complexStretchingReading (complexOfRealSpace v)
        (symmetricComplexJacobianPart (complexJacobianArrayOfCLM D)) =
      ((inner ℝ (D v) v : ℝ) : ℂ) := by
  let J : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    complexJacobianArrayOfCLM D component coordinate
  have haction := complexMatrixAction_complexJacobianArrayOfCLM D v
  change complexMatrixAction J (complexOfRealSpace v) = complexOfRealSpace (D v) at haction
  change complexStretchingReading (complexOfRealSpace v)
      (symmetricComplexJacobianPart J) = ((inner ℝ (D v) v : ℝ) : ℂ)
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  change complexDot (complexOfRealSpace v)
      (complexMatrixAction J (complexOfRealSpace v)) = ((inner ℝ (D v) v : ℝ) : ℂ)
  rw [haction, complexDot_complexOfRealSpace, real_inner_comm]

/-- The actual complex vorticity chart is the coordinatewise complexification of the torus
vorticity occurrence, with the quotient representative removed from the observable statement. -/
theorem openPeriodicComplexVorticityAt_eq_torusComplexification
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicComplexVorticityAt solution t q =
      complexOfRealSpace (torusVorticityEvolution solution t q) := by
  rfl

/-- The real, quotient-descended pointwise vortex-stretching occurrence. -/
def openPeriodicPhysicalVortexStretchingAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℝ :=
  inner ℝ
    (openPeriodicTorusJacobianSlice solution t q
      (torusVorticityEvolution solution t q))
    (torusVorticityEvolution solution t q)

/-- Pullback through the spatial quotient returns the literal pointwise integrand used by the
periodic enstrophy receiver. -/
@[simp]
theorem openPeriodicPhysicalVortexStretchingAt_projection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (x : Space) :
    openPeriodicPhysicalVortexStretchingAt solution t (euclideanToSpatialTorus x) =
      inner ℝ
        (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
        (vorticityField velocity x t.1) := by
  simp [openPeriodicPhysicalVortexStretchingAt]

/-- **[proved-derived; formal-checked]** The complete Fourier strain chart is not a proxy: it is
exactly the complexification of the physical real vortex-stretching occurrence. -/
theorem openPeriodicFullStrainReading_eq_physical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullStrainReading solution t q =
      (openPeriodicPhysicalVortexStretchingAt solution t q : ℂ) := by
  rw [openPeriodicFullStrainReading,
    openPeriodicComplexVorticityAt_eq_torusComplexification]
  exact complexStretchingReading_complexifiedJacobian
    (openPeriodicTorusJacobianSlice solution t q)
    (torusVorticityEvolution solution t q)

/-- The complex norm on the full strain chart is exactly the absolute value of the real physical
reading; no comparison constant or discarded sign enters this chart transition. -/
theorem norm_openPeriodicFullStrainReading_eq_abs_physical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicFullStrainReading solution t q‖ =
      |openPeriodicPhysicalVortexStretchingAt solution t q| := by
  rw [openPeriodicFullStrainReading_eq_physical, Complex.norm_real,
    Real.norm_eq_abs]

/-- The exact direction-depletion plus reconstruction-tail estimate now controls the physical
real vortex-stretching occurrence on every frequency cube. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
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
  rw [← norm_openPeriodicFullStrainReading_eq_abs_physical]
  exact norm_openPeriodicFullStrainReading_frequencyCube_le solution t q radius

section Audit

#print axioms complexMatrixAction_complexJacobianArrayOfCLM
#print axioms complexDot_complexOfRealSpace
#print axioms complexStretchingReading_complexifiedJacobian
#print axioms openPeriodicComplexVorticityAt_eq_torusComplexification
#print axioms openPeriodicPhysicalVortexStretchingAt_projection
#print axioms openPeriodicFullStrainReading_eq_physical
#print axioms norm_openPeriodicFullStrainReading_eq_abs_physical
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
