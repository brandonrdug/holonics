import ElementaryHolonics.Millennium.NavierStokesPeriodicHorizontalMean
import ElementaryHolonics.Millennium.NavierStokesAxialPressureMode

/-!
# The actual axial pressure mean

The unforced periodic momentum equation fixes every nonconstant axial pressure mode through the
horizontal mean of vertical velocity squared. Complete Fourier reconstruction returns the actual
mean and its derivative. Only the spatially constant pressure gauge remains free.
-/

noncomputable section
open ContDiff Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesPressureMean
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusHorizontalMean
open Soma.Holonics.Millennium.NavierStokesHorizontalMean
open Soma.Holonics.Millennium.NavierStokesPeriodicHorizontalMean
open Soma.Holonics.Millennium.NavierStokesAxialPressureMode

theorem scalarFourierMode_add (f g : Space → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hpf : IsOnePeriodic f) (hpg : IsOnePeriodic g)
    (k : SpatialFrequency) :
    scalarFourierMode (fun x ↦ f x + g x) (hf.add hg)
      (fun x i ↦ by simp only [hpf x i, hpg x i]) k =
      scalarFourierMode f hf hpf k + scalarFourierMode g hg hpg k := by
  let F := periodicTorusLift (complexScalarField f)
    (continuous_complexScalarField hf) (isOnePeriodic_complexScalarField hpf)
  let G := periodicTorusLift (complexScalarField g)
    (continuous_complexScalarField hg) (isOnePeriodic_complexScalarField hpg)
  have hsum : periodicTorusLift (complexScalarField (fun x ↦ f x + g x))
      (continuous_complexScalarField (hf.add hg))
      (isOnePeriodic_complexScalarField (fun x i ↦ by simp only [hpf x i, hpg x i])) = F + G := by
    ext q
    rw [← euclideanToSpatialTorus_representative q]
    dsimp only [F, G]
    simp only [ContinuousMap.add_apply, periodicTorusLift_projection, complexScalarField,
      Complex.ofReal_add]
  unfold scalarFourierMode
  rw [hsum]
  exact torusSpatialFourierCoeff_add F G k

def verticalVelocitySquare (u : InitialVelocity) : Space → ℝ := fun x ↦ (u x 2) ^ 2

theorem verticalVelocitySquare_contDiff (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (verticalVelocitySquare u) :=
  (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp hu).pow 2)

theorem verticalVelocitySquare_periodic (u : InitialVelocity) (hu : IsOnePeriodic u) :
    IsOnePeriodic (verticalVelocitySquare u) :=
  fun x i ↦ congrArg (fun v : Space ↦ (v 2) ^ 2) (hu x i)

/-- The scalar pressure gauge is retained as the mean at an arbitrary reference height. -/
theorem pressure_mean_add_vertical_square_mean_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (z w : ℝ) :
    horizontalMean (fun x ↦ pressure x t.1) z +
        horizontalMean (verticalVelocitySquare (fun x ↦ velocity x t.1)) z =
      horizontalMean (fun x ↦ pressure x t.1) w +
        horizontalMean (verticalVelocitySquare (fun x ↦ velocity x t.1)) w := by
  let p := fun x ↦ pressure x t.1
  let q := verticalVelocitySquare (fun x ↦ velocity x t.1)
  have hp : ContDiff ℝ ∞ p := openPeriodicSolutionOn_pressureSlice_contDiff solution t.2
  have hq : ContDiff ℝ ∞ q := verticalVelocitySquare_contDiff _
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
  have hpp : IsOnePeriodic p := solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hqp : IsOnePeriodic q := verticalVelocitySquare_periodic _
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
  have hsumperiodic : IsOnePeriodic (fun x ↦ p x + q x) :=
    fun x i ↦ by simp only [hpp x i, hqp x i]
  have hzero (n : ℤ) (hn : n ≠ 0) :
      scalarFourierMode (fun x ↦ p x + q x) (hp.continuous.add hq.continuous)
        hsumperiodic (axialFrequency n) = 0 := by
    rw [scalarFourierMode_add p q hp.continuous hq.continuous hpp hqp]
    have h := axial_pressure_scalar_mode_eq_neg_vertical_velocity_square_mode
      solution t (axialFrequency n) (by rfl) (by rfl) (by simpa [axialFrequency] using hn)
    change scalarFourierMode p hp.continuous hpp (axialFrequency n) =
      - scalarFourierMode q hq.continuous hqp (axialFrequency n) at h
    rw [h, neg_add_cancel]
  have h := horizontalMean_eq_of_axial_modes_zero (fun x ↦ p x + q x)
    (hp.continuous.add hq.continuous) hsumperiodic hzero z w
  simpa only [horizontalMean_add p q hp.continuous hq.continuous] using h

/-- The derivative is of the actual complete horizontal mean, including vertical variance. -/
theorem pressure_mean_hasDerivAt_neg_vertical_square_mean
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (z : ℝ) :
    HasDerivAt (horizontalMean (fun x ↦ pressure x t.1))
      (- horizontalMean (fun x ↦ fderiv ℝ
        (verticalVelocitySquare (fun x ↦ velocity x t.1)) x
        (EuclideanSpace.single (2 : Fin 3) 1)) z) z := by
  let p := fun x ↦ pressure x t.1
  let q := verticalVelocitySquare (fun x ↦ velocity x t.1)
  have hq : ContDiff ℝ 2 q :=
    (verticalVelocitySquare_contDiff _
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : horizontalMean p = fun ζ ↦
      (horizontalMean p 0 + horizontalMean q 0) - horizontalMean q ζ := by
    funext ζ
    have h := pressure_mean_add_vertical_square_mean_eq solution t ζ 0
    change horizontalMean p ζ + horizontalMean q ζ = _ at h
    linarith
  rw [heq]
  convert (horizontalMean_hasDerivAt q hq z).const_sub
    (horizontalMean p 0 + horizontalMean q 0) using 1

theorem horizontalMean_pressure_axialDerivative_eq_neg_vertical_square_axialDerivative
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (z : ℝ) :
    horizontalMean (fun x ↦ fderiv ℝ (fun x ↦ pressure x t.1) x
        (EuclideanSpace.single (2 : Fin 3) 1)) z =
      - horizontalMean (fun x ↦ fderiv ℝ
        (verticalVelocitySquare (fun x ↦ velocity x t.1)) x
        (EuclideanSpace.single (2 : Fin 3) 1)) z := by
  exact (horizontalMean_hasDerivAt _
    ((openPeriodicSolutionOn_pressureSlice_contDiff solution t.2).of_le (WithTop.coe_le_coe.mpr le_top)) z).unique
    (pressure_mean_hasDerivAt_neg_vertical_square_mean solution t z)

#print axioms pressure_mean_add_vertical_square_mean_eq
#print axioms pressure_mean_hasDerivAt_neg_vertical_square_mean
#print axioms horizontalMean_pressure_axialDerivative_eq_neg_vertical_square_axialDerivative
end Soma.Holonics.Millennium.NavierStokesPressureMean
