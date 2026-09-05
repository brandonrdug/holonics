import ElementaryHolonics.Millennium.NavierStokesCoordinateH1Production

/-!
# The axial strain current retains its actual pressure source

The first spatial derivative of the actual unforced momentum equation determines the strain
current. At a stagnation point whose axial direction is a velocity-gradient eigenvector, the
quadratic term is the square of that eigenvalue. The pressure curvature remains the actual
global pressure receiver. Mixed time-space commutation pays the ordinary interior time derivative.
-/

noncomputable section
open ContDiff Set Filter InnerProductSpace
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAxialStrainSource
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesVorticity

def velocityGradientEntry (velocity : VelocityField) (x : Space)
    (component coordinate : Fin 3) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y ↦ velocity y t) x (spatialBasisVector coordinate) component

def axialStrain (velocity : VelocityField) (x : Space) : ℝ → ℝ :=
  velocityGradientEntry velocity x 2 2

def axialPressureCurvature (p : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ (gradient p) x (spatialBasisVector 2) 2

def axialViscousStrain (u : InitialVelocity) (x : Space) : ℝ :=
  fderiv ℝ (Δ u) x (spatialBasisVector 2) 2

theorem velocityGradientEntry_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (component coordinate : Fin 3) :
    HasDerivAt (velocityGradientEntry velocity x component coordinate)
      (fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector coordinate) component) t := by
  let F := firstCoordinateJet velocity coordinate
  have hsmooth : ContDiffAt ℝ ∞ (Function.uncurry F) (x, t) :=
    (openPeriodicSolutionOn_coordinateJetField_contDiffOn solution 1 (firstCoordinateWord coordinate)).contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2))
  have htime := (hsmooth.differentiableAt (by simp)).hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have hvector : HasDerivAt (fun τ ↦ F x τ) (eulerianTimeJet F x t) t := by
    simpa [Function.comp_def, eulerianTimeJet] using htime.hasDerivAt
  have hcomponent := (EuclideanSpace.proj component).hasFDerivAt.comp_hasDerivAt t hvector
  have heq : velocityGradientEntry velocity x component coordinate =ᶠ[𝓝 t] (fun τ ↦ F x τ component) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact (congrArg (fun v : Space ↦ v component)
      (openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet solution hτ x coordinate)).symm
  have hreturn := hcomponent.congr_of_eventuallyEq heq
  dsimp only [F] at hreturn
  rw [openPeriodicSolutionOn_eulerianTimeJet_firstCoordinateJet_eq solution ht x coordinate] at hreturn
  exact hreturn

theorem axialStrain_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (axialStrain velocity x)
      (fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector 2) 2) t :=
  velocityGradientEntry_hasDerivAt solution ht x 2 2

/-- Every actual first-gradient entry retains the pressure Hessian at a stagnation point. -/
theorem velocityGradientEntry_hasDerivAt_at_stagnation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (component coordinate : Fin 3)
    (hzero : velocity x t = 0) :
    HasDerivAt (velocityGradientEntry velocity x component coordinate)
      (nu * fderiv ℝ (Δ (fun y ↦ velocity y t)) x (spatialBasisVector coordinate) component -
        fderiv ℝ (gradient (fun y ↦ pressure y t)) x (spatialBasisVector coordinate) component -
        (velocityJacobianAt (fun y ↦ velocity y t) x *
          velocityJacobianAt (fun y ↦ velocity y t) x) component coordinate) t := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ 2 u := (openPeriodicSolutionOn_velocitySlice_contDiff solution ht).of_le
    (WithTop.coe_le_coe.mpr le_top)
  have hadv := congrArg (fun J : Matrix3 ↦ J component coordinate)
    (velocityJacobianAt_advection_eq_advectionJacobianFromJets u x hu.contDiffAt)
  have hu0 : u x = 0 := hzero
  have hadv' : fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x
      (spatialBasisVector coordinate) component =
      (velocityJacobianAt u x * velocityJacobianAt u x) component coordinate := by
    simpa [advectionJacobianFromJets, hu0, Matrix.mul_apply, velocityJacobianAt,
      jacobianMatrix_apply, spatialBasisVector, mul_comm] using hadv
  have h := congrArg (fun v : Space ↦ v component)
    (openPeriodicSolutionOn_unforced_firstSpatialDerivative_momentum solution ht x coordinate)
  change fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector coordinate) component +
      fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x (spatialBasisVector coordinate) component =
    nu * fderiv ℝ (Δ u) x (spatialBasisVector coordinate) component -
      fderiv ℝ (gradient (fun y ↦ pressure y t)) x (spatialBasisVector coordinate) component at h
  rw [hadv'] at h
  have htime := velocityGradientEntry_hasDerivAt solution ht x component coordinate
  convert htime using 1
  linarith

/-- The nonlinear derivative at the selected stagnation point uses the complete actual first
jet; the eigenvector condition is explicit and does not presume a global axisymmetric field. -/
theorem axial_advection_derivative_at_stagnation
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (x : Space) (a : ℝ)
    (hzero : u x = 0)
    (haxis : fderiv ℝ u x (spatialBasisVector 2) = a • spatialBasisVector 2) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x (spatialBasisVector 2) 2 = a ^ 2 := by
  rw [fderiv_advection_eq_transport_add_stretching u hu x 2, hzero]
  simp only [map_zero, zero_add, spatialDirectionalJet, haxis, map_smul]
  simp [spatialBasisVector, pow_two]

theorem axialStrain_hasDerivAt_at_stagnation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (a : ℝ)
    (hzero : velocity x t = 0)
    (haxis : fderiv ℝ (fun y ↦ velocity y t) x (spatialBasisVector 2) =
      a • spatialBasisVector 2) :
    HasDerivAt (axialStrain velocity x)
      (nu * axialViscousStrain (fun y ↦ velocity y t) x -
        axialPressureCurvature (fun y ↦ pressure y t) x - a ^ 2) t := by
  have h := congrArg (fun v : Space ↦ v 2)
    (openPeriodicSolutionOn_unforced_firstSpatialDerivative_momentum solution ht x 2)
  have hadv := axial_advection_derivative_at_stagnation (fun y ↦ velocity y t)
    ((openPeriodicSolutionOn_velocitySlice_contDiff solution ht).of_le
      (WithTop.coe_le_coe.mpr le_top)) x a hzero haxis
  change fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector 2) 2 +
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ velocity z t) y (velocity y t)) x
        (spatialBasisVector 2) 2 =
    nu * axialViscousStrain (fun y ↦ velocity y t) x -
      axialPressureCurvature (fun y ↦ pressure y t) x at h
  rw [hadv] at h
  have heq : fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector 2) 2 =
      nu * axialViscousStrain (fun y ↦ velocity y t) x -
        axialPressureCurvature (fun y ↦ pressure y t) x - a ^ 2 := by linarith
  rw [← heq]
  exact axialStrain_hasDerivAt solution ht x

/-- The pressure requirement for any proposed strain rate is necessary and sufficient at this
actual interior source occurrence. It is not a freely prescribed pressure port. -/
theorem axialStrain_rate_iff_pressure_curvature
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (a target : ℝ)
    (hzero : velocity x t = 0)
    (haxis : fderiv ℝ (fun y ↦ velocity y t) x (spatialBasisVector 2) =
      a • spatialBasisVector 2) :
    deriv (axialStrain velocity x) t = target ↔
      axialPressureCurvature (fun y ↦ pressure y t) x =
        nu * axialViscousStrain (fun y ↦ velocity y t) x - a ^ 2 - target := by
  rw [(axialStrain_hasDerivAt_at_stagnation solution ht x a hzero haxis).deriv]
  constructor <;> intro h <;> linarith

#print axioms velocityGradientEntry_hasDerivAt
#print axioms velocityGradientEntry_hasDerivAt_at_stagnation
#print axioms axialStrain_hasDerivAt
#print axioms axialStrain_hasDerivAt_at_stagnation
#print axioms axialStrain_rate_iff_pressure_curvature
end Soma.Holonics.Millennium.NavierStokesAxialStrainSource
