import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Periodic pressure work on the Navier--Stokes carrier

This module closes the pressure face of the periodic kinetic-energy receiver on the actual
three-dimensional `NavierStokes.Space`.  The local product rule identifies pressure work with the
divergence of the flux `p u` when `u` is incompressible.  The existing paired-face theorem then
annihilates its integral over one period.

No integration-by-parts surrogate or coordinate-only divergence is introduced: the pointwise law
uses the repository's trace definition of `divergence`, and the global law uses
`NavierStokesPeriodicFlux.integral_divergence_unitCube_eq_zero_of_onePeriodic`.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- **The pressure-flux product rule on the actual carrier.**  The divergence of `p u` is the
pressure work `u · ∇p` plus pressure times the divergence of `u`. -/
theorem divergence_pressureFlux
    (u : InitialVelocity) (p : Space → ℝ) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hp : DifferentiableAt ℝ p x) :
    divergence (fun y ↦ p y • u y) x =
      inner ℝ (gradient p x) (u x) + p x * divergence u x := by
  unfold divergence
  rw [fderiv_fun_smul hp hu]
  change LinearMap.trace ℝ Space
      (p x • (fderiv ℝ u x).toLinearMap +
        (fderiv ℝ p x).toLinearMap.smulRight (u x)) = _
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.trace_smulRight]
  rw [inner_gradient_left hp]
  simp only [smul_eq_mul]
  rw [add_comm]
  rfl

/-- Scalar multiplication preserves spatial unit periodicity. -/
theorem pressureFlux_isOnePeriodic
    (u : InitialVelocity) (p : Space → ℝ)
    (hu : IsOnePeriodic u) (hp : IsOnePeriodic p) :
    IsOnePeriodic (fun x ↦ p x • u x) := by
  intro x i
  change p (x + EuclideanSpace.single i 1) • u (x + EuclideanSpace.single i 1) =
    p x • u x
  rw [hp x i, hu x i]

/-- **Periodic pressure does no net work on an incompressible velocity field.**

The hypotheses expose every analytic port used by the proof: both fields are globally `C¹`, both
return across opposite unit faces, and the velocity is pointwise divergence-free. -/
theorem integral_pressureWork_unitCube_eq_zero
    (u : InitialVelocity) (p : Space → ℝ)
    (hu : ContDiff ℝ 1 u) (hp : ContDiff ℝ 1 p)
    (huPeriodic : IsOnePeriodic u) (hpPeriodic : IsOnePeriodic p)
    (huIncompressible : ∀ x, divergence u x = 0) :
    ∫ x in unitCube, inner ℝ (gradient p x) (u x) = 0 := by
  have hfluxSmooth : ContDiff ℝ 1 (fun x ↦ p x • u x) := hp.smul hu
  have hfluxPeriodic : IsOnePeriodic (fun x ↦ p x • u x) :=
    pressureFlux_isOnePeriodic u p huPeriodic hpPeriodic
  have hfluxIntegral := integral_divergence_unitCube_eq_zero_of_onePeriodic
    (fun x ↦ p x • u x) hfluxPeriodic hfluxSmooth
  have hunitCubeMeasurable : MeasurableSet unitCube := by
    exact measurableSet_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  calc
    ∫ x in unitCube, inner ℝ (gradient p x) (u x) =
        ∫ x in unitCube, divergence (fun y ↦ p y • u y) x := by
      apply setIntegral_congr_fun hunitCubeMeasurable
      intro x _hx
      rw [divergence_pressureFlux u p x (hu.differentiable (by norm_num) x)
        (hp.differentiable (by norm_num) x), huIncompressible x, mul_zero, add_zero]
    _ = 0 := hfluxIntegral

/-- The pressure term of every admitted periodic smooth solution has zero kinetic-energy reading
at each strictly positive time. -/
theorem periodicSolution_integral_pressureWork_eq_zero
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
      inner ℝ (gradient (fun y ↦ pressure y t) x) (velocity x t) = 0 := by
  apply integral_pressureWork_unitCube_eq_zero
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht).of_le (by norm_num)
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
      solution.pressureSmooth ht).of_le (by norm_num)
  · exact solution.velocityPeriodic t ht.le
  · exact solution.pressurePeriodic t ht.le
  · exact fun x ↦ solution.incompressible x t ht.le

/-! ## The advective face -/

/-- Half the squared speed, the scalar density whose transport flux cancels the advective work. -/
def kineticEnergyDensity (u : InitialVelocity) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * ‖u x‖ ^ 2

/-- The gradient of the kinetic-energy density, read along the velocity, is the pointwise
advective work. -/
theorem inner_gradient_kineticEnergyDensity
    (u : InitialVelocity) (x : Space) (hu : DifferentiableAt ℝ u x) :
    inner ℝ (gradient (kineticEnergyDensity u) x) (u x) =
      inner ℝ (fderiv ℝ u x (u x)) (u x) := by
  have hnorm : DifferentiableAt ℝ (fun y ↦ ‖u y‖ ^ 2) x := hu.norm_sq ℝ
  have henergy : DifferentiableAt ℝ (kineticEnergyDensity u) x := by
    exact hnorm.const_mul (1 / 2 : ℝ)
  rw [inner_gradient_left henergy]
  unfold kineticEnergyDensity
  rw [fderiv_const_mul hnorm (1 / 2 : ℝ)]
  rw [(hu.hasFDerivAt.norm_sq).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  rw [real_inner_comm]
  ring

/-- **The kinetic-energy-flux product rule on the actual carrier.**  Its divergence is the
advective work plus the kinetic-energy density times incompressibility. -/
theorem divergence_kineticEnergyFlux
    (u : InitialVelocity) (x : Space) (hu : DifferentiableAt ℝ u x) :
    divergence (fun y ↦ kineticEnergyDensity u y • u y) x =
      inner ℝ (fderiv ℝ u x (u x)) (u x) +
        kineticEnergyDensity u x * divergence u x := by
  have henergy : DifferentiableAt ℝ (kineticEnergyDensity u) x := by
    exact (hu.norm_sq ℝ).const_mul (1 / 2 : ℝ)
  rw [divergence_pressureFlux u (kineticEnergyDensity u) x hu henergy,
    inner_gradient_kineticEnergyDensity u x hu]

/-- Kinetic-energy density returns across every unit-period face with its velocity. -/
theorem kineticEnergyFlux_isOnePeriodic
    (u : InitialVelocity) (hu : IsOnePeriodic u) :
    IsOnePeriodic (fun x ↦ kineticEnergyDensity u x • u x) := by
  apply pressureFlux_isOnePeriodic u (kineticEnergyDensity u) hu
  intro x i
  unfold kineticEnergyDensity
  rw [hu x i]

/-- **Periodic advection does no net kinetic-energy work.**  This is the exact nonlinear
cancellation on one spatial period; it uses only `C¹`, periodicity, and incompressibility. -/
theorem integral_advectionWork_unitCube_eq_zero
    (u : InitialVelocity) (hu : ContDiff ℝ 1 u)
    (huPeriodic : IsOnePeriodic u)
    (huIncompressible : ∀ x, divergence u x = 0) :
    ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) = 0 := by
  have henergySmooth : ContDiff ℝ 1 (kineticEnergyDensity u) := by
    unfold kineticEnergyDensity
    exact contDiff_const.mul (hu.norm_sq ℝ)
  have hfluxSmooth : ContDiff ℝ 1
      (fun x ↦ kineticEnergyDensity u x • u x) := henergySmooth.smul hu
  have hfluxPeriodic : IsOnePeriodic
      (fun x ↦ kineticEnergyDensity u x • u x) :=
    kineticEnergyFlux_isOnePeriodic u huPeriodic
  have hfluxIntegral := integral_divergence_unitCube_eq_zero_of_onePeriodic
    (fun x ↦ kineticEnergyDensity u x • u x) hfluxPeriodic hfluxSmooth
  have hunitCubeMeasurable : MeasurableSet unitCube := by
    exact measurableSet_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  calc
    ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) =
        ∫ x in unitCube,
          divergence (fun y ↦ kineticEnergyDensity u y • u y) x := by
      apply setIntegral_congr_fun hunitCubeMeasurable
      intro x _hx
      rw [divergence_kineticEnergyFlux u x (hu.differentiable (by norm_num) x),
        huIncompressible x, mul_zero, add_zero]
    _ = 0 := hfluxIntegral

/-- The nonlinear term of every admitted periodic smooth solution has zero kinetic-energy reading
at each strictly positive time. -/
theorem periodicSolution_integral_advectionWork_eq_zero
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ velocity y t) x (velocity x t))
        (velocity x t) = 0 := by
  apply integral_advectionWork_unitCube_eq_zero
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht).of_le (by norm_num)
  · exact solution.velocityPeriodic t ht.le
  · exact fun x ↦ solution.incompressible x t ht.le

/-! ## The viscous face -/

/-- A globally `C²` scalar field has a globally `C¹` gradient on the Euclidean carrier. -/
theorem gradient_contDiff_one (f : Space → ℝ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) := by
  unfold gradient
  exact (toDual ℝ Space).symm.contDiff.comp (hf.fderiv_right (by norm_num))

/-- Differentiation preserves the declared spatial unit periods.  The claim uses the totalized
Fréchet derivative and therefore needs no extra differentiability hypothesis. -/
theorem fderiv_isOnePeriodic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : IsOnePeriodic f) :
    IsOnePeriodic (fderiv ℝ f) := by
  intro x i
  let e : Space := EuclideanSpace.single i 1
  have hfun : (fun y ↦ f (y + e)) = f := by
    funext y
    exact hf y i
  have htranslate := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) e
  rw [hfun] at htranslate
  exact htranslate.symm

/-- Consequently the gradient of a periodic scalar field is periodic. -/
theorem gradient_isOnePeriodic (f : Space → ℝ) (hf : IsOnePeriodic f) :
    IsOnePeriodic (gradient f) := by
  intro x i
  unfold gradient
  exact congrArg (toDual ℝ Space).symm (fderiv_isOnePeriodic f hf x i)

/-- The repository's trace divergence is continuous for every globally `C¹` vector field. -/
theorem divergence_continuous_of_contDiff_one
    (v : InitialVelocity) (hv : ContDiff ℝ 1 v) :
    Continuous (divergence v) := by
  have hsum : Continuous fun x : Space ↦ ∑ i : Fin 3,
      (EuclideanSpace.proj i).comp (fderiv ℝ v x)
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1)) := by
    apply continuous_finset_sum
    intro i _hi
    have happly := hv.continuous_fderiv_apply (by norm_num)
    have hdirection := happly.comp
      (continuous_id.prodMk
        (continuous_const : Continuous fun _ : Space ↦
          (EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1)))
    exact (EuclideanSpace.proj i).continuous.comp hdirection
  exact hsum.congr (fun x ↦ sum_coordinate_fderiv_eq_divergence v x)

/-- On a globally `C²` scalar field, the trace divergence of the metric gradient is Mathlib's
canonical-tensor Laplacian. -/
theorem divergence_gradient_eq_laplacian
    (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x : Space) :
    divergence (gradient f) x = Δ f x := by
  rw [← sum_coordinate_fderiv_eq_divergence (gradient f) x]
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x]
  apply Finset.sum_congr rfl
  intro i _hi
  let e : Space := EuclideanSpace.basisFun (Fin 3) ℝ i
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgradSmooth : ContDiff ℝ 1 (gradient f) := gradient_contDiff_one f hf
  have hgradDiff : Differentiable ℝ (gradient f) :=
    hgradSmooth.differentiable (by norm_num)
  have hcoord : (fun y ↦ gradient f y i) = (fun y ↦ fderiv ℝ f y e) := by
    funext y
    rw [← EuclideanSpace.inner_basisFun_real (Fin 3) (gradient f y : Space) i]
    simpa [e] using (inner_gradient_left (hfDiff y) :
      inner ℝ (gradient f y) e = fderiv ℝ f y e)
  have hleft := ((EuclideanSpace.proj i).hasFDerivAt.comp x
    (hgradDiff x).hasFDerivAt).fderiv
  have hleftApply := congrArg (fun L : Space →L[ℝ] ℝ ↦ L e) hleft
  have hfderivSmooth : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hfderivDiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hfderivSmooth.differentiable (by norm_num) x
  have hconst : DifferentiableAt ℝ (fun _ : Space ↦ e) x := differentiableAt_const e
  have hright := fderiv_clm_apply hfderivDiff hconst
  have hrightApply := congrArg (fun L : Space →L[ℝ] ℝ ↦ L e) hright
  calc
    (EuclideanSpace.proj i).comp (fderiv ℝ (gradient f) x)
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1)) =
        fderiv ℝ (fun y ↦ gradient f y i) x e := by
          simpa [e, equiv_symm_single_eq_basisFun] using hleftApply.symm
    _ = fderiv ℝ (fun y ↦ fderiv ℝ f y e) x e := by rw [hcoord]
    _ = fderiv ℝ (fderiv ℝ f) x e e := by
          simpa using hrightApply
    _ = iteratedFDeriv ℝ 2 f x ![e, e] := by
          rw [iteratedFDeriv_two_apply]
          rfl

/-- **Periodic scalar Green identity.**  The Laplacian pairs with its field as minus the squared
gradient over one unit period. -/
theorem integral_laplacian_mul_eq_neg_integral_norm_gradient_sq
    (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (hfPeriodic : IsOnePeriodic f) :
    ∫ x in unitCube, Δ f x * f x =
      -∫ x in unitCube, ‖gradient f x‖ ^ 2 := by
  have hfOne : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hgradSmooth : ContDiff ℝ 1 (gradient f) := gradient_contDiff_one f hf
  have hgradPeriodic : IsOnePeriodic (gradient f) := gradient_isOnePeriodic f hfPeriodic
  have hfluxSmooth : ContDiff ℝ 1 (fun x ↦ f x • gradient f x) := hfOne.smul hgradSmooth
  have hfluxPeriodic : IsOnePeriodic (fun x ↦ f x • gradient f x) :=
    pressureFlux_isOnePeriodic (gradient f) f hgradPeriodic hfPeriodic
  have hfluxIntegral := integral_divergence_unitCube_eq_zero_of_onePeriodic
    (fun x ↦ f x • gradient f x) hfluxPeriodic hfluxSmooth
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hdivFluxContinuous : Continuous
      (divergence (fun x ↦ f x • gradient f x)) :=
    divergence_continuous_of_contDiff_one _ hfluxSmooth
  have hdivFluxIntegrable : IntegrableOn
      (divergence (fun x ↦ f x • gradient f x)) unitCube :=
    hdivFluxContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hnormIntegrable : IntegrableOn (fun x ↦ ‖gradient f x‖ ^ 2) unitCube :=
    (hgradSmooth.norm_sq ℝ).continuous.continuousOn.integrableOn_compact hcubeCompact
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  calc
    ∫ x in unitCube, Δ f x * f x =
        ∫ x in unitCube,
          divergence (fun y ↦ f y • gradient f y) x - ‖gradient f x‖ ^ 2 := by
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      change Δ f x * f x =
        divergence (fun y ↦ f y • gradient f y) x - ‖gradient f x‖ ^ 2
      rw [divergence_pressureFlux (gradient f) f x
        (hgradSmooth.differentiable (by norm_num) x)
        (hfOne.differentiable (by norm_num) x),
        divergence_gradient_eq_laplacian f hf x, real_inner_self_eq_norm_sq]
      ring
    _ = (∫ x in unitCube, divergence (fun y ↦ f y • gradient f y) x) -
          ∫ x in unitCube, ‖gradient f x‖ ^ 2 := by
      exact integral_sub hdivFluxIntegrable hnormIntegrable
    _ = -∫ x in unitCube, ‖gradient f x‖ ^ 2 := by rw [hfluxIntegral, zero_sub]

/-- **The viscous integration-by-parts identity, componentwise on the actual velocity carrier.**
This is the exact available Frobenius population: one squared spatial gradient for each velocity
component. -/
theorem integral_laplacian_component_mul_eq_neg_integral_norm_gradient_sq
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (huPeriodic : IsOnePeriodic u) (i : Fin 3) :
    ∫ x in unitCube, (Δ u x) i * u x i =
      -∫ x in unitCube, ‖gradient (fun y ↦ u y i) x‖ ^ 2 := by
  have hcomponentSmooth : ContDiff ℝ 2 (fun x ↦ u x i) :=
    by simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  have hcomponentPeriodic : IsOnePeriodic (fun x ↦ u x i) := by
    intro x j
    exact congrArg (fun z : Space ↦ z i) (huPeriodic x j)
  have hscalar := integral_laplacian_mul_eq_neg_integral_norm_gradient_sq
    (fun x ↦ u x i) hcomponentSmooth hcomponentPeriodic
  have hlaplacian : ∀ x : Space, Δ (fun y ↦ u y i) x = (Δ u x) i := by
    intro x
    have h := (hu.contDiffAt (x := x)).laplacian_CLM_comp_left
      (l := EuclideanSpace.proj i)
    simpa [Function.comp_def] using h
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact measurableSet_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  calc
    ∫ x in unitCube, (Δ u x) i * u x i =
        ∫ x in unitCube, Δ (fun y ↦ u y i) x * u x i := by
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      change (Δ u x) i * u x i = Δ (fun y ↦ u y i) x * u x i
      rw [hlaplacian]
    _ = -∫ x in unitCube, ‖gradient (fun y ↦ u y i) x‖ ^ 2 := hscalar

/-- **The complete periodic viscous face.**  The vector Laplacian's kinetic-energy reading is
minus the integral of the componentwise gradient-square population, the Frobenius-square form
available from the current Euclidean carrier. -/
theorem integral_inner_laplacian_eq_neg_integral_component_gradient_sq
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (huPeriodic : IsOnePeriodic u) :
    ∫ x in unitCube, inner ℝ (Δ u x) (u x) =
      -∫ x in unitCube, ∑ i : Fin 3, ‖gradient (fun y ↦ u y i) x‖ ^ 2 := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hcomponentSmooth : ∀ i : Fin 3, ContDiff ℝ 2 (fun x ↦ u x i) := by
    intro i
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  have hcomponentPeriodic : ∀ i : Fin 3, IsOnePeriodic (fun x ↦ u x i) := by
    intro i x j
    exact congrArg (fun z : Space ↦ z i) (huPeriodic x j)
  have hlaplacian : ∀ (i : Fin 3) (x : Space),
      Δ (fun y ↦ u y i) x = (Δ u x) i := by
    intro i x
    have h := (hu.contDiffAt (x := x)).laplacian_CLM_comp_left
      (l := EuclideanSpace.proj i)
    simpa [Function.comp_def] using h
  have hworkIntegrable : ∀ i : Fin 3,
      IntegrableOn (fun x ↦ (Δ u x) i * u x i) unitCube := by
    intro i
    have hgradSmooth := gradient_contDiff_one (fun x ↦ u x i) (hcomponentSmooth i)
    have hdivGradContinuous := divergence_continuous_of_contDiff_one
      (gradient (fun x ↦ u x i)) hgradSmooth
    have hlapContinuous : Continuous (fun x ↦ Δ (fun y ↦ u y i) x) :=
      hdivGradContinuous.congr (fun x ↦
        divergence_gradient_eq_laplacian (fun y ↦ u y i) (hcomponentSmooth i) x)
    have hlapComponentContinuous : Continuous (fun x ↦ (Δ u x) i) :=
      hlapContinuous.congr (fun x ↦ (hlaplacian i x))
    exact (hlapComponentContinuous.mul (hcomponentSmooth i).continuous).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hgradientIntegrable : ∀ i : Fin 3,
      IntegrableOn (fun x ↦ ‖gradient (fun y ↦ u y i) x‖ ^ 2) unitCube := by
    intro i
    exact ((gradient_contDiff_one (fun x ↦ u x i) (hcomponentSmooth i)).norm_sq ℝ).continuous
      |>.continuousOn.integrableOn_compact hcubeCompact
  calc
    ∫ x in unitCube, inner ℝ (Δ u x) (u x) =
        ∫ x in unitCube, ∑ i : Fin 3, (Δ u x) i * u x i := by
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      simp [PiLp.inner_apply, mul_comm]
    _ = ∑ i : Fin 3, ∫ x in unitCube, (Δ u x) i * u x i := by
      exact integral_finset_sum Finset.univ (fun i _hi ↦ hworkIntegrable i)
    _ = ∑ i : Fin 3, -∫ x in unitCube,
          ‖gradient (fun y ↦ u y i) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact integral_laplacian_component_mul_eq_neg_integral_norm_gradient_sq
        u hu huPeriodic i
    _ = -(∑ i : Fin 3, ∫ x in unitCube,
          ‖gradient (fun y ↦ u y i) x‖ ^ 2) := by
      rw [Finset.sum_neg_distrib]
    _ = -∫ x in unitCube, ∑ i : Fin 3,
          ‖gradient (fun y ↦ u y i) x‖ ^ 2 := by
      rw [integral_finset_sum Finset.univ (fun i _hi ↦ hgradientIntegrable i)]

/-- Every admitted periodic smooth solution supplies the componentwise viscous Green identity at
strictly positive time. -/
theorem periodicSolution_integral_laplacian_component_mul_eq_neg_gradient_sq
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (i : Fin 3) :
    ∫ x in unitCube, (Δ (fun y ↦ velocity y t) x) i * velocity x t i =
      -∫ x in unitCube,
        ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2 := by
  apply integral_laplacian_component_mul_eq_neg_integral_norm_gradient_sq
  · rw [contDiff_iff_contDiffAt]
    intro x
    have hslice : ContDiffAt ℝ ∞ (fun y ↦ velocity y t) x :=
      spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
        solution.velocitySmooth ht
    exact hslice.of_le (WithTop.coe_le_coe.mpr le_top)
  · exact solution.velocityPeriodic t ht.le

/-- The complete viscous face attached to every admitted periodic smooth solution at positive
time. -/
theorem periodicSolution_integral_inner_laplacian_eq_neg_component_gradient_sq
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y ↦ velocity y t) x) (velocity x t) =
      -∫ x in unitCube, ∑ i : Fin 3,
        ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2 := by
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · rw [contDiff_iff_contDiffAt]
    intro x
    have hslice : ContDiffAt ℝ ∞ (fun y ↦ velocity y t) x :=
      spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
        solution.velocitySmooth ht
    exact hslice.of_le (WithTop.coe_le_coe.mpr le_top)
  · exact solution.velocityPeriodic t ht.le

section Audit

#print axioms divergence_pressureFlux
#print axioms pressureFlux_isOnePeriodic
#print axioms integral_pressureWork_unitCube_eq_zero
#print axioms periodicSolution_integral_pressureWork_eq_zero
#print axioms inner_gradient_kineticEnergyDensity
#print axioms divergence_kineticEnergyFlux
#print axioms kineticEnergyFlux_isOnePeriodic
#print axioms integral_advectionWork_unitCube_eq_zero
#print axioms periodicSolution_integral_advectionWork_eq_zero
#print axioms gradient_contDiff_one
#print axioms fderiv_isOnePeriodic
#print axioms gradient_isOnePeriodic
#print axioms divergence_continuous_of_contDiff_one
#print axioms divergence_gradient_eq_laplacian
#print axioms integral_laplacian_mul_eq_neg_integral_norm_gradient_sq
#print axioms integral_laplacian_component_mul_eq_neg_integral_norm_gradient_sq
#print axioms integral_inner_laplacian_eq_neg_integral_component_gradient_sq
#print axioms periodicSolution_integral_laplacian_component_mul_eq_neg_gradient_sq
#print axioms periodicSolution_integral_inner_laplacian_eq_neg_component_gradient_sq

end Audit

end Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
