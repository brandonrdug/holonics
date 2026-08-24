import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Periodic kinetic-energy equality on the Navier--Stokes carrier

This module closes the positive-time periodic kinetic-energy receiver on the actual
three-dimensional `NavierStokes.Space`.  Local product rules identify pressure and advective work
with divergences, the paired-face theorem annihilates their integrals over one period, and scalar
Green identities assemble the vector viscous work.  It is dissipative when `0 ≤ ν`; the exact
equality itself is valid for every real coefficient admitted by `PeriodicSolution`.  The joint
space--time derivative then supplies the Eulerian time jet.  Smoothness on a compact positive-time
cylinder provides the
domination needed to differentiate the unit-cube integral, returning the full forced equality

`d/dt (1/2 ∫ |u|²) = -ν ∫ ∑ᵢ |∇uᵢ|² + ∫ f·u`

for every strictly positive time admitted by `PeriodicSolution`.

No integration-by-parts surrogate or coordinate-only divergence is introduced: the pointwise law
uses the repository's trace definition of `divergence`, and the global law uses
`NavierStokesPeriodicFlux.integral_divergence_unitCube_eq_zero_of_onePeriodic`.  The boundary time
`t = 0`, enstrophy evolution, and any global regularity estimate remain separate open faces.
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

/-! ## The positive-time kinetic-energy balance -/

/-- The Eulerian time jet read from the derivative of the joint space--time velocity field.

Using the joint derivative makes continuity in both variables available before any integration.
At a positive-time solution occurrence it agrees with the `derivWithin` appearing in the official
momentum equation; that attachment is proved immediately below. -/
def eulerianTimeJet (velocity : VelocityField) (x : Space) (t : ℝ) : Space :=
  fderiv ℝ (Function.uncurry velocity) (x, t) (0, 1)

/-- At positive time the joint Eulerian jet is exactly the within-time derivative used by the
official Navier--Stokes momentum equation. -/
theorem periodicSolution_eulerianTimeJet_eq_derivWithin
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    eulerianTimeJet velocity x t = derivWithin (velocity x) (Ici 0) t := by
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (solution.velocitySmooth.contDiffAt hdomain).differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have htimeApply := congrArg (fun L : ℝ →L[ℝ] Space ↦ L 1) htime.fderiv
  have hhalf : Set.Ici (0 : ℝ) ∈ nhds t :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) Set.Ioi_subset_Ici_self
  rw [derivWithin_of_mem_nhds hhalf]
  simpa [eulerianTimeJet, Function.comp_def, fderiv_apply_one_eq_deriv] using htimeApply.symm

/-- Pointwise differentiation of half the squared speed in the positive-time direction. -/
theorem periodicSolution_hasDerivAt_kineticEnergyDensity_time
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun τ ↦ kineticEnergyDensity (fun y ↦ velocity y τ) x)
      (inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) t := by
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (solution.velocitySmooth.contDiffAt hdomain).differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have hvelocity : HasDerivAt (velocity x) (eulerianTimeJet velocity x t) t := by
    simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt
  have hnorm := hvelocity.norm_sq.const_mul (1 / 2 : ℝ)
  simpa [kineticEnergyDensity, real_inner_comm] using hnorm

/-- The pointwise momentum equation read against the velocity itself. -/
theorem periodicSolution_pointwise_momentumWork
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    inner ℝ (eulerianTimeJet velocity x t) (velocity x t) +
        inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t) x (velocity x t))
          (velocity x t) =
      ν * inner ℝ (Δ (fun y ↦ velocity y t) x) (velocity x t) -
        inner ℝ (gradient (fun y ↦ pressure y t) x) (velocity x t) +
        inner ℝ (force x t) (velocity x t) := by
  have hmomentum := solution.momentum x t ht.le
  rw [periodicSolution_eulerianTimeJet_eq_derivWithin solution x t ht]
  have hread := congrArg (fun v : Space ↦ inner ℝ v (velocity x t)) hmomentum
  simpa [inner_add_left, inner_sub_left, real_inner_smul_left] using hread

/-- The Eulerian time jet of an admitted solution varies continuously across every positive-time
spatial slice. -/
theorem periodicSolution_eulerianTimeJet_continuous
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    Continuous (fun x ↦ eulerianTimeJet velocity x t) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  have hjoint : ContDiffAt ℝ ∞ (Function.uncurry velocity) (x, t) :=
    solution.velocitySmooth.contDiffAt hdomain
  have hjetAt : ContinuousAt
      (fun z ↦ fderiv ℝ (Function.uncurry velocity) z (0, 1)) (x, t) :=
    (hjoint.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hpair : ContinuousAt (fun y : Space ↦ (y, t)) x :=
    continuousAt_id.prodMk continuousAt_const
  simpa [eulerianTimeJet, Function.comp_def] using hjetAt.comp_of_eq hpair rfl

/-- The vector-Laplacian work is integrable on the compact unit cube for every globally `C²`
velocity slice. -/
theorem integrableOn_inner_laplacian_unitCube
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) :
    IntegrableOn (fun x ↦ inner ℝ (Δ u x) (u x)) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hcomponentSmooth : ∀ i : Fin 3, ContDiff ℝ 2 (fun x ↦ u x i) := by
    intro i
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  have hlaplacian : ∀ (i : Fin 3) (x : Space),
      Δ (fun y ↦ u y i) x = (Δ u x) i := by
    intro i x
    have h := (hu.contDiffAt (x := x)).laplacian_CLM_comp_left
      (l := EuclideanSpace.proj i)
    simpa [Function.comp_def] using h
  have hcomponentWork : ∀ i : Fin 3,
      IntegrableOn (fun x ↦ (Δ u x) i * u x i) unitCube := by
    intro i
    have hgradSmooth := gradient_contDiff_one (fun x ↦ u x i) (hcomponentSmooth i)
    have hdivGradContinuous := divergence_continuous_of_contDiff_one
      (gradient (fun x ↦ u x i)) hgradSmooth
    have hlapContinuous : Continuous (fun x ↦ Δ (fun y ↦ u y i) x) :=
      hdivGradContinuous.congr (fun x ↦
        divergence_gradient_eq_laplacian (fun y ↦ u y i) (hcomponentSmooth i) x)
    have hlapComponentContinuous : Continuous (fun x ↦ (Δ u x) i) :=
      hlapContinuous.congr (fun x ↦ hlaplacian i x)
    exact (hlapComponentContinuous.mul (hcomponentSmooth i).continuous).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hsum : IntegrableOn (fun x ↦ ∑ i : Fin 3, (Δ u x) i * u x i) unitCube :=
    integrable_finset_sum Finset.univ (fun i _hi ↦ hcomponentWork i)
  exact hsum.congr_fun (fun x _hx ↦ by simp [PiLp.inner_apply, mul_comm]) hcubeMeasurable

/-- **The integrated positive-time momentum receiver.**  After the exact periodic pressure and
advection cancellations and the viscous Green identity are composed, the Eulerian time work is
forcing work minus `ν` times the full component-gradient population.  The latter is dissipative
under the separate physical sign condition `0 ≤ ν`; this equality does not need that condition.
This theorem does not yet interchange time differentiation with spatial integration. -/
theorem periodicSolution_integral_eulerianTimeWork_eq_forcing_sub_dissipation
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
        inner ℝ (eulerianTimeJet velocity x t) (velocity x t) =
      -ν * (∫ x in unitCube, ∑ i : Fin 3,
        ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2) +
        ∫ x in unitCube, inner ℝ (force x t) (velocity x t) := by
  let u : InitialVelocity := fun x ↦ velocity x t
  let p : Space → ℝ := fun x ↦ pressure x t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hu : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
      solution.pressureSmooth ht
  have htimeContinuous : Continuous
      (fun x ↦ inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) :=
    (periodicSolution_eulerianTimeJet_continuous solution t ht).inner hu.continuous
  have hadvectionContinuous : Continuous (fun x ↦
      inner ℝ (fderiv ℝ u x (u x)) (u x)) := by
    have hfield : Continuous (fun x ↦ fderiv ℝ u x (u x)) :=
      (hu.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hu.continuous)
    exact hfield.inner hu.continuous
  have hpressureContinuous : Continuous (fun x ↦
      inner ℝ (gradient p x) (u x)) :=
    (gradient_contDiff_one p (hp.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hu.continuous
  have htimeInt : IntegrableOn
      (fun x ↦ inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) unitCube :=
    htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hadvectionInt : IntegrableOn
      (fun x ↦ inner ℝ (fderiv ℝ u x (u x)) (u x)) unitCube :=
    hadvectionContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x ↦ inner ℝ (Δ u x) (u x)) unitCube :=
    integrableOn_inner_laplacian_unitCube u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpressureInt : IntegrableOn
      (fun x ↦ inner ℝ (gradient p x) (u x)) unitCube :=
    hpressureContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hforceInt : IntegrableOn
      (fun x ↦ inner ℝ (force x t) (u x)) unitCube := by
    have hrest : IntegrableOn (fun x ↦
        (inner ℝ (eulerianTimeJet velocity x t) (u x) +
          inner ℝ (fderiv ℝ u x (u x)) (u x) -
            ν * inner ℝ (Δ u x) (u x)) + inner ℝ (gradient p x) (u x)) unitCube :=
      ((htimeInt.add hadvectionInt).sub (hviscousInt.const_mul ν)).add hpressureInt
    apply hrest.congr_fun _ hcubeMeasurable
    intro x _hx
    have hpoint := periodicSolution_pointwise_momentumWork solution x t ht
    change (inner ℝ (eulerianTimeJet velocity x t) (u x) +
        inner ℝ (fderiv ℝ u x (u x)) (u x) -
          ν * inner ℝ (Δ u x) (u x)) + inner ℝ (gradient p x) (u x) =
      inner ℝ (force x t) (u x)
    change inner ℝ (eulerianTimeJet velocity x t) (u x) +
        inner ℝ (fderiv ℝ u x (u x)) (u x) =
      ν * inner ℝ (Δ u x) (u x) - inner ℝ (gradient p x) (u x) +
        inner ℝ (force x t) (u x) at hpoint
    linarith
  have hintegrated :
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet velocity x t) (u x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) =
        ν * (∫ x in unitCube, inner ℝ (Δ u x) (u x)) -
          (∫ x in unitCube, inner ℝ (gradient p x) (u x)) +
          ∫ x in unitCube, inner ℝ (force x t) (u x) := by
    calc
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet velocity x t) (u x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) =
        ∫ x in unitCube,
          (inner ℝ (eulerianTimeJet velocity x t) (u x) +
            inner ℝ (fderiv ℝ u x (u x)) (u x)) :=
          (integral_add htimeInt hadvectionInt).symm
      _ = ∫ x in unitCube,
          ((ν * inner ℝ (Δ u x) (u x) - inner ℝ (gradient p x) (u x)) +
            inner ℝ (force x t) (u x)) := by
        apply setIntegral_congr_fun hcubeMeasurable
        intro x _hx
        exact periodicSolution_pointwise_momentumWork solution x t ht
      _ = (∫ x in unitCube,
            (ν * inner ℝ (Δ u x) (u x) - inner ℝ (gradient p x) (u x))) +
            ∫ x in unitCube, inner ℝ (force x t) (u x) :=
        integral_add ((hviscousInt.const_mul ν).sub hpressureInt) hforceInt
      _ = ((∫ x in unitCube, ν * inner ℝ (Δ u x) (u x)) -
            ∫ x in unitCube, inner ℝ (gradient p x) (u x)) +
            ∫ x in unitCube, inner ℝ (force x t) (u x) := by
        rw [integral_sub (hviscousInt.const_mul ν) hpressureInt]
      _ = ν * (∫ x in unitCube, inner ℝ (Δ u x) (u x)) -
            (∫ x in unitCube, inner ℝ (gradient p x) (u x)) +
            ∫ x in unitCube, inner ℝ (force x t) (u x) := by
        rw [integral_const_mul]
  have hadvectionZero := periodicSolution_integral_advectionWork_eq_zero solution t ht
  have hpressureZero := periodicSolution_integral_pressureWork_eq_zero solution t ht
  have hviscous :=
    periodicSolution_integral_inner_laplacian_eq_neg_component_gradient_sq solution t ht
  change (∫ x in unitCube,
      inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) = _
  change (∫ x in unitCube,
      inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) +
        (∫ x in unitCube,
          inner ℝ (fderiv ℝ (fun y ↦ velocity y t) x (velocity x t)) (velocity x t)) =
      ν * (∫ x in unitCube, inner ℝ (Δ (fun y ↦ velocity y t) x) (velocity x t)) -
        (∫ x in unitCube,
          inner ℝ (gradient (fun y ↦ pressure y t) x) (velocity x t)) +
        ∫ x in unitCube, inner ℝ (force x t) (velocity x t) at hintegrated
  rw [hadvectionZero, hpressureZero, hviscous] at hintegrated
  linarith

/-- Under declared integrability and the physical sign condition `0 ≤ ν`, the viscous
contribution in the energy equality is nonpositive.  This is the exact point at which the algebraic
work term earns the name "dissipation". -/
theorem viscousEnergyContribution_nonpositive
    {velocity : VelocityField} {t ν : ℝ} (hν : 0 ≤ ν)
    (hintegrable : IntegrableOn (fun x ↦ ∑ i : Fin 3,
      ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2) unitCube) :
    -ν * (∫ x in unitCube, ∑ i : Fin 3,
      ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2) ≤ 0 := by
  have _hfiniteReceiver := hintegrable
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  have hpopulation : 0 ≤ ∫ x in unitCube, ∑ i : Fin 3,
      ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2 :=
    setIntegral_nonneg hcubeMeasurable (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν) hpopulation

/-- Half the squared-speed population integrated over one spatial period. -/
def periodicKineticEnergy (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, kineticEnergyDensity (fun y ↦ velocity y t) x

/-- **Differentiation of the periodic kinetic-energy population.**

The domination needed to interchange the positive-time derivative with the spatial integral is
not assumed.  It is obtained from joint smoothness on a compact product of the unit cube with a
closed time interval strictly inside `(0, ∞)`. -/
theorem periodicSolution_hasDerivAt_periodicKineticEnergy_eq_timeWork
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (periodicKineticEnergy velocity)
      (∫ x in unitCube,
        inner ℝ (eulerianTimeJet velocity x t) (velocity x t)) t := by
  let timeSet : Set ℝ := Ioo (t / 2) (3 * t / 2)
  let timeCompact : Set ℝ := Icc (t / 2) (3 * t / 2)
  let positiveCylinder : Set (Space × ℝ) := Set.univ ×ˢ Ioi (0 : ℝ)
  let compactCylinder : Set (Space × ℝ) := unitCube ×ˢ timeCompact
  have htimeSet : timeSet ∈ nhds t := by
    apply Ioo_mem_nhds <;> dsimp [timeSet] <;> linarith
  have hpositiveOpen : IsOpen positiveCylinder := by
    exact isOpen_univ.prod isOpen_Ioi
  have hpositiveSmooth : ContDiffOn ℝ ∞ (Function.uncurry velocity) positiveCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, τ⟩ ⟨_hx, hτ⟩
    exact ⟨Set.mem_univ x, show 0 ≤ τ from hτ.le⟩
  have hjointJetContinuous : ContinuousOn
      (fun z : Space × ℝ ↦
        fderiv ℝ (Function.uncurry velocity) z (0, 1)) positiveCylinder := by
    have hfd : ContinuousOn (fderiv ℝ (Function.uncurry velocity)) positiveCylinder :=
      hpositiveSmooth.continuousOn_fderiv_of_isOpen hpositiveOpen
        (WithTop.coe_le_coe.mpr le_top)
    exact hfd.clm_apply continuousOn_const
  have hjointWorkContinuous : ContinuousOn
      (fun z : Space × ℝ ↦
        inner ℝ (eulerianTimeJet velocity z.1 z.2) (velocity z.1 z.2))
      positiveCylinder := by
    exact hjointJetContinuous.inner hpositiveSmooth.continuousOn
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hcompactCylinder : IsCompact compactCylinder := hcubeCompact.prod isCompact_Icc
  have hcompactSubset : compactCylinder ⊆ positiveCylinder := by
    rintro ⟨x, τ⟩ ⟨hx, hτ⟩
    exact ⟨Set.mem_univ x, lt_of_lt_of_le (half_pos ht) hτ.1⟩
  have hworkNormContinuous : ContinuousOn
      (fun z : Space × ℝ ↦
        ‖inner ℝ (eulerianTimeJet velocity z.1 z.2) (velocity z.1 z.2)‖)
      compactCylinder :=
    (hjointWorkContinuous.mono hcompactSubset).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompactCylinder.bddAbove_image hworkNormContinuous)
  have hFmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (fun x ↦ kineticEnergyDensity (fun y ↦ velocity y τ) x)
      (volume.restrict unitCube) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    have huτ : ContDiff ℝ ∞ (fun x ↦ velocity x τ) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x τ
        solution.velocitySmooth hτ
    exact (contDiff_const.mul (huτ.norm_sq ℝ)).continuous.aestronglyMeasurable
  have hFint : Integrable
      (fun x ↦ kineticEnergyDensity (fun y ↦ velocity y t) x)
      (volume.restrict unitCube) := by
    have hut : ContDiff ℝ ∞ (fun x ↦ velocity x t) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
        solution.velocitySmooth ht
    exact (contDiff_const.mul (hut.norm_sq ℝ)).continuous.continuousOn
      |>.integrableOn_compact hcubeCompact
  have hF'meas : AEStronglyMeasurable
      (fun x ↦ inner ℝ (eulerianTimeJet velocity x t) (velocity x t))
      (volume.restrict unitCube) :=
    ((periodicSolution_eulerianTimeJet_continuous solution t ht).inner
      ((by
        rw [contDiff_iff_contDiffAt]
        intro x
        exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
          solution.velocitySmooth ht) : ContDiff ℝ ∞ (fun x ↦ velocity x t)).continuous)
      |>.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      ‖inner ℝ (eulerianTimeJet velocity x τ) (velocity x τ)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hcubeMeasurable] with x hx
    intro τ hτ
    apply hC
    refine ⟨(x, τ), ?_, rfl⟩
    exact ⟨hx, hτ.1.le, hτ.2.le⟩
  have hboundIntegrable : Integrable (fun _ : Space ↦ C) (volume.restrict unitCube) :=
    integrableOn_const hcubeCompact.measure_lt_top.ne
  have hdiff : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      HasDerivAt
        (fun σ ↦ kineticEnergyDensity (fun y ↦ velocity y σ) x)
        (inner ℝ (eulerianTimeJet velocity x τ) (velocity x τ)) τ := by
    filter_upwards with x
    intro τ hτ
    apply periodicSolution_hasDerivAt_kineticEnergyDensity_time solution x τ
    exact lt_trans (half_pos ht) hτ.1
  simpa [periodicKineticEnergy] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun τ x ↦ kineticEnergyDensity (fun y ↦ velocity y τ) x)
      (F' := fun τ x ↦ inner ℝ (eulerianTimeJet velocity x τ) (velocity x τ))
      (bound := fun _ : Space ↦ C) (x₀ := t) (s := timeSet)
      (μ := volume.restrict unitCube)
      htimeSet hFmeas hFint hF'meas hbound hboundIntegrable hdiff).2

/-- **The complete forced periodic kinetic-energy equality at positive time.** -/
theorem periodicSolution_hasDerivAt_periodicKineticEnergy
    {ν : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution ν initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (periodicKineticEnergy velocity)
      (-ν * (∫ x in unitCube, ∑ i : Fin 3,
        ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2) +
        ∫ x in unitCube, inner ℝ (force x t) (velocity x t)) t := by
  have hderivative :=
    periodicSolution_hasDerivAt_periodicKineticEnergy_eq_timeWork solution t ht
  rw [periodicSolution_integral_eulerianTimeWork_eq_forcing_sub_dissipation
    solution t ht] at hderivative
  exact hderivative

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
#print axioms periodicSolution_eulerianTimeJet_eq_derivWithin
#print axioms periodicSolution_hasDerivAt_kineticEnergyDensity_time
#print axioms periodicSolution_pointwise_momentumWork
#print axioms periodicSolution_eulerianTimeJet_continuous
#print axioms integrableOn_inner_laplacian_unitCube
#print axioms periodicSolution_integral_eulerianTimeWork_eq_forcing_sub_dissipation
#print axioms periodicSolution_hasDerivAt_periodicKineticEnergy_eq_timeWork
#print axioms periodicSolution_hasDerivAt_periodicKineticEnergy

end Audit

end Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
