import ElementaryHolonics.Millennium.NavierStokesViscousSwirlBalance
import ElementaryHolonics.Millennium.NavierStokesRescalingPeriodObstruction
import ElementaryHolonics.Millennium.NavierStokesRescalingClock
import Mathlib.Analysis.Calculus.DSlope

/-!
# The viscous inner chart carries physical angular momentum

The squared radius and rescaled viscosity have the same leading contraction rate. The regular
chart s=mu*xi transforms the full angular-momentum equation, retaining radial diffusion at unit
strength. Its physical radial scale squared is nu*length*normalizer, and its angular-momentum
carrier reconstructs with the constant factor nu. The mu=0 inverse is not asserted.
-/

noncomputable section

open ContDiff Set InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesViscousInnerChart

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesMovingSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesSwirlDiffusion
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
open Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction
open Soma.Holonics.Millennium.NavierStokesRescalingClock

def radialScale (mu : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (mu * p.1, p.2)

def radialScaleCLM (mu : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (mu • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem radialScaleCLM_apply (mu : ℝ) (p : ℝ × ℝ) :
    radialScaleCLM mu p = (mu * p.1, p.2) := by simp [radialScaleCLM]

theorem radialScale_hasFDerivAt (mu : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (radialScale mu) (radialScaleCLM mu) p :=
  (radialScaleCLM mu).hasFDerivAt

theorem radialScale_inverse (mu : ℝ) (hmu : mu ≠ 0) (p : ℝ × ℝ) :
    radialScale mu (radialScale mu⁻¹ p) = p := by
  ext <;> simp [radialScale, hmu]

def radialPullback (mu : ℝ) (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ := f (radialScale mu p)

theorem radialPullback_contDiff (mu : ℝ) (f : MeridionalProfile) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (radialPullback mu f) := hf.comp (radialScaleCLM mu).contDiff

theorem radialPullback_hasFDerivAt (mu : ℝ) (f : MeridionalProfile) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (radialScale mu p)) :
    HasFDerivAt (radialPullback mu f)
      ((fderiv ℝ f (radialScale mu p)).comp (radialScaleCLM mu)) p :=
  hf.hasFDerivAt.comp p (radialScale_hasFDerivAt mu p)

theorem radialDerivative_pullback (mu : ℝ) (f : MeridionalProfile) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (radialScale mu p)) :
    radialDerivative (radialPullback mu f) p = mu * radialDerivative f (radialScale mu p) := by
  rw [radialDerivative, (radialPullback_hasFDerivAt mu f p hf).fderiv]
  simp only [ContinuousLinearMap.comp_apply, radialScaleCLM_apply, mul_one]
  change fderiv ℝ f (radialScale mu p) (mu, 0) = _
  rw [profile_fderiv_apply]
  ring

theorem axialDerivative_pullback (mu : ℝ) (f : MeridionalProfile) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (radialScale mu p)) :
    axialDerivative (radialPullback mu f) p = axialDerivative f (radialScale mu p) := by
  rw [axialDerivative, (radialPullback_hasFDerivAt mu f p hf).fderiv]
  simp [ContinuousLinearMap.comp_apply, axialDerivative]

theorem radialSecondDerivative_pullback (mu : ℝ) (f : MeridionalProfile)
    (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    radialSecondDerivative (radialPullback mu f) p = mu ^ 2 * radialSecondDerivative f (radialScale mu p) := by
  have hfirst : radialDerivative (radialPullback mu f) =
      fun q ↦ mu * radialPullback mu (radialDerivative f) q := by
    funext q
    exact radialDerivative_pullback mu f q (hf.differentiable (by norm_num) _)
  have hdr := differentiableAt_radialDerivative f (radialScale mu p) hf
  have hp := radialPullback_hasFDerivAt mu (radialDerivative f) p hdr
  change fderiv ℝ (radialDerivative (radialPullback mu f)) p (1, 0) = _
  rw [hfirst, (hp.const_mul mu).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    radialScaleCLM_apply, mul_one]
  change mu * fderiv ℝ (radialDerivative f) (radialScale mu p) (mu, 0) = _
  rw [profile_fderiv_apply]
  change mu * (mu * radialSecondDerivative f (radialScale mu p) + 0 * _) = _
  ring

theorem axialSecondDerivative_pullback (mu : ℝ) (f : MeridionalProfile)
    (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    axialSecondDerivative (radialPullback mu f) p = axialSecondDerivative f (radialScale mu p) := by
  have hfirst : axialDerivative (radialPullback mu f) = radialPullback mu (axialDerivative f) := by
    funext q
    exact axialDerivative_pullback mu f q (hf.differentiable (by norm_num) _)
  have hdz := differentiableAt_axialDerivative f (radialScale mu p) hf
  have hp := radialPullback_hasFDerivAt mu (axialDerivative f) p hdz
  change fderiv ℝ (axialDerivative (radialPullback mu f)) p (0, 1) = _
  rw [hfirst, hp.fderiv]
  simp [ContinuousLinearMap.comp_apply, axialSecondDerivative]

def innerAngularMomentum (mu : ℝ → ℝ) (Omega : SpacetimeProfile) (t : ℝ) : MeridionalProfile :=
  angularMomentum (radialPullback (mu t) (timeSlice Omega t))

theorem angularMomentum_scale (mu : ℝ) (Omega : MeridionalProfile) (p : ℝ × ℝ) :
    angularMomentum Omega (radialScale mu p) = mu * angularMomentum (radialPullback mu Omega) p := by
  simp [angularMomentum, radialPullback, radialScale]
  ring

theorem outerAngularMomentum_eq_mu_inner (mu : ℝ → ℝ) (Omega : SpacetimeProfile)
    (t : ℝ) (p : ℝ × ℝ) :
    angularMomentum (timeSlice Omega t) (radialScale (mu t) p) = mu t * innerAngularMomentum mu Omega t p := by
  simp [angularMomentum, innerAngularMomentum, radialPullback, radialScale]
  ring

theorem innerAngularMomentum_time_hasDerivAt (delta : ℝ) (mu : ℝ → ℝ)
    (Omega : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ)
    (hmu : HasDerivAt mu (-delta * mu t) t)
    (hOmega : DifferentiableAt ℝ Omega (t, radialScale (mu t) p)) :
    HasDerivAt (fun τ ↦ innerAngularMomentum mu Omega τ p)
      (p.1 * (timeDerivative Omega t (radialScale (mu t) p) -
        delta * mu t * p.1 * radialDerivative (timeSlice Omega t) (radialScale (mu t) p))) t := by
  have hp : HasDerivAt (fun τ ↦ radialScale (mu τ) p) (-delta * mu t * p.1, 0) t :=
    (hmu.mul_const p.1).prodMk (hasDerivAt_const t p.2)
  have hpath := (hasDerivAt_id' t).prodMk hp
  have h := (hOmega.hasFDerivAt.comp_hasDerivAt t hpath).const_mul p.1
  have hsplit := timeDerivative_plus_spatial_fderiv Omega t (radialScale (mu t) p)
    (-delta * mu t * p.1, 0) hOmega
  rw [profile_fderiv_apply] at hsplit
  convert h using 1 <;> first | rfl | (rw [hsplit]; ring)

def innerSwirlResidual (alpha beta : ℝ) (mu : ℝ → ℝ) (V W : MeridionalProfile)
    (Omega : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun τ ↦ innerAngularMomentum mu Omega τ p) t +
    2 * p.1 * (V (radialScale (mu t) p) + (alpha + beta) / 2) *
      radialDerivative (innerAngularMomentum mu Omega t) p +
    (W (radialScale (mu t) p) + beta * p.2) * axialDerivative (innerAngularMomentum mu Omega t) p -
    4 * p.1 * radialSecondDerivative (innerAngularMomentum mu Omega t) p -
    mu t * axialSecondDerivative (innerAngularMomentum mu Omega t) p

/-- Exact source conjugation. Radial diffusion has unit strength in xi=s/mu; the remaining
axial diffusion retains its transported coefficient mu. -/
theorem innerSwirlResidual_source (alpha beta : ℝ) (mu : ℝ → ℝ) (V W : MeridionalProfile)
    (Omega : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ)
    (hmu : HasDerivAt mu (-(alpha - beta) * mu t) t)
    (hOmega : DifferentiableAt ℝ Omega (t, radialScale (mu t) p))
    (hOs : ContDiff ℝ 2 (timeSlice Omega t)) :
    innerSwirlResidual alpha beta mu V W Omega t p = p.1 *
      (timeDerivative Omega t (radialScale (mu t) p) +
        swirlMomentum alpha beta V (timeSlice Omega t) W (radialScale (mu t) p) -
        mu t * swirlDiffusionCoefficient (timeSlice Omega t) (radialScale (mu t) p)) := by
  have hp := radialPullback_contDiff (mu t) (timeSlice Omega t) hOs
  have hpd := hp.differentiable (by norm_num) p
  have hos := hOs.differentiable (by norm_num) (radialScale (mu t) p)
  unfold innerSwirlResidual
  rw [(innerAngularMomentum_time_hasDerivAt (alpha - beta) mu Omega t p hmu hOmega).deriv]
  unfold innerAngularMomentum
  rw [angularMomentum_radialDerivative _ _ hpd, angularMomentum_axialDerivative _ _ hpd,
    angularMomentum_radialSecondDerivative _ _ hp, angularMomentum_axialSecondDerivative _ _ hp]
  rw [radialDerivative_pullback _ _ _ hos, axialDerivative_pullback _ _ _ hos,
    radialSecondDerivative_pullback _ _ hOs, axialSecondDerivative_pullback _ _ hOs]
  unfold radialPullback swirlMomentum swirlDiffusionCoefficient radialScale
  ring

/-- The complete Cartesian source pays the transformed inner equation on every regular
positive-viscosity chart, including the zero-radius face. -/
theorem innerSwirlResidual_of_cartesian_source (V Omega W : SpacetimeProfile)
    (P : ℝ → MeridionalProfile) (alpha beta mu : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ)
    (hmu : HasDerivAt mu (-(alpha t - beta t) * mu t) t) (hmupos : 0 < mu t) (hp : 0 ≤ p.1)
    (hV : DifferentiableAt ℝ V (t, radialScale (mu t) p))
    (hOmega : DifferentiableAt ℝ Omega (t, radialScale (mu t) p))
    (hW : DifferentiableAt ℝ W (t, radialScale (mu t) p))
    (hVs : ContDiff ℝ 2 (timeSlice V t)) (hOs : ContDiff ℝ 2 (timeSlice Omega t))
    (hWs : ContDiff ℝ 2 (timeSlice W t))
    (hP : DifferentiableAt ℝ (P t) (radialScale (mu t) p))
    (hPDE : ∀ x, centredMomentumResidual V Omega W P alpha beta mu t x = 0) :
    innerSwirlResidual (alpha t) (beta t) mu (timeSlice V t) (timeSlice W t) Omega t p = 0 := by
  let x : Space := assemble (Real.sqrt (mu t * p.1)) 0 p.2
  have hx : meridionalChart x = radialScale (mu t) p := by
    ext <;> simp [x, meridionalChart, radialScale, Real.sq_sqrt (mul_nonneg hmupos.le hp)]
  have h := centredMomentumResidual_angular_projection V Omega W P alpha beta mu t x
    (by simpa [hx] using hV) (by simpa [hx] using hOmega) (by simpa [hx] using hW)
    hVs hOs hWs (by simpa [hx] using hP)
  rw [hPDE x] at h
  simp only [PiLp.zero_apply, mul_zero, sub_self, hx] at h
  rw [angularMomentum_meridionalDiffusion (timeSlice Omega t) (radialScale (mu t) p) hOs] at h
  have hproduct : mu t * innerSwirlResidual (alpha t) (beta t) mu
      (timeSlice V t) (timeSlice W t) Omega t p = 0 := by
    rw [innerSwirlResidual_source (alpha t) (beta t) mu (timeSlice V t) (timeSlice W t)
      Omega t p hmu hOmega hOs]
    unfold movingSwirlResidual timeSliceV timeSliceW at h
    simp only [swirlDiffusionCoefficient, radialScale] at h ⊢
    linear_combination -h
  exact (mul_eq_zero.mp hproduct).resolve_left hmupos.ne'

/-- The viscosity rate follows from the actual MFR1 length and reciprocal normalizer jets. -/
theorem viscosityRatio_hasDerivAt (nu alpha beta : ℝ) (length normalizer : ℝ → ℝ) (t : ℝ)
    (hell : HasDerivAt length (-beta * length t) t)
    (hq : HasDerivAt normalizer (-alpha * normalizer t) t) (hellne : length t ≠ 0) :
    HasDerivAt (fun τ ↦ nu * normalizer τ / length τ)
      (-(alpha - beta) * (nu * normalizer t / length t)) t := by
  have h := (hq.const_mul nu).div hell hellne
  convert h using 1 <;> first | rfl | (field_simp [hellne] <;> ring)

theorem viscosityPower_hasDerivAt (j : ℕ) (delta : ℝ) (mu : ℝ → ℝ) (t : ℝ)
    (hmu : HasDerivAt mu (-delta * mu t) t) :
    HasDerivAt (fun τ ↦ mu τ ^ j) (-(j : ℝ) * delta * mu t ^ j) t := by
  have h := hmu.pow j
  have hc : (j : ℝ) * mu t ^ (j - 1) * (-delta * mu t) =
      -(j : ℝ) * delta * mu t ^ j := by
    cases j with
    | zero => simp
    | succ j => simp [pow_succ]; ring
  rw [hc] at h
  exact h

/-- The radial and viscosity indices share a scale order while retaining their separate
xi-polynomial carriers. Their sum alone does not select the radial coefficient. -/
theorem combined_monomial_inner_chart (m j n : ℕ) (mu xi z : ℝ) :
    (mu * xi) ^ m * mu ^ j * z ^ n = mu ^ (m + j) * xi ^ m * z ^ n := by
  rw [mul_pow, pow_add]
  ring

/-- The axis pressure is retained separately; dividing its complete value by mu would
introduce a spurious singular pressure carrier. -/
def innerPressure (mu : ℝ) (P : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  mu⁻¹ * (radialPullback mu P p - radialPullback 0 P p)

theorem innerPressure_reconstruct (mu : ℝ) (hmu : mu ≠ 0) (P : MeridionalProfile) (p : ℝ × ℝ) :
    radialPullback mu P p = radialPullback 0 P p + mu * innerPressure mu P p := by
  unfold innerPressure
  field_simp
  ring

theorem innerPressure_contDiff (mu : ℝ) (P : MeridionalProfile) (hP : ContDiff ℝ 2 P) :
    ContDiff ℝ 2 (innerPressure mu P) :=
  contDiff_const.mul ((radialPullback_contDiff mu P hP).sub (radialPullback_contDiff 0 P hP))

theorem radialDerivative_innerPressure (mu : ℝ) (hmu : mu ≠ 0) (P : MeridionalProfile)
    (hP : Differentiable ℝ P) (p : ℝ × ℝ) :
    radialDerivative (innerPressure mu P) p = radialDerivative P (radialScale mu p) := by
  have hd := ((radialPullback_hasFDerivAt mu P p (hP _)).sub
    (radialPullback_hasFDerivAt 0 P p (hP _))).const_mul mu⁻¹
  change HasFDerivAt (innerPressure mu P) _ p at hd
  rw [radialDerivative, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, radialScaleCLM_apply, mul_one]
  rw [profile_fderiv_apply, profile_fderiv_apply]
  field_simp <;> ring

theorem axialDerivative_innerPressure (mu : ℝ) (P : MeridionalProfile)
    (hP : Differentiable ℝ P) (p : ℝ × ℝ) :
    axialDerivative (innerPressure mu P) p = innerPressure mu (axialDerivative P) p := by
  have hd := ((radialPullback_hasFDerivAt mu P p (hP _)).sub
    (radialPullback_hasFDerivAt 0 P p (hP _))).const_mul mu⁻¹
  change HasFDerivAt (innerPressure mu P) _ p at hd
  rw [axialDerivative, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, innerPressure, radialPullback, axialDerivative]

theorem radialSecondDerivative_innerPressure (mu : ℝ) (hmu : mu ≠ 0)
    (P : MeridionalProfile) (hP : ContDiff ℝ 2 P) (p : ℝ × ℝ) :
    radialSecondDerivative (innerPressure mu P) p = mu * radialSecondDerivative P (radialScale mu p) := by
  have hfirst : radialDerivative (innerPressure mu P) = radialPullback mu (radialDerivative P) := by
    funext q
    exact radialDerivative_innerPressure mu hmu P (hP.differentiable (by norm_num)) q
  change radialDerivative (radialDerivative (innerPressure mu P)) p = _
  rw [hfirst, radialDerivative_pullback mu (radialDerivative P) p
    (differentiableAt_radialDerivative P (radialScale mu p) hP)]
  rfl

theorem axialSecondDerivative_innerPressure (mu : ℝ) (P : MeridionalProfile)
    (hP : ContDiff ℝ 2 P) (p : ℝ × ℝ) :
    axialSecondDerivative (innerPressure mu P) p =
      mu⁻¹ * (axialSecondDerivative P (radialScale mu p) - axialSecondDerivative P (radialScale 0 p)) := by
  have hfirst : axialDerivative (innerPressure mu P) = innerPressure mu (axialDerivative P) := by
    funext q
    exact axialDerivative_innerPressure mu P (hP.differentiable (by norm_num)) q
  change axialDerivative (axialDerivative (innerPressure mu P)) p = _
  rw [hfirst, axialDerivative_innerPressure mu (axialDerivative P)
    (fun q ↦ differentiableAt_axialDerivative P q hP) p]
  rfl

/-- The transformed pressure operator retains the second axial derivative of the axis trace. -/
theorem innerPressure_laplacian_identity (mu : ℝ) (hmu : mu ≠ 0)
    (P : MeridionalProfile) (hP : ContDiff ℝ 2 P) (p : ℝ × ℝ) :
    4 * (radialScale mu p).1 * radialSecondDerivative P (radialScale mu p) +
      4 * radialDerivative P (radialScale mu p) + axialSecondDerivative P (radialScale mu p) =
      axialSecondDerivative P (radialScale 0 p) +
        4 * p.1 * radialSecondDerivative (innerPressure mu P) p +
        4 * radialDerivative (innerPressure mu P) p +
        mu * axialSecondDerivative (innerPressure mu P) p := by
  rw [radialSecondDerivative_innerPressure mu hmu P hP p,
    radialDerivative_innerPressure mu hmu P (hP.differentiable (by norm_num)) p,
    axialSecondDerivative_innerPressure mu P hP p]
  simp only [radialScale]
  field_simp
  ring

def regularizedInnerPressure (P : MeridionalProfile) (p : ℝ × ℝ) (mu : ℝ) : ℝ :=
  dslope (fun r ↦ radialPullback r P p) 0 mu

theorem pressureScale_hasDerivAt_zero (P : MeridionalProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (radialScale 0 p)) :
    HasDerivAt (fun r ↦ radialPullback r P p)
      (p.1 * radialDerivative P (radialScale 0 p)) 0 := by
  have hp : HasDerivAt (fun r : ℝ ↦ radialScale r p) (p.1, 0) 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).mul_const p.1).prodMk (hasDerivAt_const 0 p.2) using 1 <;>
      first | rfl | simp
  have h := hP.hasFDerivAt.comp_hasDerivAt 0 hp
  convert h using 1 <;> first | rfl | (rw [profile_fderiv_apply]; ring)

theorem regularizedInnerPressure_of_ne (P : MeridionalProfile) (p : ℝ × ℝ)
    {mu : ℝ} (hmu : mu ≠ 0) : regularizedInnerPressure P p mu = innerPressure mu P p := by
  rw [regularizedInnerPressure, dslope_of_ne _ hmu]
  simp [slope, innerPressure]

theorem regularizedInnerPressure_zero (P : MeridionalProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (radialScale 0 p)) :
    regularizedInnerPressure P p 0 = p.1 * radialDerivative P (radialScale 0 p) := by
  rw [regularizedInnerPressure, dslope_same, (pressureScale_hasDerivAt_zero P p hP).deriv]

theorem regularizedInnerPressure_continuousAt_zero (P : MeridionalProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (radialScale 0 p)) :
    ContinuousAt (regularizedInnerPressure P p) 0 :=
  continuousAt_dslope_same.mpr (pressureScale_hasDerivAt_zero P p hP).differentiableAt

/-- Both pressure evaluations use the same viscosity parameter. The changing axis trace is
subtracted before taking the quotient, so its parameter derivative is retained and cancels. -/
def pressureFamilyDifference (P : SpacetimeProfile) (p : ℝ × ℝ) (mu : ℝ) : ℝ :=
  P (mu, radialScale mu p) - P (mu, radialScale 0 p)

def regularizedPressureFamily (P : SpacetimeProfile) (p : ℝ × ℝ) (mu : ℝ) : ℝ :=
  dslope (pressureFamilyDifference P p) 0 mu

theorem pressureFamilyDifference_hasDerivAt_zero (P : SpacetimeProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (0, radialScale 0 p)) :
    HasDerivAt (pressureFamilyDifference P p)
      (p.1 * radialDerivative (timeSlice P 0) (radialScale 0 p)) 0 := by
  have hr : HasDerivAt (fun r : ℝ ↦ radialScale r p) (p.1, 0) 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).mul_const p.1).prodMk (hasDerivAt_const 0 p.2) using 1 <;>
      first | rfl | simp
  have hp1 := (hasDerivAt_id' (0 : ℝ)).prodMk hr
  have hp0 : HasDerivAt (fun r : ℝ ↦ (r, radialScale 0 p))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) 0 :=
    (hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const 0 (radialScale 0 p))
  have h := (hP.hasFDerivAt.comp_hasDerivAt 0 hp1).sub (hP.hasFDerivAt.comp_hasDerivAt 0 hp0)
  have hsplit := timeDerivative_plus_spatial_fderiv P 0 (radialScale 0 p) (p.1, 0) hP
  rw [profile_fderiv_apply] at hsplit
  convert h using 1 <;> first | rfl | (rw [hsplit]; unfold timeDerivative; ring)

theorem regularizedPressureFamily_of_ne (P : SpacetimeProfile) (p : ℝ × ℝ)
    {mu : ℝ} (hmu : mu ≠ 0) :
    regularizedPressureFamily P p mu = innerPressure mu (timeSlice P mu) p := by
  rw [regularizedPressureFamily, dslope_of_ne _ hmu]
  simp [slope, pressureFamilyDifference, innerPressure, radialPullback, timeSlice]

theorem regularizedPressureFamily_zero (P : SpacetimeProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (0, radialScale 0 p)) :
    regularizedPressureFamily P p 0 = p.1 * radialDerivative (timeSlice P 0) (radialScale 0 p) := by
  rw [regularizedPressureFamily, dslope_same, (pressureFamilyDifference_hasDerivAt_zero P p hP).deriv]

theorem regularizedPressureFamily_continuousAt_zero (P : SpacetimeProfile) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P (0, radialScale 0 p)) :
    ContinuousAt (regularizedPressureFamily P p) 0 :=
  continuousAt_dslope_same.mpr (pressureFamilyDifference_hasDerivAt_zero P p hP).differentiableAt

/-- The physical inner radial scale is fixed by the actual MFR1 clock derivative lambda*q. -/
theorem physical_inner_radius_squared (nu length normalizer : ℝ) (hell : length ≠ 0) :
    length ^ 2 * (nu * normalizer / length) = nu * (length * normalizer) := by
  field_simp <;> ring

theorem inner_radius_squared_eq_clock_derivative (nu : ℝ) (length normalizer clock : ℝ → ℝ)
    (t : ℝ) (hell : length t ≠ 0)
    (hclock : HasDerivAt clock (length t * normalizer t) t) :
    length t ^ 2 * (nu * normalizer t / length t) = nu * deriv clock t := by
  rw [hclock.deriv]
  exact physical_inner_radius_squared nu (length t) (normalizer t) hell

theorem exponential_inner_radius_squared (nu ell0 q0 alpha beta t : ℝ)
    (hell0 : ell0 ≠ 0) (hclock : alpha + beta ≠ 0) :
    exponentialLength ell0 beta t ^ 2 *
      (nu * exponentialLength q0 alpha t / exponentialLength ell0 beta t) =
      nu * (alpha + beta) * physicalClockRemaining (ell0 * q0) (alpha + beta) t := by
  have hell : exponentialLength ell0 beta t ≠ 0 :=
    mul_ne_zero hell0 (Real.exp_ne_zero _)
  rw [physical_inner_radius_squared nu _ _ hell]
  unfold exponentialLength physicalClockRemaining
  rw [show -(alpha + beta) * t = -beta * t + -alpha * t by ring, Real.exp_add]
  field_simp <;> ring

/-- Physical angular momentum is nu times the inner carrier on every regular chart. -/
theorem physical_inner_circulation (nu length normalizer : ℝ)
    (hell : length ≠ 0) (hq : normalizer ≠ 0) (Omega : MeridionalProfile) (p : ℝ × ℝ) :
    (length / normalizer) * angularMomentum Omega (radialScale (nu * normalizer / length) p) =
      nu * angularMomentum (radialPullback (nu * normalizer / length) Omega) p := by
  rw [angularMomentum_scale]
  field_simp <;> ring

#print axioms radialScale_inverse
#print axioms radialSecondDerivative_pullback
#print axioms innerAngularMomentum_time_hasDerivAt
#print axioms innerSwirlResidual_source
#print axioms innerSwirlResidual_of_cartesian_source
#print axioms viscosityRatio_hasDerivAt
#print axioms viscosityPower_hasDerivAt
#print axioms combined_monomial_inner_chart
#print axioms innerPressure_laplacian_identity
#print axioms regularizedInnerPressure_zero
#print axioms regularizedInnerPressure_continuousAt_zero
#print axioms regularizedPressureFamily_zero
#print axioms regularizedPressureFamily_continuousAt_zero
#print axioms physical_inner_radius_squared
#print axioms inner_radius_squared_eq_clock_derivative
#print axioms exponential_inner_radius_squared
#print axioms physical_inner_circulation

end Soma.Holonics.Millennium.NavierStokesViscousInnerChart
