import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling
import ElementaryHolonics.Millennium.NavierStokesLinearFrameSpace

/-!
# The moving linear frame retains its complete physical time jet

The spatial map, its inverse and the physical-clock rate remain factored continuous-linear
maps. The same physical velocity supplies every derivative. The linear-frame momentum algebra
retains centre motion, grid deformation, pressure and force before spatial operators are joined.
-/

noncomputable section
open ContDiff Set Filter InnerProductSpace
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling
open Soma.Holonics.Millennium.NavierStokesLinearFrameSpace

def linearFrameVelocity (centre : ℝ → Space)
    (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ) (velocity : VelocityField) : VelocityField :=
  fun y t ↦ rate t • B t (velocity (centre t + A t y) (clock t))

def linearFramePressure (centre : ℝ → Space)
    (A : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ) (pressure : PressureField) : PressureField :=
  fun y t ↦ rate t ^ 2 * pressure (centre t + A t y) (clock t)

/-- The actual differentiated inverse identity; no inverse-time jet is selected by a profile. -/
theorem inverse_frame_derivative (A B : ℝ → Space →L[ℝ] Space)
    (Ajet Bjet : Space →L[ℝ] Space) (t : ℝ)
    (hA : HasDerivAt A Ajet t) (hB : HasDerivAt B Bjet t)
    (hBA : (fun τ ↦ (B τ).comp (A τ)) =ᶠ[𝓝 t] fun _ ↦ ContinuousLinearMap.id ℝ Space)
    (hAB : (A t).comp (B t) = ContinuousLinearMap.id ℝ Space) :
    Bjet = -((B t).comp Ajet).comp (B t) := by
  have hd := hB.clm_comp hA
  have hz := (hasDerivAt_const t (ContinuousLinearMap.id ℝ Space)).congr_of_eventuallyEq hBA
  have heq := hd.unique hz
  have happ := congrArg (fun L : Space →L[ℝ] Space ↦ L.comp (B t)) heq
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_assoc, hAB, ContinuousLinearMap.comp_id] at happ
  exact eq_neg_of_add_eq_zero_left happ

theorem hasDerivAt_linearFrameVelocity (centre : ℝ → Space)
    (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ) (velocity : VelocityField)
    (y : Space) (t : ℝ) (centreJet : Space) (Ajet Bjet : Space →L[ℝ] Space) (rateJet clockJet : ℝ)
    (hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (centre t + A t y, clock t))
    (hc : HasDerivAt centre centreJet t) (hA : HasDerivAt A Ajet t)
    (hB : HasDerivAt B Bjet t) (hb : HasDerivAt rate rateJet t)
    (hclock : HasDerivAt clock clockJet t) :
    HasDerivAt (linearFrameVelocity centre A B rate clock velocity y)
      (rateJet • B t (velocity (centre t + A t y) (clock t)) +
        rate t • (Bjet (velocity (centre t + A t y) (clock t)) +
          B t (fderiv ℝ (fun x ↦ velocity x (clock t)) (centre t + A t y)
            (centreJet + Ajet y) + clockJet • deriv (velocity (centre t + A t y)) (clock t)))) t := by
  have hposition := hc.add (hA.clm_apply (hasDerivAt_const t y))
  simp only [map_zero, add_zero] at hposition
  have hv := hasDerivAt_velocity_along_spacetime velocity
    (fun τ ↦ centre τ + A τ y) clock t (centreJet + Ajet y) clockJet hjoint hposition hclock
  have h := hb.smul (hB.clm_apply hv)
  convert h using 1 <;> first | rfl | module

/-- The physical solution pays the time derivative, including its actual pressure and force. -/
theorem OpenSmoothSolutionOn.linearFrame_time_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ)
    (y : Space) (t : ℝ) (centreJet : Space) (Ajet Bjet : Space →L[ℝ] Space) (rateJet : ℝ)
    (ht : clock t ∈ Ioo 0 T) (hc : HasDerivAt centre centreJet t)
    (hA : HasDerivAt A Ajet t) (hB : HasDerivAt B Bjet t)
    (hb : HasDerivAt rate rateJet t) (hclock : HasDerivAt clock (rate t) t) :
    HasDerivAt (linearFrameVelocity centre A B rate clock velocity y)
      (rateJet • B t (velocity (centre t + A t y) (clock t)) +
        rate t • (Bjet (velocity (centre t + A t y) (clock t)) +
          B t (fderiv ℝ (fun x ↦ velocity x (clock t)) (centre t + A t y)
            (centreJet + Ajet y) + rate t •
              (nu • Δ (fun x ↦ velocity x (clock t)) (centre t + A t y) -
                gradient (fun x ↦ pressure x (clock t)) (centre t + A t y) +
                force (centre t + A t y) (clock t) -
                fderiv ℝ (fun x ↦ velocity x (clock t)) (centre t + A t y)
                  (velocity (centre t + A t y) (clock t)))))) t := by
  have h := hasDerivAt_linearFrameVelocity centre A B rate clock velocity y t centreJet
    Ajet Bjet rateJet (rate t) (OpenSmoothSolutionOn.joint_differentiableAt solution _ ht)
    hc hA hB hb hclock
  rw [OpenSmoothSolutionOn.time_derivative_eq_momentum solution _ ht] at h
  exact h

/-- Recombine the same physical jets into the transported momentum law. -/
theorem linear_momentum_algebra (nu b bJet : ℝ) (hb : b ≠ 0)
    (A B Ajet spatialJet : Space →L[ℝ] Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (v timeJet diffusion pressureJet force centreJet y : Space)
    (hsource : timeJet + spatialJet v = nu • diffusion - pressureJet + force) :
    let U := b • B v
    let J := b • (B.comp spatialJet).comp A
    (bJet • B v + b • (-B (Ajet (B v)) +
      B (spatialJet (centreJet + Ajet y) + b • timeJet))) +
      J (U - B (centreJet + Ajet y)) + B (Ajet U) - (bJet / b) • U =
      (nu * b) • (b • B diffusion) - b ^ 2 • B pressureJet + b ^ 2 • B force := by
  have hab (z : Space) : A (B z) = z :=
    congrArg (fun L : Space →L[ℝ] Space ↦ L z) hAB
  have ht : timeJet = nu • diffusion - pressureJet + force - spatialJet v :=
    (eq_sub_iff_add_eq).mpr hsource
  have hcancel : bJet / b * b = bJet := div_mul_cancel₀ bJet hb
  dsimp only
  rw [ht]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_smul, hab, smul_add, smul_sub, smul_neg, smul_smul, hcancel]
  module

theorem OpenSmoothSolutionOn.pressureSlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) : ContDiff ℝ ∞ (fun x ↦ pressure x t) := by
  rw [← contDiffOn_univ]
  exact solution.pressureSmooth.comp
    (contDiff_id.prodMk (contDiff_const (c := t))).contDiffOn
    (by intro x _; exact ⟨Set.mem_univ x, ht⟩)

/-- The complete moving linear-frame equation is paid by the actual physical solution.
Pressure and viscosity use the same inverse metric; the grid and centre currents are retained. -/
theorem OpenSmoothSolutionOn.linearFrame_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ)
    (y : Space) (t : ℝ) (centreJet : Space) (Ajet : Space →L[ℝ] Space) (rateJet : ℝ)
    (ht : clock t ∈ Ioo 0 T) (hc : HasDerivAt centre centreJet t)
    (hA : HasDerivAt A Ajet t)
    (hB : HasDerivAt B (-((B t).comp Ajet).comp (B t)) t)
    (hb : HasDerivAt rate rateJet t) (hclock : HasDerivAt clock (rate t) t)
    (hbne : rate t ≠ 0) (hAB : (A t).comp (B t) = ContinuousLinearMap.id ℝ Space) :
    let U := linearFrameVelocity centre A B rate clock velocity
    let P := linearFramePressure centre A rate clock pressure
    deriv (U y) t + fderiv ℝ (fun z ↦ U z t) y (U y t - B t (centreJet + Ajet y)) +
      B t (Ajet (U y t)) - (rateJet / rate t) • U y t =
        (nu * rate t) • weightedLaplacian (B t) (fun z ↦ U z t) y -
          ((B t).comp (B t).adjoint) (gradient (fun z ↦ P z t) y) +
          rate t ^ 2 • B t (force (centre t + A t y) (clock t)) := by
  dsimp only
  have htime := hasDerivAt_linearFrameVelocity centre A B rate clock velocity y t centreJet
    Ajet (-((B t).comp Ajet).comp (B t)) rateJet (rate t)
    (OpenSmoothSolutionOn.joint_differentiableAt solution _ ht) hc hA hB hb hclock
  have hu : ContDiff ℝ 2 (fun x ↦ velocity x (clock t)) :=
    (OpenSmoothSolutionOn.velocitySlice_contDiff solution ⟨ht.1.le, ht.2⟩).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hp : DifferentiableAt ℝ (fun x ↦ pressure x (clock t)) (centre t + A t y) :=
    (OpenSmoothSolutionOn.pressureSlice_contDiff solution ⟨ht.1.le, ht.2⟩).differentiable (by simp) _
  have hpadj : (B t).adjoint.comp (A t).adjoint = ContinuousLinearMap.id ℝ Space := by
    have h := congrArg ContinuousLinearMap.adjoint hAB
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using h
  have hpadj_apply (v : Space) : (B t).adjoint ((A t).adjoint v) = v :=
    congrArg (fun L : Space →L[ℝ] Space ↦ L v) hpadj
  change deriv (linearFrameVelocity centre A B rate clock velocity y) t +
    fderiv ℝ (velocityPullback (rate t) (A t) (B t) (centre t) (fun x ↦ velocity x (clock t))) y
      (velocityPullback (rate t) (A t) (B t) (centre t) (fun x ↦ velocity x (clock t)) y -
        B t (centreJet + Ajet y)) +
    B t (Ajet (velocityPullback (rate t) (A t) (B t) (centre t) (fun x ↦ velocity x (clock t)) y)) -
    (rateJet / rate t) • velocityPullback (rate t) (A t) (B t) (centre t) (fun x ↦ velocity x (clock t)) y =
      (nu * rate t) • weightedLaplacian (B t)
        (velocityPullback (rate t) (A t) (B t) (centre t) (fun x ↦ velocity x (clock t))) y -
      ((B t).comp (B t).adjoint)
        (gradient (pressurePullback (rate t) (A t) (centre t) (fun x ↦ pressure x (clock t))) y) + _
  rw [htime.deriv, fderiv_velocityPullback _ _ _ _ _ _ (hu.differentiable (by norm_num) _),
    weightedLaplacian_velocityPullback _ _ _ _ _ _ hu hAB,
    gradient_pressurePullback _ _ _ _ _ hp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_smul, hpadj_apply]
  exact linear_momentum_algebra nu (rate t) rateJet hbne (A t) (B t) Ajet
    (fderiv ℝ (fun x ↦ velocity x (clock t)) (centre t + A t y)) hAB
    (velocity (centre t + A t y) (clock t))
    (deriv (velocity (centre t + A t y)) (clock t))
    (Δ (fun x ↦ velocity x (clock t)) (centre t + A t y))
    (gradient (fun x ↦ pressure x (clock t)) (centre t + A t y))
    (force (centre t + A t y) (clock t)) centreJet y
    ((eq_sub_iff_add_eq).mp (OpenSmoothSolutionOn.time_derivative_eq_momentum solution _ ht))

theorem OpenSmoothSolutionOn.linearFrame_incompressible
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ)
    (y : Space) (t : ℝ) (ht : clock t ∈ openTimeSlab T)
    (hAB : (A t).comp (B t) = ContinuousLinearMap.id ℝ Space) :
    divergence (fun z ↦ linearFrameVelocity centre A B rate clock velocity z t) y = 0 := by
  change divergence (velocityPullback (rate t) (A t) (B t) (centre t)
    (fun x ↦ velocity x (clock t))) y = 0
  rw [divergence_velocityPullback _ _ _ _ _ _
    ((OpenSmoothSolutionOn.velocitySlice_contDiff solution ht).differentiable (by simp) _) hAB,
    solution.incompressible _ _ ht, mul_zero]

#print axioms inverse_frame_derivative
#print axioms hasDerivAt_linearFrameVelocity
#print axioms OpenSmoothSolutionOn.linearFrame_time_hasDerivAt
#print axioms linear_momentum_algebra
#print axioms OpenSmoothSolutionOn.linearFrame_momentum
#print axioms OpenSmoothSolutionOn.linearFrame_incompressible
end Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics
