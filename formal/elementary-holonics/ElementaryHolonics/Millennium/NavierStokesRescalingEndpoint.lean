import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling
import ElementaryHolonics.Millennium.NavierStokesRescalingClock

/-!
# A retained rescaled receiver obstructs physical continuation

The moving chart is joined to the actual compatible-extension owner. When its sampled spatial
point approaches a finite point, its clock approaches the finite terminal time from within the
old lifespan, and a vanishing normalization leaves a nonzero value or spatial derivative,
no compatible smooth extension exists. The scale and lower-bound hypotheses are exposed; this
does not construct an initial condition satisfying them or assert a Navier--Stokes singularity.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesRescalingEndpoint

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling
open Soma.Holonics.Millennium.NavierStokesRescalingSpace
open Soma.Holonics.Millennium.NavierStokesRescalingClock

/-- The physical occurrence sampled by one fixed point in the normalized chart. -/
def spacetimePath (centre : ℝ → Space) (length clock : ℝ → ℝ) (y : Space) :
    ℝ → Space × ℝ := fun s ↦ (centre s + length s • y, clock s)

theorem tendsto_spacetimePath
    {centre : ℝ → Space} {length clock : ℝ → ℝ} {xstar : Space} {T : ℝ}
    (y : Space) (hcentre : Tendsto centre atTop (𝓝 xstar))
    (hlength : Tendsto length atTop (𝓝 0)) (hclock : Tendsto clock atTop (𝓝 T)) :
    Tendsto (spacetimePath centre length clock y) atTop (𝓝 (xstar, T)) := by
  have hposition : Tendsto (fun s ↦ centre s + length s • y) atTop (𝓝 xstar) := by
    simpa using hcentre.add (hlength.smul_const y)
  exact hposition.prodMk_nhds hclock

/-- A nonzero normalized velocity behind a vanishing multiplier obstructs every compatible
extension. Both the source path and the extension's old-lifespan agreement are used. -/
theorem OpenPeriodicSolutionOn.isMaximal_of_rescaled_value
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y xstar : Space) {δ : ℝ} (hδ : 0 < δ)
    (hcentre : Tendsto centre atTop (𝓝 xstar))
    (hlength : Tendsto length atTop (𝓝 0))
    (hamplitude : Tendsto amplitude atTop (𝓝 0))
    (hclock : Tendsto clock atTop (𝓝 T))
    (hinside : ∀ᶠ s in atTop, clock s ∈ Ioo 0 T)
    (hlower : ∀ᶠ s in atTop,
      δ ≤ ‖rescaledVelocity centre length amplitude clock velocity y s‖) :
    solution.IsMaximal := by
  rintro ⟨extension⟩
  have hcontinuous : ContinuousAt (Function.uncurry extension.extendedVelocity) (xstar, T) :=
    (Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.joint_contDiffAt
      extension.extendedSolution.toOpenSmoothSolutionOn xstar
        ⟨solution.terminal_pos, extension.terminal_lt⟩).continuousAt
  have hlower' : ∀ᶠ s in atTop,
      δ ≤ ‖amplitude s • Function.uncurry extension.extendedVelocity
        (spacetimePath centre length clock y s)‖ := by
    filter_upwards [hinside, hlower] with s hs hlarge
    change δ ≤ ‖amplitude s •
      extension.extendedVelocity (centre s + length s • y) (clock s)‖
    rw [← extension.agreesBefore.velocity _ _ ⟨hs.1.le, hs.2⟩]
    exact hlarge
  exact scaledReceiver_eventually_nonzero_implies_not_continuousAt
    hamplitude (tendsto_spacetimePath y hcentre hlength hclock) hδ hlower' hcontinuous

/-- The spatial derivative is a stronger continuation receiver than the velocity value.
Its normalizer is the product of amplitude and spatial scale, exactly as the chain rule returns.
No claim that the normalized derivative stays nonzero is hidden in a certificate. -/
theorem OpenPeriodicSolutionOn.isMaximal_of_rescaled_spatialDerivative
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y xstar : Space) {δ : ℝ} (hδ : 0 < δ)
    (hcentre : Tendsto centre atTop (𝓝 xstar))
    (hlength : Tendsto length atTop (𝓝 0))
    (hscale : Tendsto (fun s ↦ amplitude s * length s) atTop (𝓝 0))
    (hclock : Tendsto clock atTop (𝓝 T))
    (hinside : ∀ᶠ s in atTop, clock s ∈ Ioo 0 T)
    (hlower : ∀ᶠ s in atTop,
      δ ≤ ‖fderiv ℝ (fun z ↦ rescaledVelocity centre length amplitude clock velocity z s) y‖) :
    solution.IsMaximal := by
  rintro ⟨extension⟩
  let receiver : Space × ℝ → (Space →L[ℝ] Space) := fun event ↦
    (fderiv ℝ (Function.uncurry extension.extendedVelocity) event).comp
      (ContinuousLinearMap.inl ℝ Space ℝ)
  have hsmooth :=
    Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.joint_contDiffAt
      extension.extendedSolution.toOpenSmoothSolutionOn xstar
        ⟨solution.terminal_pos, extension.terminal_lt⟩
  have hcontinuous : ContinuousAt receiver (xstar, T) :=
    (hsmooth.continuousAt_fderiv (by simp)).clm_comp continuousAt_const
  have hlower' : ∀ᶠ s in atTop,
      δ ≤ ‖(amplitude s * length s) • receiver (spacetimePath centre length clock y s)‖ := by
    filter_upwards [hinside, hlower] with s hs hlarge
    have hfields : (fun x ↦ velocity x (clock s)) =
        (fun x ↦ extension.extendedVelocity x (clock s)) := by
      funext x
      exact extension.agreesBefore.velocity x _ ⟨hs.1.le, hs.2⟩
    have hjoint :=
      Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.joint_differentiableAt
        extension.extendedSolution.toOpenSmoothSolutionOn (centre s + length s • y)
          ⟨hs.1, hs.2.trans extension.terminal_lt⟩
    have hscaled :
        fderiv ℝ (fun z ↦ rescaledVelocity centre length amplitude clock velocity z s) y =
          (amplitude s * length s) • receiver (spacetimePath centre length clock y s) := by
      change fderiv ℝ (spatialPullback (amplitude s) (length s) (centre s)
        (fun x ↦ velocity x (clock s))) y = _
      rw [fderiv_spatialPullback, hfields,
        fderiv_slice_eq_joint_spatialPort extension.extendedVelocity _ _ hjoint, smul_smul]
      rfl
    rw [← hscaled]
    exact hlarge
  exact scaledReceiver_eventually_nonzero_implies_not_continuousAt
    (X := Space × ℝ) (E := Space →L[ℝ] Space)
    (q := fun s ↦ amplitude s * length s)
    (state := spacetimePath centre length clock y) (receiver := receiver)
    (xstar := (xstar, T))
    hscale (tendsto_spacetimePath y hcentre hlength hclock) hδ hlower' hcontinuous

#print axioms tendsto_spacetimePath
#print axioms OpenPeriodicSolutionOn.isMaximal_of_rescaled_value
#print axioms OpenPeriodicSolutionOn.isMaximal_of_rescaled_spatialDerivative

end Soma.Holonics.Millennium.NavierStokesRescalingEndpoint
