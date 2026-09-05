import ElementaryHolonics.Millennium.NavierStokesRescalingPeriodObstruction
import ElementaryHolonics.Millennium.NavierStokesPeriodicPressureRigidity
import ElementaryHolonics.Millennium.NavierStokesRescalingClock

/-!
# The source momentum excludes a growing global stationary profile on the torus

The changing period first makes the globally fixed normalized profile spatially constant.
Its actual rescaled momentum then makes the periodic pressure gradient a constant multiple of
that profile. Periodic pressure rigidity kills this constant gradient. At any interior chart
time where the amplitude normalizer changes, the profile is therefore zero.

This is an exclusion for the declared exact global ansatz. Local convergence on an expanding
fundamental cell and genuinely time-dependent profiles remain outside this hypothesis.
-/

noncomputable section

open Set Filter ContDiff InnerProductSpace
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesStationaryRescalingExclusion

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling
open Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction
open Soma.Holonics.Millennium.NavierStokesPeriodicPressureRigidity
open Soma.Holonics.Millennium.NavierStokesRescalingClock

theorem pressureSlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun x ↦ pressure x t) := by
  rw [← contDiffOn_univ]
  exact solution.pressureSmooth.comp (s := (Set.univ : Set Space))
    (contDiff_id.prodMk (contDiff_const (c := t))).contDiffOn
    (by intro x _hx; exact ⟨Set.mem_univ x, ht⟩)

theorem rescaledPressure_slice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (s : ℝ) (ht : clock s ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun y ↦ rescaledPressure centre length amplitude clock pressure y s) := by
  have hp := pressureSlice_contDiff solution ht
  have hmap : ContDiff ℝ ∞ (fun y : Space ↦ centre s + length s • y) :=
    contDiff_const.add (contDiff_id.const_smul (length s))
  exact contDiff_const.mul (hp.comp hmap)

/-- A globally stationary profile cannot carry a changing normalization amplitude in this
actual unforced periodic source. No stability or terminal assumption is used. -/
theorem OpenPeriodicSolutionOn.stationaryProfile_eq_zero
    {T nu ell₀ beta : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hell₀ : 0 < ell₀) (hbeta : 0 < beta)
    (centre : ℝ → Space) (amplitude clock : ℝ → ℝ) (profile : Space → Space)
    (hprofile : ∀ s : ℝ, 0 ≤ s → ∀ y,
      rescaledVelocity centre (exponentialLength ell₀ beta) amplitude clock velocity y s = profile y)
    (hinside : ∀ s : ℝ, 0 ≤ s → clock s ∈ openTimeSlab T)
    (s : ℝ) (hs : 0 < s) (ht : clock s ∈ Ioo 0 T)
    (centreJet : Space) (lengthJet amplitudeJet : ℝ)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt (exponentialLength ell₀ beta) lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock (exponentialLength ell₀ beta s * amplitude s) s)
    (hq : amplitude s ≠ 0) (hqJet : amplitudeJet ≠ 0) :
    ∀ y, profile y = 0 := by
  let length := exponentialLength ell₀ beta
  have hell : length s ≠ 0 := mul_ne_zero hell₀.ne' (Real.exp_ne_zero _)
  have hconstant :=
    Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction.OpenPeriodicSolutionOn.stationaryProfile_constant_exponential
      solution hell₀ hbeta centre amplitude clock profile hprofile hinside
  have htime (y : Space) : deriv (rescaledVelocity centre length amplitude clock velocity y) s = 0 := by
    have heq : rescaledVelocity centre length amplitude clock velocity y =ᶠ[𝓝 s]
        (fun _ : ℝ ↦ profile 0) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact (hprofile r hr.le y).trans (hconstant y)
    rw [heq.deriv_eq, deriv_const]
  have hspace : (fun y ↦ rescaledVelocity centre length amplitude clock velocity y s) =
      (fun _ : Space ↦ profile 0) := funext fun y ↦ (hprofile s hs.le y).trans (hconstant y)
  let P : Space → ℝ := fun y ↦ rescaledPressure centre length amplitude clock pressure y s
  have hP : ContDiff ℝ 1 P :=
    (rescaledPressure_slice_contDiff solution.toOpenSmoothSolutionOn centre length amplitude clock
      s ⟨ht.1.le, ht.2⟩).of_le (by simp)
  have hperiod : ∀ y i, P (y + (length s)⁻¹ • EuclideanSpace.single i 1) = P y :=
    Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenPeriodicSolutionOn.rescaled_pressure_period
      solution centre length amplitude clock s ⟨ht.1.le, ht.2⟩ hell
  have hgrad : ∀ y, gradient P y = (amplitudeJet / amplitude s) • profile 0 := by
    intro y
    have hm :=
      Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.rescaled_momentum
        solution.toOpenSmoothSolutionOn centre length amplitude clock y s centreJet lengthJet
        amplitudeJet ht hcentre hlength hamplitude hclock hq hell
    dsimp only at hm
    have hvalue : rescaledVelocity centre length amplitude clock velocity y s = profile 0 :=
      congrFun hspace y
    have hbalance : (0 : Space) = -gradient P y + (amplitudeJet / amplitude s) • profile 0 := by
      simpa [hspace, htime y, hvalue, P] using hm
    have hn := congrArg Neg.neg (eq_neg_of_add_eq_zero_left hbalance.symm)
    simpa using hn
  have hzero := constant_gradient_eq_zero_of_periodic P hP (length s)⁻¹ (inv_ne_zero hell)
    hperiod ((amplitudeJet / amplitude s) • profile 0) hgrad
  have hprofileZero : profile 0 = 0 := (smul_eq_zero.mp hzero).resolve_left (div_ne_zero hqJet hq)
  exact fun y ↦ (hconstant y).trans hprofileZero

/-- The exponential concentration chart discharges all derivative and physical-time premises.
Its normalizer is the reciprocal physical amplitude: `q = q₀ exp(-alpha s)`. -/
theorem OpenPeriodicSolutionOn.exponential_stationaryProfile_eq_zero
    {nu ell₀ q₀ alpha beta : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (hell₀ : 0 < ell₀) (hq₀ : 0 < q₀) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (solution : OpenPeriodicSolutionOn (physicalClockEndpoint 0 (ell₀ * q₀) (alpha + beta))
      nu initial (0 : VelocityField) velocity pressure)
    (centre : Space) (profile : Space → Space)
    (hprofile : ∀ s : ℝ, 0 ≤ s → ∀ y,
      rescaledVelocity (fun _ ↦ centre) (exponentialLength ell₀ beta)
        (exponentialLength q₀ alpha) (physicalClock 0 (ell₀ * q₀) (alpha + beta))
        velocity y s = profile y) :
    ∀ y, profile y = 0 := by
  have hB : 0 < ell₀ * q₀ := mul_pos hell₀ hq₀
  have hk : 0 < alpha + beta := add_pos halpha hbeta
  have hinside (s : ℝ) (hs : 0 ≤ s) :
      physicalClock 0 (ell₀ * q₀) (alpha + beta) s ∈
        openTimeSlab (physicalClockEndpoint 0 (ell₀ * q₀) (alpha + beta)) :=
    physicalClock_mem_Ico hB hk hs
  have hturnover : HasDerivAt (physicalClock 0 (ell₀ * q₀) (alpha + beta))
      (exponentialLength ell₀ beta 1 * exponentialLength q₀ alpha 1) 1 := by
    convert physicalClock_hasDerivAt (t₀ := 0) (B := ell₀ * q₀) (s := 1) hk using 1
    simp only [exponentialLength, mul_one]
    rw [show -(alpha + beta) = -beta + -alpha by ring, Real.exp_add]
    ring
  exact OpenPeriodicSolutionOn.stationaryProfile_eq_zero solution hell₀ hbeta
    (fun _ ↦ centre) (exponentialLength q₀ alpha)
    (physicalClock 0 (ell₀ * q₀) (alpha + beta)) profile hprofile hinside 1
    zero_lt_one ⟨physicalClock_gt_initial hB hk zero_lt_one,
      physicalClock_lt_endpoint hB hk⟩ 0
    (-beta * exponentialLength ell₀ beta 1) (-alpha * exponentialLength q₀ alpha 1)
    (hasDerivAt_const 1 centre) (exponentialLength_hasDerivAt ell₀ beta 1)
    (exponentialLength_hasDerivAt q₀ alpha 1) hturnover
    (mul_ne_zero hq₀.ne' (Real.exp_ne_zero _))
    (mul_ne_zero (neg_ne_zero.mpr halpha.ne') (mul_ne_zero hq₀.ne' (Real.exp_ne_zero _)))

#print axioms pressureSlice_contDiff
#print axioms OpenPeriodicSolutionOn.stationaryProfile_eq_zero
#print axioms OpenPeriodicSolutionOn.exponential_stationaryProfile_eq_zero

end Soma.Holonics.Millennium.NavierStokesStationaryRescalingExclusion
