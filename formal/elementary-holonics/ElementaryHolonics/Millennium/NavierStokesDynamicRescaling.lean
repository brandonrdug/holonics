import Mathlib
import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import ElementaryHolonics.Millennium.NavierStokesRescalingSpace

/-!
# Dynamic rescaling of an actual open-lifespan fluid solution

MFR1 composes the existing spatial scaling with an actual moving spacetime path and amplitude.
The time jet is derived from joint differentiability, so the spatial drift and physical clock
remain part of the same derivative. No profile equation or endpoint regularity is assumed.
-/

noncomputable section

open Set Filter ContDiff InnerProductSpace
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesDynamicRescaling

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesRescalingSpace

/-- The full joint derivative separates into the actual spatial and physical-time ports. -/
theorem joint_derivative_split
    (velocity : VelocityField) (x direction : Space) (t clockJet : ℝ)
    (hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t)) :
    fderiv ℝ (Function.uncurry velocity) (x, t) (direction, clockJet) =
      fderiv ℝ (fun y ↦ velocity y t) x direction + clockJet • deriv (velocity x) t := by
  have hspace := hjoint.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have htime := hjoint.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hsp : fderiv ℝ (fun y ↦ velocity y t) x direction =
      fderiv ℝ (Function.uncurry velocity) (x, t) (direction, 0) := by
    simpa [Function.comp_def] using congrArg (fun f : Space →L[ℝ] Space ↦ f direction)
      hspace.fderiv
  have htm : deriv (velocity x) t =
      fderiv ℝ (Function.uncurry velocity) (x, t) (0, 1) := by
    simpa [Function.comp_def] using htime.deriv
  rw [hsp, htm]
  have hpair : (direction, clockJet) =
      (direction, (0 : ℝ)) + clockJet • ((0 : Space), (1 : ℝ)) := by simp
  rw [hpair, map_add, map_smul]

/-- Pulling a field along the moving spatial receiver and the physical clock retains both jets. -/
theorem hasDerivAt_velocity_along_spacetime
    (velocity : VelocityField) (position : ℝ → Space) (clock : ℝ → ℝ)
    (s : ℝ) (positionJet : Space) (clockJet : ℝ)
    (hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (position s, clock s))
    (hposition : HasDerivAt position positionJet s)
    (hclock : HasDerivAt clock clockJet s) :
    HasDerivAt (fun r ↦ velocity (position r) (clock r))
      (fderiv ℝ (fun y ↦ velocity y (clock s)) (position s) positionJet +
        clockJet • deriv (velocity (position s)) (clock s)) s := by
  have h := hjoint.hasFDerivAt.comp_hasDerivAt s (hposition.prodMk hclock)
  rw [joint_derivative_split velocity (position s) positionJet (clock s) clockJet hjoint] at h
  exact h

/-- The normalized velocity uses the same physical field through one moving chart.
`amplitude` is the multiplying normalizer `q = 1/a` of the plan's physical amplitude. -/
def rescaledVelocity (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (velocity : VelocityField) : VelocityField :=
  fun y s ↦ amplitude s • velocity (centre s + length s • y) (clock s)

/-- Pressure uses the square of the velocity's reciprocal amplitude. -/
def rescaledPressure (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (pressure : PressureField) : PressureField :=
  fun y s ↦ amplitude s ^ 2 * pressure (centre s + length s • y) (clock s)

/-- The time derivative of the normalized velocity includes the changing frame and amplitude. -/
theorem hasDerivAt_rescaledVelocity
    (velocity : VelocityField) (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet clockJet : ℝ)
    (hjoint : DifferentiableAt ℝ (Function.uncurry velocity)
      (centre s + length s • y, clock s))
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock clockJet s) :
    HasDerivAt (rescaledVelocity centre length amplitude clock velocity y)
      (amplitudeJet • velocity (centre s + length s • y) (clock s) +
        amplitude s •
          (fderiv ℝ (fun x ↦ velocity x (clock s)) (centre s + length s • y)
              (centreJet + lengthJet • y) +
            clockJet • deriv (velocity (centre s + length s • y)) (clock s))) s := by
  have hposition : HasDerivAt (fun r ↦ centre r + length r • y)
      (centreJet + lengthJet • y) s := hcentre.add (hlength.smul_const y)
  have hvelocity := hasDerivAt_velocity_along_spacetime velocity
    (fun r ↦ centre r + length r • y) clock s _ clockJet hjoint hposition hclock
  convert hamplitude.smul hvelocity using 1 <;> first | rfl | exact add_comm _ _

/-- Joint smoothness is supplied by the actual open solution at every strict interior
occurrence; no extra smoothness port is introduced for a profile. -/
theorem OpenSmoothSolutionOn.joint_contDiffAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiffAt ℝ ∞ (Function.uncurry velocity) (x, t) := by
  have hopen : IsOpen (Set.univ ×ˢ Ioo (0 : ℝ) T : Set (Space × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry velocity)
      (Set.univ ×ˢ Ioo (0 : ℝ) T) := solution.velocitySmooth.mono (by
    rintro ⟨z, r⟩ hr
    exact ⟨Set.mem_univ z, hr.2.1.le, hr.2.2⟩)
  exact hsmooth.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ x, ht⟩)

theorem OpenSmoothSolutionOn.joint_differentiableAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
  (OpenSmoothSolutionOn.joint_contDiffAt solution x ht).differentiableAt (by simp)

/-- The complete spatial derivative is the joint derivative restricted to the spatial port. -/
theorem fderiv_slice_eq_joint_spatialPort
    (velocity : VelocityField) (x : Space) (t : ℝ)
    (hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t)) :
    fderiv ℝ (fun y ↦ velocity y t) x =
      (fderiv ℝ (Function.uncurry velocity) (x, t)).comp
        (ContinuousLinearMap.inl ℝ Space ℝ) := by
  have h := hjoint.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  exact h.fderiv

/-- The whole spatial slice is smooth, derived from the source's joint smoothness. -/
theorem OpenSmoothSolutionOn.velocitySlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun x ↦ velocity x t) := by
  rw [← contDiffOn_univ]
  have h := solution.velocitySmooth.comp (s := (Set.univ : Set Space))
    (contDiff_id.prodMk (contDiff_const (c := t))).contDiffOn (by
      intro x _hx
      exact ⟨Set.mem_univ x, ht⟩)
  exact h

/-- The ordinary interior derivative reads exactly the source's momentum equation. -/
theorem OpenSmoothSolutionOn.time_derivative_eq_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    deriv (velocity x) t =
      nu • Δ (fun y ↦ velocity y t) x - gradient (fun y ↦ pressure y t) x + force x t -
        fderiv ℝ (fun y ↦ velocity y t) x (velocity x t) := by
  have hmomentum := solution.momentum x t ⟨ht.1.le, ht.2⟩
  have hslab : openTimeSlab T ∈ 𝓝 t :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) (fun _ hr ↦ ⟨hr.1.le, hr.2⟩)
  rw [derivWithin_of_mem_nhds hslab] at hmomentum
  exact (eq_sub_iff_add_eq).2 hmomentum

/-- The rescaled time jet is constructed from the actual fluid equation, including force.
The moving centre, spatial scale and amplitude are independent supplied chart functions. -/
theorem OpenSmoothSolutionOn.hasDerivAt_rescaledVelocity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet clockJet : ℝ)
    (ht : clock s ∈ Ioo 0 T)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock clockJet s) :
    HasDerivAt (rescaledVelocity centre length amplitude clock velocity y)
      (amplitudeJet • velocity (centre s + length s • y) (clock s) +
        amplitude s •
          (fderiv ℝ (fun x ↦ velocity x (clock s)) (centre s + length s • y)
              (centreJet + lengthJet • y) +
            clockJet •
              (nu • Δ (fun x ↦ velocity x (clock s)) (centre s + length s • y) -
                gradient (fun x ↦ pressure x (clock s)) (centre s + length s • y) +
                force (centre s + length s • y) (clock s) -
                fderiv ℝ (fun x ↦ velocity x (clock s)) (centre s + length s • y)
                  (velocity (centre s + length s • y) (clock s))))) s := by
  have h := Soma.Holonics.Millennium.NavierStokesDynamicRescaling.hasDerivAt_rescaledVelocity
    velocity centre length amplitude clock y s centreJet lengthJet amplitudeJet clockJet
    (OpenSmoothSolutionOn.joint_differentiableAt solution _ ht) hcentre hlength hamplitude hclock
  rw [OpenSmoothSolutionOn.time_derivative_eq_momentum solution _ ht] at h
  exact h

/-- Recombining the transported jets is an algebraic consequence of the same source momentum
balance. This helper keeps the full spatial linear map and all vector currents. -/
theorem normalized_momentum_algebra
    (nu q ell qJet ellJet : ℝ) (hq : q ≠ 0) (hell : ell ≠ 0)
    (v timeJet diffusion pressureJet force centreJet y : Space)
    (spatialJet : Space →L[ℝ] Space)
    (hmomentum : timeJet + spatialJet v = nu • diffusion - pressureJet + force) :
    (qJet • v + q • (spatialJet (centreJet + ellJet • y) +
        (ell * q) • timeJet)) + (q ^ 2 * ell) • spatialJet v =
      (nu * q / ell) • ((q * ell ^ 2) • diffusion) -
        (q ^ 2 * ell) • pressureJet +
        (ellJet / ell) • ((q * ell) • spatialJet y) +
        ell⁻¹ • ((q * ell) • spatialJet centreJet) +
        (qJet / q) • (q • v) + (ell * q ^ 2) • force := by
  have ht : timeJet = nu • diffusion - pressureJet + force - spatialJet v :=
    (eq_sub_iff_add_eq).2 hmomentum
  have hdiff : (nu * q / ell) * (q * ell ^ 2) = (ell * q ^ 2) * nu := by
    field_simp
  have hlength : (ellJet / ell) * (q * ell) = q * ellJet := by
    field_simp
  have hcentre : ell⁻¹ * (q * ell) = q := by
    field_simp
  have hamp : (qJet / q) * q = qJet := by
    field_simp
  rw [ht]
  simp only [map_add, map_smul, smul_smul]
  rw [hdiff, hlength, hcentre, hamp]
  module

/-- The actual source momentum equation in the moving frame, with the turnover clock
`clock' = length * amplitude`. The transformed viscosity, centre motion, dilation current,
amplitude current and force are all derived. -/
theorem OpenSmoothSolutionOn.rescaled_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet : ℝ)
    (ht : clock s ∈ Ioo 0 T)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock (length s * amplitude s) s)
    (hq : amplitude s ≠ 0) (hell : length s ≠ 0) :
    let U := rescaledVelocity centre length amplitude clock velocity
    let P := rescaledPressure centre length amplitude clock pressure
    deriv (U y) s + fderiv ℝ (fun z ↦ U z s) y (U y s) =
      (nu * amplitude s / length s) • Δ (fun z ↦ U z s) y -
        gradient (fun z ↦ P z s) y +
        (lengthJet / length s) • fderiv ℝ (fun z ↦ U z s) y y +
        (length s)⁻¹ • fderiv ℝ (fun z ↦ U z s) y centreJet +
        (amplitudeJet / amplitude s) • U y s +
        (length s * amplitude s ^ 2) • force (centre s + length s • y) (clock s) := by
  dsimp only
  have hjet := Soma.Holonics.Millennium.NavierStokesDynamicRescaling.hasDerivAt_rescaledVelocity
    velocity centre length amplitude clock y s centreJet lengthJet amplitudeJet
    (length s * amplitude s)
    (OpenSmoothSolutionOn.joint_differentiableAt solution _ ht)
    hcentre hlength hamplitude hclock
  have hsmooth : ContDiff ℝ 2 (fun x ↦ velocity x (clock s)) :=
    (OpenSmoothSolutionOn.velocitySlice_contDiff solution ⟨ht.1.le, ht.2⟩).of_le (by
      show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  change deriv (rescaledVelocity centre length amplitude clock velocity y) s +
      fderiv ℝ (spatialPullback (amplitude s) (length s) (centre s)
        (fun x ↦ velocity x (clock s))) y
        (spatialPullback (amplitude s) (length s) (centre s)
          (fun x ↦ velocity x (clock s)) y) =
    (nu * amplitude s / length s) •
        Δ (spatialPullback (amplitude s) (length s) (centre s)
          (fun x ↦ velocity x (clock s))) y -
      gradient (spatialPullback (amplitude s ^ 2) (length s) (centre s)
        (fun x ↦ pressure x (clock s))) y +
      (lengthJet / length s) •
        fderiv ℝ (spatialPullback (amplitude s) (length s) (centre s)
          (fun x ↦ velocity x (clock s))) y y +
      (length s)⁻¹ •
        fderiv ℝ (spatialPullback (amplitude s) (length s) (centre s)
          (fun x ↦ velocity x (clock s))) y centreJet +
      (amplitudeJet / amplitude s) •
        spatialPullback (amplitude s) (length s) (centre s)
          (fun x ↦ velocity x (clock s)) y +
      (length s * amplitude s ^ 2) • force (centre s + length s • y) (clock s)
  rw [hjet.deriv, advection_spatialPullback,
    laplacian_spatialPullback _ _ _ _ hsmooth, gradient_spatialPullback]
  simp only [fderiv_spatialPullback, smul_apply, smul_smul,
    spatialPullback]
  simpa only [smul_smul] using
    normalized_momentum_algebra nu (amplitude s) (length s) amplitudeJet lengthJet hq hell
    (velocity (centre s + length s • y) (clock s))
    (deriv (velocity (centre s + length s • y)) (clock s))
    (Δ (fun x ↦ velocity x (clock s)) (centre s + length s • y))
    (gradient (fun x ↦ pressure x (clock s)) (centre s + length s • y))
    (force (centre s + length s • y) (clock s)) centreJet y
    (fderiv ℝ (fun x ↦ velocity x (clock s)) (centre s + length s • y))
    ((eq_sub_iff_add_eq).1
      (OpenSmoothSolutionOn.time_derivative_eq_momentum solution _ ht))

/-- Incompressibility follows from the source divergence, including zero chart multipliers. -/
theorem OpenSmoothSolutionOn.rescaled_incompressible
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (ht : clock s ∈ openTimeSlab T) :
    divergence (fun z ↦ rescaledVelocity centre length amplitude clock velocity z s) y = 0 := by
  change divergence (spatialPullback (amplitude s) (length s) (centre s)
    (fun x ↦ velocity x (clock s))) y = 0
  rw [divergence_spatialPullback, solution.incompressible _ _ ht, mul_zero]

/-- The initial occurrence is pulled back from the actual initial data when the clock reads zero. -/
theorem OpenSmoothSolutionOn.rescaled_initial
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (ht : clock s = 0) :
    rescaledVelocity centre length amplitude clock velocity y s =
      amplitude s • initial (centre s + length s • y) := by
  simp only [rescaledVelocity, ht, solution.initial]

/-- The moving spatial chart retains the transported period of the source velocity. -/
theorem OpenPeriodicSolutionOn.rescaled_velocity_period
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (s : ℝ) (ht : clock s ∈ openTimeSlab T) (hell : length s ≠ 0) :
    ∀ y i, rescaledVelocity centre length amplitude clock velocity
      (y + (length s)⁻¹ • EuclideanSpace.single i 1) s =
      rescaledVelocity centre length amplitude clock velocity y s :=
  spatialPullback_isPeriodic (amplitude s) (length s) hell (centre s)
    (solution.velocityPeriodic _ ht)

/-- Pressure carries exactly the same rescaled period as velocity. -/
theorem OpenPeriodicSolutionOn.rescaled_pressure_period
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (s : ℝ) (ht : clock s ∈ openTimeSlab T) (hell : length s ≠ 0) :
    ∀ y i, rescaledPressure centre length amplitude clock pressure
      (y + (length s)⁻¹ • EuclideanSpace.single i 1) s =
      rescaledPressure centre length amplitude clock pressure y s :=
  spatialPullback_isPeriodic (amplitude s ^ 2) (length s) hell (centre s)
    (solution.pressurePeriodic _ ht)

/-- The physical velocity is recovered on every regular spatial-amplitude chart. -/
theorem rescaledVelocity_reconstruct
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (velocity : VelocityField) (x : Space) (s : ℝ)
    (hq : amplitude s ≠ 0) (hell : length s ≠ 0) :
    (amplitude s)⁻¹ • rescaledVelocity centre length amplitude clock velocity
      ((length s)⁻¹ • (x - centre s)) s = velocity x (clock s) := by
  have h := spatialPushforward_spatialPullback (amplitude s) (length s) hq hell
    (centre s) (fun z ↦ velocity z (clock s))
  exact congrFun h x

/-- At a zero normalizer the displayed velocity is zero; no inverse statement is made there. -/
theorem rescaledVelocity_zero_normalizer
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (velocity : VelocityField) (y : Space) (s : ℝ) (hq : amplitude s = 0) :
    rescaledVelocity centre length amplitude clock velocity y s = 0 := by
  simp [rescaledVelocity, hq]

#print axioms OpenSmoothSolutionOn.hasDerivAt_rescaledVelocity
#print axioms OpenSmoothSolutionOn.rescaled_momentum
#print axioms OpenSmoothSolutionOn.rescaled_incompressible
#print axioms OpenPeriodicSolutionOn.rescaled_velocity_period
#print axioms OpenPeriodicSolutionOn.rescaled_pressure_period
#print axioms rescaledVelocity_reconstruct

end Soma.Holonics.Millennium.NavierStokesDynamicRescaling
