import ElementaryHolonics.Millennium.NavierStokesAnisotropicDynamics
import ElementaryHolonics.Millennium.NavierStokesRescalingClock
import ElementaryHolonics.Millennium.NavierStokesRescalingPeriodObstruction

/-!
# A radial viscous clock retains the aspect-ratio source

With clock rate b=r²/k, the physical angular reconstruction is k and the radial viscosity
is nu/k. Axial viscosity and the reduced axial pressure force share the factor (r/z)².
These are source identities and admissible chart choices, not a profile or stability theorem.
-/

noncomputable section
open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAnisotropicViscousClock
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
open Soma.Holonics.Millennium.NavierStokesAnisotropicDynamics
open Soma.Holonics.Millennium.NavierStokesLinearFrameSpace
open Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics
open Soma.Holonics.Millennium.NavierStokesRescalingClock
open Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction

def clockRate (k r : ℝ) : ℝ := r ^ 2 / k

def aspect (r z : ℝ) : ℝ := (r / z) ^ 2

theorem clockRate_pos (k r : ℝ) (hk : 0 < k) (hr : r ≠ 0) : 0 < clockRate k r :=
  div_pos (sq_pos_of_ne_zero hr) hk

theorem angular_reconstruction_fixed (k r : ℝ) (hk : k ≠ 0) (hr : r ≠ 0) :
    r ^ 2 / clockRate k r = k := by
  unfold clockRate
  field_simp

theorem viscosities (nu k r z : ℝ) (hk : k ≠ 0) (hr : r ≠ 0) (hz : z ≠ 0) :
    nu * clockRate k r / r ^ 2 = nu / k ∧
      nu * clockRate k r / z ^ 2 = (nu / k) * aspect r z := by
  unfold clockRate aspect
  constructor <;> field_simp <;> ring

theorem clockRate_hasDerivAt (k : ℝ) (r : ℝ → ℝ) (rJet t : ℝ)
    (hr : HasDerivAt r rJet t) (hrne : r t ≠ 0) :
    HasDerivAt (fun τ ↦ clockRate k (r τ)) ((2 * rJet / r t) * clockRate k (r t)) t := by
  have h := (hr.pow 2).div_const k
  convert h using 1 <;> first | rfl |
    (simp only [clockRate, Pi.pow_apply]; field_simp <;> ring)

theorem aspect_hasDerivAt (r z : ℝ → ℝ) (rJet zJet t : ℝ)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t)
    (hrne : r t ≠ 0) (hzne : z t ≠ 0) :
    HasDerivAt (fun τ ↦ aspect (r τ) (z τ))
      (2 * (rJet / r t - zJet / z t) * aspect (r t) (z t)) t := by
  have h := (hr.div hz hzne).pow 2
  convert h using 1 <;> first | rfl |
    (simp only [aspect, Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
     field_simp [hrne, hzne] <;> ring)

/-- The reduced pressure metric retains its axial factor instead of dropping that force. -/
theorem reduced_pressure_metric (r z : ℝ) (hr : r ≠ 0) (hz : z ≠ 0) (v : Space) :
    metricFrame r z (r ^ 2 • v) = diagonalFrame 1 (aspect r z) v := by
  rw [metricFrame_apply, diagonalFrame_apply]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [assemble, aspect] <;> field_simp <;> ring

theorem reduced_pressure_pullback (k r z : ℝ) (hr : r ≠ 0) (hz : z ≠ 0)
    (centre : Space) (p : Space → ℝ) (y : Space)
    (hp : DifferentiableAt ℝ p (centre + diagonalFrame r z y)) :
    metricFrame r z (gradient (pressurePullback (clockRate k r) (diagonalFrame r z) centre p) y) =
      diagonalFrame 1 (aspect r z)
        (gradient (pressurePullback (r / k) (diagonalFrame r z) centre p) y) := by
  rw [gradient_pressurePullback _ _ _ _ _ hp, gradient_pressurePullback _ _ _ _ _ hp]
  have hrate : clockRate k r ^ 2 = r ^ 2 * (r / k) ^ 2 := by
    unfold clockRate
    ring
  rw [hrate, mul_smul, reduced_pressure_metric r z hr hz]

theorem reduced_diffusion (nu k r z : ℝ) (hk : k ≠ 0) (hr : r ≠ 0) (hz : z ≠ 0)
    (radial axial : Space) :
    (nu * clockRate k r) • (r⁻¹ ^ 2 • radial + z⁻¹ ^ 2 • axial) =
      (nu / k) • (radial + aspect r z • axial) := by
  have hc1 : nu * clockRate k r * r⁻¹ ^ 2 = nu / k := by
    unfold clockRate
    field_simp
  have hc2 : nu * clockRate k r * z⁻¹ ^ 2 = (nu / k) * aspect r z := by
    unfold clockRate aspect
    field_simp
  simp only [smul_add, smul_smul, hc1, hc2]

/-- The exact energy weights after choosing this clock, prior to any profile lower bound. -/
theorem reduced_energy_density (k r z : ℝ) (hk : k ≠ 0) (hr : r ≠ 0) (hz : 0 < z) (U : Space) :
    (|r ^ 2 * z| / clockRate k r ^ 2) * kineticMetric r z U =
      k ^ 2 * (z * (U 0 ^ 2 + U 1 ^ 2) + (z ^ 3 / r ^ 2) * U 2 ^ 2) := by
  rw [abs_of_pos (mul_pos (sq_pos_of_ne_zero hr) hz)]
  unfold clockRate kineticMetric
  field_simp <;> ring

/-- The existing physical clock supplies this radial turnover rate and its finite endpoint. -/
theorem exponential_clock_rate (t0 r0 k beta t : ℝ) (hbeta : 0 < beta) :
    HasDerivAt (physicalClock t0 (r0 ^ 2 / k) (2 * beta))
      (clockRate k (exponentialLength r0 beta t)) t := by
  have h := physicalClock_hasDerivAt (t₀ := t0) (B := r0 ^ 2 / k) (k := 2 * beta)
    (s := t) (by positivity)
  have he : Real.exp (-(2 * beta) * t) = Real.exp (-beta * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  convert h using 1
  unfold clockRate exponentialLength
  rw [he]
  ring

/-- The physical solution supplies the reduced anisotropic equation for the chosen radial
clock. The axial pressure force remains multiplied by the aspect factor, not discarded. -/
theorem OpenSmoothSolutionOn.radial_clock_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (r z clock : ℝ → ℝ) (k : ℝ)
    (y : Space) (t : ℝ) (centreJet : Space) (rJet zJet : ℝ)
    (ht : clock t ∈ Ioo 0 T) (hc : HasDerivAt centre centreJet t)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t)
    (hclock : HasDerivAt clock (clockRate k (r t)) t)
    (hk : k ≠ 0) (hrne : r t ≠ 0) (hzne : z t ≠ 0) :
    let A := fun τ ↦ diagonalFrame (r τ) (z τ)
    let B := fun τ ↦ inverseFrame (r τ) (z τ)
    let U := linearFrameVelocity centre A B (fun τ ↦ clockRate k (r τ)) clock velocity
    let Pi := linearFramePressure centre A (fun τ ↦ r τ / k) clock pressure
    deriv (U y) t +
      fderiv ℝ (fun v ↦ U v t) y (U y t - B t (centreJet + diagonalFrame rJet zJet y)) +
      gridRate (r t) (z t) rJet zJet (U y t) - (2 * rJet / r t) • U y t =
        (nu / k) • (radialSecondJet (fun v ↦ U v t) y +
          aspect (r t) (z t) • axialSecondJet (fun v ↦ U v t) y) -
          diagonalFrame 1 (aspect (r t) (z t)) (gradient (fun v ↦ Pi v t) y) +
          clockRate k (r t) ^ 2 • B t (force (centre t + A t y) (clock t)) := by
  dsimp only
  have hrate_ne : clockRate k (r t) ≠ 0 := div_ne_zero (pow_ne_zero 2 hrne) hk
  have h := Soma.Holonics.Millennium.NavierStokesAnisotropicDynamics.OpenSmoothSolutionOn.anisotropic_momentum
    solution centre r z (fun τ ↦ clockRate k (r τ)) clock y t centreJet rJet zJet
    ((2 * rJet / r t) * clockRate k (r t)) ht hc hr hz
    (clockRate_hasDerivAt k r rJet t hr hrne) hclock hrne hzne hrate_ne
  dsimp only at h
  rw [mul_div_cancel_right₀ _ hrate_ne, reduced_diffusion nu k (r t) (z t) hk hrne hzne] at h
  have hp : DifferentiableAt ℝ (fun x ↦ pressure x (clock t))
      (centre t + diagonalFrame (r t) (z t) y) :=
    (Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics.OpenSmoothSolutionOn.pressureSlice_contDiff
      solution ⟨ht.1.le, ht.2⟩).differentiable (by simp) _
  have hpull := reduced_pressure_pullback k (r t) (z t) hrne hzne (centre t)
    (fun x ↦ pressure x (clock t)) y hp
  change metricFrame (r t) (z t)
      (gradient (fun v ↦ linearFramePressure centre (fun τ ↦ diagonalFrame (r τ) (z τ))
        (fun τ ↦ clockRate k (r τ)) clock pressure v t) y) =
    diagonalFrame 1 (aspect (r t) (z t))
      (gradient (fun v ↦ linearFramePressure centre (fun τ ↦ diagonalFrame (r τ) (z τ))
        (fun τ ↦ r τ / k) clock pressure v t) y) at hpull
  rw [hpull] at h
  exact h

#print axioms angular_reconstruction_fixed
#print axioms clockRate_hasDerivAt
#print axioms aspect_hasDerivAt
#print axioms reduced_pressure_pullback
#print axioms reduced_diffusion
#print axioms reduced_energy_density
#print axioms exponential_clock_rate
#print axioms OpenSmoothSolutionOn.radial_clock_momentum
end Soma.Holonics.Millennium.NavierStokesAnisotropicViscousClock
