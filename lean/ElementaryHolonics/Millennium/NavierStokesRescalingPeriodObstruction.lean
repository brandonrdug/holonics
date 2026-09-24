import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling

/-!
# An expanding periodic chart cannot carry one nonconstant global stationary profile

A fixed global profile inheriting every sufficiently large coordinate period must be constant:
the difference of two admitted periods returns any coordinate displacement. The theorem uses
the actual period transported by `OpenPeriodicSolutionOn.rescaled_velocity_period`.

It excludes a global stationary rescaled ansatz on the unit torus with the stated period range.
It does not exclude local convergence on an expanding cell, modulated profiles or discrete
scale families whose periods do not fill a ray.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling

/-- Two large periods retain their joining equality and return any signed coordinate step. -/
theorem coordinate_translation_eq_of_period_ray
    {E : Type*} (profile : Space → E) (p₀ : ℝ)
    (hperiod : ∀ p : ℝ, p₀ ≤ p → ∀ y i,
      profile (y + p • EuclideanSpace.single i 1) = profile y)
    (y : Space) (i : Fin 3) (step : ℝ) :
    profile (y + step • EuclideanSpace.single i 1) = profile y := by
  let p : ℝ := max p₀ (p₀ - step)
  have hp : p₀ ≤ p := le_max_left _ _
  have hpstep : p₀ ≤ p + step := by
    have h := le_max_right p₀ (p₀ - step)
    dsimp [p]
    linarith
  have hfirst := hperiod p hp (y - p • EuclideanSpace.single i 1) i
  have hsecond := hperiod (p + step) hpstep (y - p • EuclideanSpace.single i 1) i
  rw [show y - p • EuclideanSpace.single i 1 + p • EuclideanSpace.single i 1 = y by module]
    at hfirst
  rw [show y - p • EuclideanSpace.single i 1 + (p + step) • EuclideanSpace.single i 1 =
    y + step • EuclideanSpace.single i 1 by module] at hsecond
  exact hsecond.trans hfirst.symm

/-- A full ray of periods in each source coordinate forces the global profile to be constant.
No continuity assumption is needed for this exact algebraic consequence. -/
theorem constant_of_coordinate_period_ray
    {E : Type*} (profile : Space → E) (p₀ : ℝ)
    (hperiod : ∀ p : ℝ, p₀ ≤ p → ∀ y i,
      profile (y + p • EuclideanSpace.single i 1) = profile y) :
    ∀ y, profile y = profile 0 := by
  intro y
  have h := coordinate_translation_eq_of_period_ray profile p₀ hperiod
  have hy : ((0 : Space) + y 0 • EuclideanSpace.single 0 1) +
      y 1 • EuclideanSpace.single 1 1 + y 2 • EuclideanSpace.single 2 1 = y := by
    ext i
    fin_cases i <;> simp
  rw [← hy]
  rw [h, h, h]

/-- The period of one global stationary profile is read from the actual periodic source.
The period-range hypothesis will be constructed for an exponential scale below. -/
theorem OpenPeriodicSolutionOn.stationaryProfile_constant_of_period_range
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (profile : Space → Space) (p₀ : ℝ)
    (hprofile : ∀ s : ℝ, 0 ≤ s → ∀ y,
      rescaledVelocity centre length amplitude clock velocity y s = profile y)
    (hinside : ∀ s : ℝ, 0 ≤ s → clock s ∈ openTimeSlab T)
    (hrange : ∀ p : ℝ, p₀ ≤ p → ∃ s : ℝ, 0 ≤ s ∧ length s ≠ 0 ∧ (length s)⁻¹ = p) :
    ∀ y, profile y = profile 0 := by
  apply constant_of_coordinate_period_ray profile p₀
  intro p hp y i
  obtain ⟨s, hs, hlength, hperiod⟩ := hrange p hp
  have h :=
    Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenPeriodicSolutionOn.rescaled_velocity_period
      solution centre length amplitude clock s (hinside s hs) hlength y i
  simpa only [hperiod, hprofile s hs] using h

def exponentialLength (ell₀ beta s : ℝ) : ℝ := ell₀ * Real.exp (-beta * s)

theorem exponentialLength_hasDerivAt (ell₀ beta s : ℝ) :
    HasDerivAt (exponentialLength ell₀ beta) (-beta * exponentialLength ell₀ beta s) s := by
  have h := ((hasDerivAt_const_mul (-beta) (x := s)).exp).const_mul ell₀
  change HasDerivAt (fun y : ℝ ↦ ell₀ * Real.exp (-beta * y))
    (-beta * (ell₀ * Real.exp (-beta * s))) s
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The reciprocal lengths of a shrinking exponential chart fill the complete period ray. -/
theorem exponentialLength_period_range {ell₀ beta : ℝ} (hell₀ : 0 < ell₀) (hbeta : 0 < beta) :
    ∀ p : ℝ, ell₀⁻¹ ≤ p →
      ∃ s : ℝ, 0 ≤ s ∧ exponentialLength ell₀ beta s ≠ 0 ∧
        (exponentialLength ell₀ beta s)⁻¹ = p := by
  intro p hp
  have hprod : 1 ≤ ell₀ * p := by
    have h := mul_le_mul_of_nonneg_left hp hell₀.le
    rwa [mul_inv_cancel₀ hell₀.ne'] at h
  have hprodpos : 0 < ell₀ * p := zero_lt_one.trans_le hprod
  let s : ℝ := Real.log (ell₀ * p) / beta
  have hs : 0 ≤ s := div_nonneg (Real.log_nonneg hprod) hbeta.le
  have he : Real.exp (-beta * s) = (ell₀ * p)⁻¹ := by
    rw [show -beta * s = -Real.log (ell₀ * p) by dsimp [s]; field_simp]
    rw [Real.exp_neg, Real.exp_log hprodpos]
  refine ⟨s, hs, mul_ne_zero hell₀.ne' (Real.exp_ne_zero _), ?_⟩
  unfold exponentialLength
  rw [he, mul_inv_rev, inv_inv]
  field_simp

/-- A global stationary profile of an exponentially shrinking periodic chart is constant. -/
theorem OpenPeriodicSolutionOn.stationaryProfile_constant_exponential
    {T nu ell₀ beta : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hell₀ : 0 < ell₀) (hbeta : 0 < beta)
    (centre : ℝ → Space) (amplitude clock : ℝ → ℝ) (profile : Space → Space)
    (hprofile : ∀ s : ℝ, 0 ≤ s → ∀ y,
      rescaledVelocity centre (exponentialLength ell₀ beta) amplitude clock velocity y s = profile y)
    (hinside : ∀ s : ℝ, 0 ≤ s → clock s ∈ openTimeSlab T) :
    ∀ y, profile y = profile 0 :=
  OpenPeriodicSolutionOn.stationaryProfile_constant_of_period_range solution centre
    (exponentialLength ell₀ beta) amplitude clock profile ell₀⁻¹ hprofile hinside
      (exponentialLength_period_range hell₀ hbeta)

#print axioms constant_of_coordinate_period_ray
#print axioms exponentialLength_period_range
#print axioms OpenPeriodicSolutionOn.stationaryProfile_constant_exponential

end Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction
