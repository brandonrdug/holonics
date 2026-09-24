import ElementaryHolonics.Millennium.NavierStokesPeriodicEnergy
import ElementaryHolonics.Millennium.NavierStokesRescalingSpace

/-!
# Periodic pressure rigidity

This owner records the pressure closure used by the moving-frame line.  A smooth one-periodic
pressure cannot have a nonzero constant spatial gradient; the proof composes the periodic
pressure-work cancellation with the constant test velocity and the actual unit-cube volume.
The same result is transported to any fixed nonzero spatial period by the existing rescaling
gradient owner.

Neither result assumes a Navier--Stokes solution, a blowup profile, or a desired terminal
conclusion.  The final velocity consequence only uses the displayed stationary momentum balance.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set Filter
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesPeriodicPressureRigidity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

/-- The actual unit cube has Lebesgue volume one. -/
theorem unitCube_volume_eq_one : volume unitCube = 1 := by
  let eL : Space ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  have he : MeasurePreserving eL volume volume := by
    change MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume
    exact PiLp.volume_preserving_ofLp (Fin 3)
  unfold unitCube
  rw [he.measure_preimage_emb eL.toHomeomorph.measurableEmbedding]
  rw [Real.volume_Icc_pi]
  simp

/-- A smooth one-periodic pressure has no nonzero constant spatial gradient. -/
theorem constant_gradient_eq_zero_of_isOnePeriodic
    (p : Space → ℝ) (hp : ContDiff ℝ 1 p) (hpPeriodic : IsOnePeriodic p)
    (v : Space) (hgradient : ∀ x, gradient p x = v) : v = 0 := by
  let u : InitialVelocity := fun _ ↦ v
  have hu : ContDiff ℝ 1 u := contDiff_const
  have huPeriodic : IsOnePeriodic u := by
    intro x i
    rfl
  have huIncompressible : ∀ x, divergence u x = 0 := by
    intro x
    simp [u, divergence]
  have hwork := integral_pressureWork_unitCube_eq_zero u p hu hp huPeriodic hpPeriodic
    huIncompressible
  have hwork' : (∫ x in unitCube, ‖v‖ ^ 2) = 0 := by
    calc
      (∫ x in unitCube, ‖v‖ ^ 2) =
          ∫ x in unitCube, inner ℝ (gradient p x) (u x) := by
        apply setIntegral_congr_fun
        · exact (by
            unfold unitCube
            exact measurableSet_Icc.preimage
              ((EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding).measurable)
        intro x _hx
        change ‖v‖ ^ 2 = inner ℝ (gradient p x) (u x)
        rw [hgradient x]
        simp [u]
      _ = 0 := hwork
  have hcube : volume unitCube = 1 := unitCube_volume_eq_one
  have hnorm : ‖v‖ ^ 2 = 0 := by
    simp [integral_const, Measure.real, hcube] at hwork'
    simpa using hwork'
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- The same pressure rigidity for any fixed nonzero spatial period.  Rescaling the pressure
argument by that period composes the generic statement with the unit-period integration owner. -/
theorem constant_gradient_eq_zero_of_periodic
    (p : Space → ℝ) (hp : ContDiff ℝ 1 p) (period : ℝ) (hperiod : period ≠ 0)
    (hperiodic : ∀ y i, p (y + period • EuclideanSpace.single i 1) = p y)
    (v : Space) (hgradient : ∀ x, gradient p x = v) : v = 0 := by
  let q : Space → ℝ := fun y ↦ p (period • y)
  have hqdef : q = NavierStokesRescalingSpace.spatialPullback 1 period 0 p := by
    funext y
    simp [q, NavierStokesRescalingSpace.spatialPullback]
  have hq : ContDiff ℝ 1 q := by
    exact hp.comp (contDiff_const_smul period)
  have hqPeriodic : IsOnePeriodic q := by
    intro y i
    unfold q
    have harg : period • (y + EuclideanSpace.single i 1) =
        period • y + period • EuclideanSpace.single i 1 := by
      rw [smul_add]
    rw [harg, hperiodic]
  have hqGradient : ∀ y, gradient q y = period • v := by
    intro y
    have h := NavierStokesRescalingSpace.gradient_spatialPullback 1 period 0 p y
    rw [hqdef]
    simpa [hgradient] using h
  have hscaled := constant_gradient_eq_zero_of_isOnePeriodic q hq hqPeriodic
    (period • v) hqGradient
  exact (smul_eq_zero.mp hscaled).resolve_left hperiod

/-! ## The constant-velocity stationary pressure closure -/

/-- In a stationary rescaled momentum balance `0 = -∇P + c • U`, a nonzero scalar `c` and
periodic smooth pressure force the constant spatial velocity `U` to vanish. -/
theorem constant_velocity_eq_zero_of_stationary_pressure_balance
    (pressure : Space → ℝ) (U : Space) (c : ℝ)
    (hpressureSmooth : ContDiff ℝ 1 pressure)
    (hpressurePeriodic : IsOnePeriodic pressure)
    (hc : c ≠ 0)
    (hbalance : ∀ x, (0 : Space) = -gradient pressure x + c • U) :
    U = 0 := by
  have hgradient : ∀ x, gradient pressure x = c • U := by
    intro x
    have h := hbalance x
    have hn := congrArg Neg.neg (eq_neg_of_add_eq_zero_left h.symm)
    simpa using hn
  have hcu : c • U = 0 := constant_gradient_eq_zero_of_isOnePeriodic pressure
    hpressureSmooth hpressurePeriodic (c • U) hgradient
  exact (smul_eq_zero.mp hcu).resolve_left hc

#print axioms unitCube_volume_eq_one
#print axioms constant_gradient_eq_zero_of_isOnePeriodic
#print axioms constant_velocity_eq_zero_of_stationary_pressure_balance

end Soma.Holonics.Millennium.NavierStokesPeriodicPressureRigidity
