import ElementaryHolonics.Millennium.NavierStokesCompactAngularObstruction
import ElementaryHolonics.Millennium.NavierStokesMovingPeriodicCore
import ElementaryHolonics.Millennium.NavierStokesRescalingPeriodObstruction

/-!
# The actual exponentially rescaled periodic cutoff retains a positive residual

The scale, reciprocal velocity normalizer and viscosity are the MFR1 exponential functions.
The physical potential is periodized before the normalized field is read. The local residual
identity transfers the compact angular obstruction to this actual moving periodic family.
Pressure remains an arbitrary smooth Cartesian field, so solving its periodic Poisson equation
cannot evade the returned lower bound.
-/

noncomputable section
open ContDiff Set Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesCompactPeriodicObstruction
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
open Soma.Holonics.Millennium.NavierStokesExteriorTorque
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
open Soma.Holonics.Millennium.NavierStokesRadialCoreCutoff
open Soma.Holonics.Millennium.NavierStokesAffineAngularResidual
open Soma.Holonics.Millennium.NavierStokesCompactAngularObstruction
open Soma.Holonics.Millennium.NavierStokesMovingPeriodicCore
open Soma.Holonics.Millennium.NavierStokesRescalingPeriodObstruction

theorem exponentialLength_tendsto_zero (initial rate : ℝ) (hrate : 0 < rate) :
    Tendsto (exponentialLength initial rate) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hrate)
  unfold exponentialLength
  simpa [Function.comp_def, neg_mul] using he.const_mul initial

theorem exponential_core_domain (ell0 q0 : ℝ) (hell : 0 < ell0) (hell1 : ell0 < 1)
    (hq : 0 < q0) : ∀ t : ℝ, 0 < t →
      0 < exponentialLength ell0 1 t ∧ exponentialLength ell0 1 t < 1 ∧
        exponentialLength q0 (3 / 2) t ≠ 0 := by
  intro t ht
  have he : Real.exp (-(1 : ℝ) * t) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  refine ⟨mul_pos hell (Real.exp_pos _), ?_, (mul_pos hq (Real.exp_pos _)).ne'⟩
  exact (mul_le_of_le_one_right hell.le he).trans_lt hell1

/-- The supplied viscosity is exactly nu*q/ell, rather than an independent small knob. -/
theorem exponential_viscosity_ratio (nu ell0 q0 t : ℝ) (hell : ell0 ≠ 0) :
    nu * exponentialLength q0 (3 / 2) t / exponentialLength ell0 1 t =
      exponentialLength (nu * q0 / ell0) (1 / 2) t := by
  unfold exponentialLength
  have hexp : Real.exp (-((3 : ℝ) / 2) * t) =
      Real.exp (-(1 : ℝ) * t) * Real.exp (-((1 : ℝ) / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp [Real.exp_ne_zero, hell]

/-- At every sufficiently late normalized time, the full periodic candidate has an angular
momentum residual exceeding radius²/4 somewhere in the normalized radius-1/4 ball. The two
retained free coefficients may be any fixed finite values satisfying the displayed seed. -/
theorem periodic_finite_core_eventually_positive_residual
    (h0 g0 h1 g1 : MeridionalProfile)
    (hh0 : ContDiff ℝ ∞ h0) (hg0 : ContDiff ℝ ∞ g0)
    (hh1 : ContDiff ℝ ∞ h1) (hg1 : ContDiff ℝ ∞ g1)
    (radius : ℝ)
    (hseed : radius ^ 2 < angularField (coreCurl (cutPotential h0 g0)) (assemble radius 0 0))
    (nu ell0 q0 : ℝ) (hnu : 0 < nu) (hell : 0 < ell0) (hell1 : ell0 < 1) (hq : 0 < q0) :
    ∀ᶠ t : ℝ in atTop, ∀ (P : ℝ → Space → ℝ), ContDiff ℝ 1 (P t) →
      ∃ y : Space, ‖y‖ ≤ 1 / 4 ∧ radius ^ 2 / 4 < cartesianAngularMomentum y
        (momentumResidual
          (movingNormalizedVelocity (exponentialLength ell0 1) (exponentialLength q0 (3 / 2))
            (exponentialLength (nu * q0 / ell0) (1 / 2)) (cutPotential h0 g0) (cutPotential h1 g1))
          P (fun _ ↦ 3 / 2) (fun _ ↦ 1) (exponentialLength (nu * q0 / ell0) (1 / 2)) t y) := by
  obtain ⟨epsilon, heps, hbound⟩ := finite_core_cutoff_residual_lower_bound
    h0 g0 h1 g1 hh0 hg0 hh1 hg1 radius hseed
  let mu := exponentialLength (nu * q0 / ell0) (1 / 2)
  have hmu0 : 0 < nu * q0 / ell0 := div_pos (mul_pos hnu hq) hell
  have htend : Tendsto mu atTop (𝓝 0) :=
    exponentialLength_tendsto_zero _ _ (by norm_num)
  have hsmall : ∀ᶠ t : ℝ in atTop, mu t < epsilon := htend.eventually (gt_mem_nhds heps)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with t hmusmall ht
  intro P hP
  have hmu : HasDerivAt mu (-mu t / 2) t := by
    convert exponentialLength_hasDerivAt (nu * q0 / ell0) (1 / 2) t using 1 <;> ring
  have hmupos : 0 ≤ mu t := (mul_pos hmu0 (Real.exp_pos _)).le
  obtain ⟨y, hy, hres⟩ := hbound mu t P hmu hmupos hmusmall.le hP
  refine ⟨y, hy, ?_⟩
  rw [movingNormalizedVelocity_momentumResidual_eq_affine
    (exponentialLength ell0 1) (exponentialLength q0 (3 / 2)) mu
    (cutPotential h0 g0) (cutPotential h1 g1) P (fun _ ↦ 3 / 2) (fun _ ↦ 1)
    (cutPotential_support h0 g0) (cutPotential_support h1 g1)
    (exponential_core_domain ell0 q0 hell hell1 hq)
    (cutPotential_contDiff h0 g0 hh0 hg0) (cutPotential_contDiff h1 g1 hh1 hg1) ht
    (by linarith : ‖y‖ < 1 / 2)]
  exact hres

#print axioms exponential_viscosity_ratio
#print axioms periodic_finite_core_eventually_positive_residual
end Soma.Holonics.Millennium.NavierStokesCompactPeriodicObstruction
