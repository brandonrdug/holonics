import ElementaryHolonics.Millennium.NavierStokesPeriodicCore
import ElementaryHolonics.Millennium.NavierStokesExteriorTorque
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# An explicit radial cutoff of the finite core

The cutoff is a specified smooth function of squared distance. Rotational symmetry is supplied
by this formula, rather than inferred from the weaker contract of a generic bump function.
Cutting off the potential includes all annular derivatives in the resulting velocity.
-/

noncomputable section
open ContDiff Set Function
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesRadialCoreCutoff
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
open Soma.Holonics.Millennium.NavierStokesPeriodicCore
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesExteriorTorque

/-- Inner radius 1/8, outer radius 1/4 in the normalized spatial chart. -/
def radialCutoff (p : ℝ × ℝ) : ℝ :=
  Real.smoothTransition ((4 - 64 * (p.1 + p.2 ^ 2)) / 3)

theorem radialCutoff_contDiff : ContDiff ℝ ∞ radialCutoff := by
  unfold radialCutoff
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem radialCutoff_eq_one {p : ℝ × ℝ} (hp : p.1 + p.2 ^ 2 ≤ 1 / 64) :
    radialCutoff p = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem radialCutoff_eq_zero {p : ℝ × ℝ} (hp : 1 / 16 ≤ p.1 + p.2 ^ 2) :
    radialCutoff p = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem norm_sq_eq_meridional (x : Space) :
    ‖x‖ ^ 2 = (meridionalChart x).1 + (meridionalChart x).2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, meridionalChart]
  ring

def cutH (h : MeridionalProfile) : MeridionalProfile := fun p ↦ radialCutoff p * h p

def cutPotential (h g : MeridionalProfile) : InitialVelocity :=
  meridionalVectorPotential (cutH h) (cutH g)

theorem cutH_contDiff (h : MeridionalProfile) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (cutH h) := radialCutoff_contDiff.mul hh

theorem cutPotential_contDiff (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cutPotential h g) :=
  meridionalVectorPotential_contDiff _ _ (cutH_contDiff h hh) (cutH_contDiff g hg)

theorem cutPotential_eq_zero (h g : MeridionalProfile) (x : Space)
    (hx : 1 / 4 ≤ ‖x‖) : cutPotential h g x = 0 := by
  have hs : 1 / 16 ≤ (meridionalChart x).1 + (meridionalChart x).2 ^ 2 := by
    rw [← norm_sq_eq_meridional]
    nlinarith [norm_nonneg x]
  simp [cutPotential, meridionalVectorPotential, axisymmetricVelocity, cutH,
    radialCutoff_eq_zero hs, assemble]

theorem cutPotential_support (h g : MeridionalProfile) :
    support (cutPotential h g) ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  intro x hx
  by_contra hnot
  have hn : 1 / 4 < ‖x‖ := by simpa using hnot
  exact hx (cutPotential_eq_zero h g x hn.le)

theorem cutPotential_tsupport (h g : MeridionalProfile) :
    tsupport (cutPotential h g) ⊆ Metric.closedBall (0 : Space) (1 / 4) :=
  closure_minimal (cutPotential_support h g) Metric.isClosed_closedBall

theorem cutPotential_hasCompactSupport (h g : MeridionalProfile) :
    HasCompactSupport (cutPotential h g) :=
  (isCompact_closedBall (0 : Space) (1 / 4)).of_isClosed_subset
    (isClosed_tsupport _) (cutPotential_tsupport h g)

def cutV (h : MeridionalProfile) : MeridionalProfile := fun p ↦ -axialDerivative (cutH h) p

def cutOmega (g : MeridionalProfile) : MeridionalProfile :=
  fun p ↦ -2 * radialDerivative (cutH g) p

theorem cutH_eventuallyEq_inner (h : MeridionalProfile) (p : ℝ × ℝ)
    (hp : p.1 + p.2 ^ 2 < 1 / 64) : cutH h =ᶠ[𝓝 p] h := by
  have hc : Continuous (fun q : ℝ × ℝ ↦ q.1 + q.2 ^ 2) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hp)] with q hq
  simp [cutH, radialCutoff_eq_one hq.le]

theorem cutOmega_eq_inner (g : MeridionalProfile) (p : ℝ × ℝ)
    (hp : p.1 + p.2 ^ 2 < 1 / 64) : cutOmega g p = -2 * radialDerivative g p := by
  unfold cutOmega radialDerivative
  rw [(cutH_eventuallyEq_inner g p hp).fderiv_eq]

def cutW (h : MeridionalProfile) : MeridionalProfile :=
  fun p ↦ 2 * cutH h p + 2 * p.1 * radialDerivative (cutH h) p

theorem cutOmega_contDiff (g : MeridionalProfile) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cutOmega g) := by
  have hd := (cutH_contDiff g hg).fderiv_right (m := ∞) (by simp)
  exact contDiff_const.mul (hd.clm_apply contDiff_const)

/-- The actual curl includes the derivatives of the cutoff in every coefficient. -/
theorem cutPotential_curl (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    coreCurl (cutPotential h g) = axisymmetricVelocity (cutV h) (cutOmega g) (cutW h) := by
  funext x
  exact vorticity_meridionalVectorPotential (cutH h) (cutH g)
    ((cutH_contDiff h hh).of_le (WithTop.coe_le_coe.mpr le_top))
    ((cutH_contDiff g hg).of_le (WithTop.coe_le_coe.mpr le_top)) x

theorem coreCurl_hasCompactSupport (A : InitialVelocity) (hA : HasCompactSupport A) :
    HasCompactSupport (coreCurl A) := by
  have h := (hA.fderiv ℝ).comp_left (map_zero derivativeCurlLinearMap)
  exact h

theorem angularField_hasCompactSupport (u : InitialVelocity) (hu : HasCompactSupport u) :
    HasCompactSupport (angularField u) := by
  have h0 := hu.comp_left (show (coordinateProjection 0) (0 : Space) = 0 from map_zero _)
  have h1 := hu.comp_left (show (coordinateProjection 1) (0 : Space) = 0 from map_zero _)
  exact h1.mul_left.sub h0.mul_left

theorem cutVelocity_angular_support (h g : MeridionalProfile) :
    support (angularField (coreCurl (cutPotential h g))) ⊆
      Metric.closedBall (0 : Space) (1 / 4) := by
  intro x hx
  have hts : x ∈ tsupport (cutPotential h g) := by
    by_contra hnot
    have hd := fderiv_of_notMem_tsupport ℝ hnot
    apply hx
    simp [angularField, NavierStokesViscousSwirlBalance.cartesianAngularMomentum,
      coreCurl, vorticityAt, velocityJacobianAt, hd, jacobianMatrix, curlFromJacobian,
      vectorOfCoordinates]
  exact cutPotential_tsupport h g hts

/-- The compactness used in the maximum argument belongs to the actual cut Cartesian field. -/
theorem cutAngular_hasCompactSupport (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    HasCompactSupport (fun x ↦ NavierStokesSwirlCirculation.angularMomentum (cutOmega g)
      (meridionalChart x)) := by
  have hc := angularField_hasCompactSupport (coreCurl (cutPotential h g))
    (coreCurl_hasCompactSupport _ (cutPotential_hasCompactSupport h g))
  rw [cutPotential_curl h g hh hg] at hc
  have heq : angularField (axisymmetricVelocity (cutV h) (cutOmega g) (cutW h)) =
      (fun x ↦ NavierStokesSwirlCirculation.angularMomentum (cutOmega g) (meridionalChart x)) := by
    funext x
    simp [angularField, NavierStokesViscousSwirlBalance.cartesianAngularMomentum,
      axisymmetricVelocity, NavierStokesSwirlCirculation.angularMomentum, meridionalChart]
    ring
  rw [heq] at hc
  exact hc

def periodicCutVelocity (h g : MeridionalProfile) : InitialVelocity :=
  coreCurl (periodize (cutPotential h g))

theorem periodicCutVelocity_initial_condition (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    InitialVelocityConditionPeriodic (periodicCutVelocity h g) := by
  have hs := periodize_contDiff _ (cutPotential_contDiff h g hh hg)
    (by norm_num : (1 : ℝ) / 4 < 1 / 2) (cutPotential_support h g)
  exact { divergenceFree := divergence_coreCurl_eq_zero _ (hs.of_le (WithTop.coe_le_coe.mpr le_top)),
          smooth := coreCurl_contDiff _ hs,
          periodic := coreCurl_isOnePeriodic _ (fun x i ↦ periodize_periodic _ i x) }

theorem periodicCutVelocity_eq_local (h g : MeridionalProfile) {x : Space}
    (hx : ‖x‖ < 3 / 4) : periodicCutVelocity h g x = coreCurl (cutPotential h g) x := by
  have heq : periodize (cutPotential h g) =ᶠ[𝓝 x] cutPotential h g := by
    have hx' : x ∈ Metric.ball (0 : Space) (1 - (1 : ℝ) / 4) := by
      simpa only [Metric.mem_ball, dist_zero_right, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] using hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    exact periodize_eq_core_of_mem_ball (cutPotential_support h g) hy
  unfold periodicCutVelocity coreCurl vorticityAt velocityJacobianAt
  rw [heq.fderiv_eq]

#print axioms cutPotential_curl
#print axioms cutAngular_hasCompactSupport
#print axioms periodicCutVelocity_initial_condition
#print axioms periodicCutVelocity_eq_local
end Soma.Holonics.Millennium.NavierStokesRadialCoreCutoff
