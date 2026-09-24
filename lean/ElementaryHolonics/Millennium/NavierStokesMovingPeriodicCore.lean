import ElementaryHolonics.Millennium.NavierStokesRadialCoreCutoff
import ElementaryHolonics.Millennium.NavierStokesAffineAngularResidual

/-!
# A moving periodic realization of the compact core

The physical potential is first rescaled and then periodized.  Its physical curl is unit-periodic;
after evaluation at `ell • y`, the normalized field has period `ell⁻¹` in each coordinate.  On the
inner normalized ball the periodic curl agrees exactly with the original compact-core curl, so the
normalized field retains the local Cartesian source.
-/

noncomputable section

open ContDiff Set Function Filter Metric
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesMovingPeriodicCore

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
open Soma.Holonics.Millennium.NavierStokesPeriodicCore
open Soma.Holonics.Millennium.NavierStokesVorticity

open Soma.Holonics.Millennium.NavierStokesAffineAngularResidual
open Soma.Holonics.Millennium.NavierStokesExteriorTorque

/-- The normalized periodic curl, evaluated on the normalized spatial chart. -/
def normalizedPeriodicVelocity (ell q : ℝ) (A : InitialVelocity) : InitialVelocity :=
  fun y ↦ q • coreCurl (periodize (physicalPotential ell q A)) (ell • y)

/-- An affine combination of two potential fields. -/
def affinePotential (A0 A1 : InitialVelocity) (mu : ℝ) : InitialVelocity :=
  fun y ↦ A0 y + mu • A1 y

/-- A time-dependent normalized periodic realization of an affine potential family. -/
def movingNormalizedVelocity
    (ell q mu : ℝ → ℝ) (A0 A1 : InitialVelocity) (t : ℝ) : InitialVelocity :=
  normalizedPeriodicVelocity (ell t) (q t) (affinePotential A0 A1 (mu t))

theorem physicalPotential_curl_isOnePeriodic (ell q : ℝ) (A : InitialVelocity) :
    IsOnePeriodic (coreCurl (periodize (physicalPotential ell q A))) :=
  coreCurl_isOnePeriodic _ (fun x i ↦ periodize_periodic _ i x)

theorem normalizedPeriodicVelocity_period
    (ell q : ℝ) (A : InitialVelocity) (hell : ell ≠ 0) (i : Fin 3) :
    Function.Periodic (normalizedPeriodicVelocity ell q A)
      (ell⁻¹ • EuclideanSpace.single i (1 : ℝ)) := by
  intro y
  change q • coreCurl (periodize (physicalPotential ell q A))
      (ell • (y + ell⁻¹ • EuclideanSpace.single i (1 : ℝ))) =
    q • coreCurl (periodize (physicalPotential ell q A)) (ell • y)
  have hperiod := physicalPotential_curl_isOnePeriodic ell q A (ell • y) i
  have hstep : ell • (ell⁻¹ • EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single i (1 : ℝ) := by
    rw [smul_smul, mul_inv_cancel₀ hell, one_smul]
  rw [smul_add, hstep, hperiod]

theorem physicalPotential_support_subset
    (ell q : ℝ) (A : InitialVelocity)
    (hA : support A ⊆ closedBall (0 : Space) (1 / 4)) (hell : 0 < ell) :
    support (physicalPotential ell q A) ⊆ closedBall (0 : Space) (ell / 4) := by
  intro x hx
  have hApre : A (ell⁻¹ • x) ≠ 0 := by
    intro hzero
    apply hx
    simp [physicalPotential, NavierStokesCoreVectorPotential.physicalPotential,
      NavierStokesRescalingSpace.spatialPullback, hzero]
  have hpre : ell⁻¹ • x ∈ closedBall (0 : Space) (1 / 4) := hA (mem_support.mpr hApre)
  have hpre_norm : ‖ell⁻¹ • x‖ ≤ 1 / 4 := by
    simpa [mem_closedBall, dist_zero_right] using hpre
  have hellne : ell ≠ 0 := ne_of_gt hell
  have hxidentity : x = ell • (ell⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ hellne, one_smul]
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = ‖ell • (ell⁻¹ • x)‖ := congrArg norm hxidentity
    _ = ell * ‖ell⁻¹ • x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hell]
    _ ≤ ell * (1 / 4) := mul_le_mul_of_nonneg_left hpre_norm (le_of_lt hell)
    _ = ell / 4 := by ring

theorem normalizedPeriodicVelocity_eq_coreCurl_of_mem_ball
    (ell q : ℝ) (A : InitialVelocity)
    (hA : support A ⊆ closedBall (0 : Space) (1 / 4))
    (hell : 0 < ell) (hell_lt_one : ell < 1) (hq : q ≠ 0) {y : Space}
    (hy : ‖y‖ < 1 / 2) :
    normalizedPeriodicVelocity ell q A y = coreCurl A y := by
  have hellne : ell ≠ 0 := ne_of_gt hell
  have hphys : support (physicalPotential ell q A) ⊆
      closedBall (0 : Space) (ell / 4) :=
    physicalPotential_support_subset ell q A hA hell
  have hxnorm : ‖ell • y‖ < 1 - ell / 4 := by
    calc
      ‖ell • y‖ = ell * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hell]
      _ < ell * (1 / 2) := mul_lt_mul_of_pos_left hy hell
      _ < 1 / 2 := by nlinarith [hell_lt_one]
      _ < 1 - ell / 4 := by nlinarith [hell_lt_one]
  have hxball : ell • y ∈ ball (0 : Space) (1 - ell / 4) := by
    simpa [mem_ball, dist_zero_right] using hxnorm
  have heq : periodize (physicalPotential ell q A) =ᶠ[𝓝 (ell • y)]
      physicalPotential ell q A := by
    filter_upwards [isOpen_ball.mem_nhds hxball] with x hx
    exact periodize_eq_core_of_mem_ball hphys hx
  have hcurl : coreCurl (periodize (physicalPotential ell q A)) (ell • y) =
      coreCurl (physicalPotential ell q A) (ell • y) := by
    unfold coreCurl vorticityAt velocityJacobianAt
    rw [heq.fderiv_eq]
  rw [normalizedPeriodicVelocity, hcurl]
  change q • coreCurl
      (NavierStokesCoreVectorPotential.physicalPotential ell q A) (ell • y) = coreCurl A y
  rw [NavierStokesCoreVectorPotential.coreCurl_physicalPotential ell q A hellne]
  simp [smul_smul, hellne, hq]

theorem coreCurl_add_const_smul
    (A0 A1 : InitialVelocity) (mu : ℝ)
    (hA0 : ContDiff ℝ 1 A0) (hA1 : ContDiff ℝ 1 A1) (x : Space) :
    coreCurl (fun y ↦ A0 y + mu • A1 y) x =
      coreCurl A0 x + mu • coreCurl A1 x := by
  change derivativeCurlLinearMap
      (fderiv ℝ (fun y ↦ A0 y + mu • A1 y) x) = _
  have hA0' : DifferentiableAt ℝ A0 x := hA0.differentiable (by norm_num) x
  have hA1' : DifferentiableAt ℝ A1 x := hA1.differentiable (by norm_num) x
  have hsum : (fun y ↦ A0 y + mu • A1 y) = A0 + mu • A1 := rfl
  rw [hsum, fderiv_add hA0' (hA1'.const_smul mu),
    congrFun (fderiv_const_smul_field mu) x]
  simp only [Pi.smul_apply]
  rw [map_add, map_smul]
  rfl

theorem affinePotential_support_subset
    (A0 A1 : InitialVelocity) (mu : ℝ)
    (hA0 : support A0 ⊆ closedBall (0 : Space) (1 / 4))
    (hA1 : support A1 ⊆ closedBall (0 : Space) (1 / 4)) :
    support (affinePotential A0 A1 mu) ⊆ closedBall (0 : Space) (1 / 4) := by
  intro x hx
  by_contra hnot
  have hx0 : x ∉ support A0 := fun hx0 ↦ hnot (hA0 hx0)
  have hx1 : x ∉ support A1 := fun hx1 ↦ hnot (hA1 hx1)
  have hzero0 : A0 x = 0 := notMem_support.mp hx0
  have hzero1 : A1 x = 0 := notMem_support.mp hx1
  exact hx (by simp [affinePotential, hzero0, hzero1])

theorem normalizedPeriodicVelocity_affine_eq
    (ell q mu : ℝ) (A0 A1 : InitialVelocity)
    (hA0support : support A0 ⊆ closedBall (0 : Space) (1 / 4))
    (hA1support : support A1 ⊆ closedBall (0 : Space) (1 / 4))
    (hell : 0 < ell) (hell_lt_one : ell < 1) (hq : q ≠ 0)
    (hA0 : ContDiff ℝ 1 A0) (hA1 : ContDiff ℝ 1 A1)
    {y : Space} (hy : ‖y‖ < 1 / 2) :
    normalizedPeriodicVelocity ell q (affinePotential A0 A1 mu) y =
      affineVelocity (coreCurl A0) (coreCurl A1) (fun _ ↦ mu) 0 y := by
  have hsupport : support (affinePotential A0 A1 mu) ⊆
      closedBall (0 : Space) (1 / 4) :=
    affinePotential_support_subset A0 A1 mu hA0support hA1support
  rw [normalizedPeriodicVelocity_eq_coreCurl_of_mem_ball ell q
    (affinePotential A0 A1 mu) hsupport hell hell_lt_one hq hy]
  change coreCurl (fun y ↦ A0 y + mu • A1 y) y = _
  rw [coreCurl_add_const_smul A0 A1 mu hA0 hA1 y]
  rfl

theorem movingNormalizedVelocity_eq_affineVelocity_of_pos
    (ell q mu : ℝ → ℝ) (A0 A1 : InitialVelocity)
    (hA0support : support A0 ⊆ closedBall (0 : Space) (1 / 4))
    (hA1support : support A1 ⊆ closedBall (0 : Space) (1 / 4))
    (hpos : ∀ τ, 0 < τ → 0 < ell τ ∧ ell τ < 1 ∧ q τ ≠ 0)
    (hA0 : ContDiff ℝ ∞ A0) (hA1 : ContDiff ℝ ∞ A1)
    {t : ℝ} (ht : 0 < t) {y : Space} (hy : ‖y‖ < 1 / 2) :
    movingNormalizedVelocity ell q mu A0 A1 t y =
      affineVelocity (coreCurl A0) (coreCurl A1) mu t y := by
  obtain ⟨hell, hell_lt_one, hq⟩ := hpos t ht
  simpa [movingNormalizedVelocity, affineVelocity, affinePotential] using
    (normalizedPeriodicVelocity_affine_eq (ell t) (q t) (mu t) A0 A1
      hA0support hA1support hell hell_lt_one hq
      (hA0.of_le (by norm_num)) (hA1.of_le (by norm_num)) hy)

theorem movingNormalizedVelocity_momentumResidual_eq_affine
    (ell q mu : ℝ → ℝ) (A0 A1 : InitialVelocity)
    (P : ℝ → Space → ℝ) (alpha beta : ℝ → ℝ)
    (hA0support : support A0 ⊆ closedBall (0 : Space) (1 / 4))
    (hA1support : support A1 ⊆ closedBall (0 : Space) (1 / 4))
    (hpos : ∀ τ, 0 < τ → 0 < ell τ ∧ ell τ < 1 ∧ q τ ≠ 0)
    (hA0 : ContDiff ℝ ∞ A0) (hA1 : ContDiff ℝ ∞ A1)
    {t : ℝ} (ht : 0 < t) {y : Space} (hy : ‖y‖ < 1 / 2) :
    momentumResidual (movingNormalizedVelocity ell q mu A0 A1) P alpha beta mu t y =
      momentumResidual (affineVelocity (coreCurl A0) (coreCurl A1) mu)
        P alpha beta mu t y := by
  have hlocal : ∀ τ, 0 < τ →
      movingNormalizedVelocity ell q mu A0 A1 τ y =
        affineVelocity (coreCurl A0) (coreCurl A1) mu τ y := by
    intro τ hτ
    exact movingNormalizedVelocity_eq_affineVelocity_of_pos ell q mu A0 A1
      hA0support hA1support hpos hA0 hA1 hτ hy
  have htime : (fun τ ↦ movingNormalizedVelocity ell q mu A0 A1 τ y) =ᶠ[𝓝 t]
      (fun τ ↦ affineVelocity (coreCurl A0) (coreCurl A1) mu τ y) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    exact hlocal τ hτ
  have hspace : movingNormalizedVelocity ell q mu A0 A1 t =ᶠ[𝓝 y]
      affineVelocity (coreCurl A0) (coreCurl A1) mu t := by
    have hyball : y ∈ ball (0 : Space) (1 / 2) := by
      simpa [mem_ball, dist_zero_right] using hy
    filter_upwards [isOpen_ball.mem_nhds hyball] with x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      simpa [mem_ball, dist_zero_right] using hx
    exact movingNormalizedVelocity_eq_affineVelocity_of_pos ell q mu A0 A1
      hA0support hA1support hpos hA0 hA1 ht hxnorm
  have htime_deriv := htime.deriv_eq
  have hspace_fderiv :
      fderiv ℝ (movingNormalizedVelocity ell q mu A0 A1 t) y =
        fderiv ℝ (affineVelocity (coreCurl A0) (coreCurl A1) mu t) y :=
    hspace.fderiv_eq
  have hlaplacian : Δ (movingNormalizedVelocity ell q mu A0 A1 t) y =
      Δ (affineVelocity (coreCurl A0) (coreCurl A1) mu t) y :=
    (InnerProductSpace.laplacian_congr_nhds hspace).eq_of_nhds
  have hvalue := hlocal t ht
  unfold momentumResidual
  rw [htime_deriv, hspace_fderiv, hlaplacian, hvalue]

#print axioms physicalPotential_support_subset
#print axioms physicalPotential_curl_isOnePeriodic
#print axioms normalizedPeriodicVelocity_period
#print axioms normalizedPeriodicVelocity_eq_coreCurl_of_mem_ball
#print axioms coreCurl_add_const_smul
#print axioms affinePotential_support_subset
#print axioms normalizedPeriodicVelocity_affine_eq
#print axioms movingNormalizedVelocity_eq_affineVelocity_of_pos
#print axioms movingNormalizedVelocity_momentumResidual_eq_affine

end Soma.Holonics.Millennium.NavierStokesMovingPeriodicCore
