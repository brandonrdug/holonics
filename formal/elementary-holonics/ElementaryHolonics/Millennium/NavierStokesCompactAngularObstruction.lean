import ElementaryHolonics.Millennium.NavierStokesAffineAngularResidual
import ElementaryHolonics.Millennium.NavierStokesCompactMaximum
import ElementaryHolonics.Millennium.NavierStokesRadialCoreCutoff

/-!
# A compact leading circulation leaves a nonvanishing momentum residual

The pressure is arbitrary and the first velocity response can be nonaxisymmetric. A positive
compact axisymmetric leading angular momentum has a critical circle. Pressure has zero torque
somewhere on it; the complete first and second response terms are uniformly bounded there.
Consequently mu tending to zero cannot erase the leading normalization source.
-/

noncomputable section
open ContDiff Set Function Filter
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCompactAngularObstruction
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesExteriorTorque
open Soma.Holonics.Millennium.NavierStokesPressureCircle
open Soma.Holonics.Millennium.NavierStokesCompactMaximum
open Soma.Holonics.Millennium.NavierStokesAffineAngularResidual
open Soma.Holonics.Millennium.NavierStokesRadialCoreCutoff
open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential

theorem meridionalChart_circlePath (r z theta : ℝ) :
    meridionalChart (circlePath r z theta) = (r ^ 2, z) := by
  ext
  · simp only [meridionalChart, circlePath, assemble_zero, assemble_one]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  · simp [meridionalChart, circlePath]

theorem norm_circlePath_eq_of_meridional (p : Space) (theta : ℝ) :
    ‖circlePath (Real.sqrt (meridionalChart p).1) (meridionalChart p).2 theta‖ = ‖p‖ := by
  have hs : 0 ≤ (meridionalChart p).1 := by dsimp [meridionalChart]; positivity
  have hsq := norm_sq_eq_meridional
    (circlePath (Real.sqrt (meridionalChart p).1) (meridionalChart p).2 theta)
  rw [meridionalChart_circlePath, Real.sq_sqrt hs] at hsq
  have hp := norm_sq_eq_meridional p
  nlinarith [norm_nonneg p,
    norm_nonneg (circlePath (Real.sqrt (meridionalChart p).1) (meridionalChart p).2 theta)]

/-- This supplies the threshold from actual smooth fields and an attained compact maximum.
Neither a zero-pressure angle nor the finite correction bound is an assumed port. -/
theorem compact_leading_circulation_residual_lower_bound
    (u0 u1 : InitialVelocity) (h0 : ContDiff ℝ ∞ u0) (h1 : ContDiff ℝ ∞ u1)
    (Omega : MeridionalProfile) (hOmega : ContDiff ℝ 2 Omega)
    (hangular : angularField u0 = cartesianAngularMomentumProfile Omega)
    (hcompact : HasCompactSupport (angularField u0))
    (R : ℝ) (hsupport : support (angularField u0) ⊆ Metric.closedBall (0 : Space) R)
    (seed : Space) (hseed : 0 < angularField u0 seed)
    (alpha beta : ℝ) (hgap : beta < alpha) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (mu : ℝ → ℝ) (t : ℝ) (P : ℝ → Space → ℝ),
      HasDerivAt mu (-(alpha - beta) * mu t) t →
      0 ≤ mu t → mu t ≤ epsilon → ContDiff ℝ 1 (P t) →
      ∃ y : Space, ‖y‖ ≤ R ∧
        (alpha - beta) * angularField u0 seed / 2 ≤
          cartesianAngularMomentum y
            (momentumResidual (affineVelocity u0 u1 mu) P
              (fun _ ↦ alpha) (fun _ ↦ beta) mu t y) := by
  have hc : HasCompactSupport (cartesianAngularMomentumProfile Omega) := by
    rwa [hangular] at hcompact
  have hs : 0 < cartesianAngularMomentumProfile Omega seed := by rwa [hangular] at hseed
  obtain ⟨p, hpseed, hppos, _hmax, hpderiv, hps⟩ :=
    exists_positive_compact_angularMomentum_max Omega hOmega hc seed hs
  let r := Real.sqrt (meridionalChart p).1
  let z := (meridionalChart p).2
  let M := angularField u0 p
  have hM : 0 < M := by simpa [M, hangular] using hppos
  have hseedM : angularField u0 seed ≤ M := by simpa [M, hangular] using hpseed
  have hpR : ‖p‖ ≤ R := by
    have hpnonzero : angularField u0 p ≠ 0 := hM.ne'
    simpa using hsupport hpnonzero
  have hcircle (theta : ℝ) : meridionalChart (circlePath r z theta) = meridionalChart p := by
    rw [meridionalChart_circlePath]
    dsimp [r, z]
    rw [Real.sq_sqrt hps.le]
  have hvalue (theta : ℝ) : angularField u0 (circlePath r z theta) = M := by
    rw [hangular]
    change angularMomentum Omega (meridionalChart (circlePath r z theta)) = M
    rw [hcircle]
    exact (congrFun hangular p).symm
  have hd (theta : ℝ) : fderiv ℝ (angularField u0) (circlePath r z theta) = 0 := by
    have hO : DifferentiableAt ℝ (angularMomentum Omega) (meridionalChart p) :=
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := meridionalChart p)).mul
        (hOmega.differentiable (by norm_num) _).hasFDerivAt).differentiableAt
    rw [hangular]
    change fderiv ℝ (fun y ↦ angularMomentum Omega (meridionalChart y))
      (circlePath r z theta) = 0
    rw [(profileLift_hasFDerivAt (angularMomentum Omega) (circlePath r z theta)
      (by simpa only [hcircle] using hO)).fderiv, hcircle, hpderiv]
    simp
  obtain ⟨B, hBnonneg, hB⟩ := exists_circle_correction_bound beta u0 u1 h0 h1 r z
  let c0 := (alpha - beta) * M
  have hc0 : 0 < c0 := mul_pos (sub_pos.mpr hgap) hM
  let epsilon := min 1 (c0 / (2 * (B + 1)))
  have heps : 0 < epsilon := lt_min (by norm_num) (div_pos hc0 (by positivity))
  refine ⟨epsilon, heps, ?_⟩
  intro mu t P hmu hmunonneg hmusmall hP
  have hmu1 : mu t ≤ 1 := hmusmall.trans (min_le_left _ _)
  have hratio : mu t ≤ c0 / (2 * (B + 1)) := hmusmall.trans (min_le_right _ _)
  have hbudgetB : 2 * mu t * (B + 1) ≤ c0 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp hratio
    nlinarith
  obtain ⟨theta, htheta, htorque⟩ := exists_pressureTorque_eq_zero_on_circle (P t) hP r z
  have hbudget : 2 * mu t *
      (|firstAngularCorrection beta u0 u1 (circlePath r z theta)| +
        |secondAngularCorrection u1 (circlePath r z theta)|) ≤ c0 := by
    have h := mul_le_mul_of_nonneg_left ((hB theta htheta).trans (by linarith : B ≤ B + 1))
      (by positivity : 0 ≤ 2 * mu t)
    exact h.trans hbudgetB
  have hlower := polynomial_lower_bound c0
    (firstAngularCorrection beta u0 u1 (circlePath r z theta))
    (secondAngularCorrection u1 (circlePath r z theta)) (mu t) hmunonneg hmu1 hbudget
  have hres := affineVelocity_angular_residual u0 u1 P alpha beta mu t
    (h0.of_le (WithTop.coe_le_coe.mpr le_top)) (h1.of_le (WithTop.coe_le_coe.mpr le_top))
    hmu (circlePath r z theta)
  rw [hd, hvalue, htorque, ContinuousLinearMap.zero_apply] at hres
  refine ⟨circlePath r z theta, ?_, ?_⟩
  · exact (norm_circlePath_eq_of_meridional p theta).le.trans hpR
  · rw [hres]
    have hmul := mul_le_mul_of_nonneg_left hseedM (sub_pos.mpr hgap).le
    dsimp [c0] at hlower
    linarith

/-- A strict positive seed rules out exact momentum for the whole small-viscosity tail. -/
theorem compact_leading_circulation_not_exact
    (u0 u1 : InitialVelocity) (h0 : ContDiff ℝ ∞ u0) (h1 : ContDiff ℝ ∞ u1)
    (Omega : MeridionalProfile) (hOmega : ContDiff ℝ 2 Omega)
    (hangular : angularField u0 = cartesianAngularMomentumProfile Omega)
    (hcompact : HasCompactSupport (angularField u0))
    (R : ℝ) (hsupport : support (angularField u0) ⊆ Metric.closedBall (0 : Space) R)
    (seed : Space) (hseed : 0 < angularField u0 seed)
    (alpha beta : ℝ) (hgap : beta < alpha) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (mu : ℝ → ℝ) (t : ℝ) (P : ℝ → Space → ℝ),
      HasDerivAt mu (-(alpha - beta) * mu t) t →
      0 ≤ mu t → mu t ≤ epsilon → ContDiff ℝ 1 (P t) →
      ¬ (∀ y, ‖y‖ ≤ R → momentumResidual (affineVelocity u0 u1 mu) P
        (fun _ ↦ alpha) (fun _ ↦ beta) mu t y = 0) := by
  obtain ⟨epsilon, heps, hbound⟩ := compact_leading_circulation_residual_lower_bound
    u0 u1 h0 h1 Omega hOmega hangular hcompact R hsupport seed hseed alpha beta hgap
  refine ⟨epsilon, heps, ?_⟩
  intro mu t P hmu hmunonneg hmusmall hP hzero
  obtain ⟨y, hy, h⟩ := hbound mu t P hmu hmunonneg hmusmall hP
  rw [hzero y hy] at h
  have hpos : 0 < (alpha - beta) * angularField u0 seed / 2 := by positivity
  simp only [cartesianAngularMomentum, PiLp.zero_apply, mul_zero, sub_self] at h
  linarith

theorem cut_angular_profile (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    angularField (coreCurl (cutPotential h g)) = cartesianAngularMomentumProfile (cutOmega g) := by
  rw [cutPotential_curl h g hh hg]
  funext x
  simp [angularField, cartesianAngularMomentum, cartesianAngularMomentumProfile,
    angularMomentum, axisymmetricVelocity, meridionalChart]
  ring

/-- The constructed cut-potential family instantiates every compactness and symmetry
obligation. The seed inequality is the exact finite-coefficient receiver checked separately. -/
theorem finite_core_cutoff_residual_lower_bound
    (h0 g0 h1 g1 : MeridionalProfile)
    (hh0 : ContDiff ℝ ∞ h0) (hg0 : ContDiff ℝ ∞ g0)
    (hh1 : ContDiff ℝ ∞ h1) (hg1 : ContDiff ℝ ∞ g1)
    (radius : ℝ)
    (hseed : radius ^ 2 < angularField (coreCurl (cutPotential h0 g0)) (assemble radius 0 0)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (mu : ℝ → ℝ) (t : ℝ) (P : ℝ → Space → ℝ),
      HasDerivAt mu (-mu t / 2) t →
      0 ≤ mu t → mu t ≤ epsilon → ContDiff ℝ 1 (P t) →
      ∃ y : Space, ‖y‖ ≤ 1 / 4 ∧
        radius ^ 2 / 4 < cartesianAngularMomentum y
          (momentumResidual
            (affineVelocity (coreCurl (cutPotential h0 g0)) (coreCurl (cutPotential h1 g1)) mu)
            P (fun _ ↦ 3 / 2) (fun _ ↦ 1) mu t y) := by
  have h0s := coreCurl_contDiff _ (cutPotential_contDiff h0 g0 hh0 hg0)
  have h1s := coreCurl_contDiff _ (cutPotential_contDiff h1 g1 hh1 hg1)
  have hc := angularField_hasCompactSupport _
    (coreCurl_hasCompactSupport _ (cutPotential_hasCompactSupport h0 g0))
  obtain ⟨epsilon, heps, hbound⟩ := compact_leading_circulation_residual_lower_bound
    _ _ h0s h1s (cutOmega g0)
    ((cutOmega_contDiff g0 hg0).of_le (WithTop.coe_le_coe.mpr le_top))
    (cut_angular_profile h0 g0 hh0 hg0) hc (1 / 4) (cutVelocity_angular_support h0 g0)
    (assemble radius 0 0) (by nlinarith [sq_nonneg radius]) (3 / 2) 1 (by norm_num)
  refine ⟨epsilon, heps, ?_⟩
  intro mu t P hmu hmunonneg hmusmall hP
  have hm : HasDerivAt mu (-((3 : ℝ) / 2 - 1) * mu t) t := by
    convert hmu using 1 <;> ring
  obtain ⟨y, hy, hb⟩ := hbound mu t P hm hmunonneg hmusmall hP
  refine ⟨y, hy, ?_⟩
  linarith

#print axioms compact_leading_circulation_residual_lower_bound
#print axioms compact_leading_circulation_not_exact
#print axioms finite_core_cutoff_residual_lower_bound
end Soma.Holonics.Millennium.NavierStokesCompactAngularObstruction
