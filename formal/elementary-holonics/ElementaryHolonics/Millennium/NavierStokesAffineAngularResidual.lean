import ElementaryHolonics.Millennium.NavierStokesExteriorTorque
import ElementaryHolonics.Millennium.NavierStokesPressureCircle
import ElementaryHolonics.Millennium.NavierStokesH3Production

/-!
# The complete angular residual of an affine viscosity response

The source is the actual Cartesian momentum residual. Both quadratic products and the vector
Laplacian remain present. With mu'=-(alpha-beta)mu, the first response's normalization current
cancels its time derivative; the leading angular current remains.
-/

noncomputable section
open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAffineAngularResidual
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
open Soma.Holonics.Millennium.NavierStokesExteriorTorque
open Soma.Holonics.Millennium.NavierStokesPressureCircle
open Soma.Holonics.Millennium.NavierStokesH3Production

def affineVelocity (u0 u1 : InitialVelocity) (mu : ℝ → ℝ) (t : ℝ) : InitialVelocity :=
  fun x ↦ u0 x + mu t • u1 x

def firstAngularCorrection (beta : ℝ) (u0 u1 : InitialVelocity) (x : Space) : ℝ :=
  fderiv ℝ (angularField u1) x (u0 x + beta • x) - cartesianAngularMomentum x (Δ u0 x)

def secondAngularCorrection (u1 : InitialVelocity) (x : Space) : ℝ :=
  fderiv ℝ (angularField u1) x (u1 x) - cartesianAngularMomentum x (Δ u1 x)

theorem affineVelocity_laplacian (u0 u1 : InitialVelocity) (mu : ℝ → ℝ) (t : ℝ)
    (h0 : ContDiff ℝ 2 u0) (h1 : ContDiff ℝ 2 u1) (x : Space) :
    Δ (affineVelocity u0 u1 mu t) x = Δ u0 x + mu t • Δ u1 x := by
  have hsm := ContDiff.const_smul (mu t) h1
  have hfun : affineVelocity u0 u1 mu t = u0 + (fun y ↦ mu t • u1 y) := rfl
  rw [hfun, h0.contDiffAt.laplacian_add hsm.contDiffAt]
  have hl := h1.contDiffAt.laplacian_CLM_comp_left
    (x := x) (l := (mu t) • ContinuousLinearMap.id ℝ Space)
  simpa [Function.comp_def] using congrArg (fun z : Space ↦ Δ u0 x + z) hl

/-- No symmetry or pressure hypothesis is used in this complete source expansion. -/
theorem affineVelocity_angular_residual (u0 u1 : InitialVelocity) (P : ℝ → Space → ℝ)
    (alpha beta : ℝ) (mu : ℝ → ℝ) (t : ℝ)
    (h0 : ContDiff ℝ 2 u0) (h1 : ContDiff ℝ 2 u1)
    (hmu : HasDerivAt mu (-(alpha - beta) * mu t) t) (x : Space) :
    cartesianAngularMomentum x
      (momentumResidual (affineVelocity u0 u1 mu) P (fun _ ↦ alpha) (fun _ ↦ beta) mu t x) =
      (alpha - beta) * angularField u0 x +
        fderiv ℝ (angularField u0) x (u0 x + mu t • u1 x + beta • x) +
        mu t * firstAngularCorrection beta u0 u1 x +
        mu t ^ 2 * secondAngularCorrection u1 x + pressureTorque (P t) x := by
  have hd0 := h0.differentiable (by norm_num) x
  have hd1 := h1.differentiable (by norm_num) x
  have htime := (hasDerivAt_const t (u0 x)).add (hmu.smul_const (u1 x))
  change HasDerivAt (fun τ ↦ affineVelocity u0 u1 mu τ x) _ t at htime
  have hspace := hd0.hasFDerivAt.add (hd1.hasFDerivAt.const_smul (mu t))
  change HasFDerivAt (affineVelocity u0 u1 mu t) _ x at hspace
  unfold firstAngularCorrection secondAngularCorrection
  rw [angularField_fderiv_apply u0 x _ hd0,
    angularField_fderiv_apply u1 x _ hd1, angularField_fderiv_apply u1 x _ hd1]
  unfold momentumResidual
  rw [htime.deriv, hspace.fderiv, affineVelocity_laplacian u0 u1 mu t h0 h1 x]
  simp only [affineVelocity, angularField, pressureTorque, cartesianAngularMomentum,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply,
    smul_eq_mul]
  ring

theorem angularField_contDiff (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (angularField u) := by
  have h0 : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := (coordinateProjection 0).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : Space ↦ x 1) := (coordinateProjection 1).contDiff
  exact (h0.mul (h1.comp hu)).sub (h1.mul (h0.comp hu))

theorem firstAngularCorrection_continuous (beta : ℝ) (u0 u1 : InitialVelocity)
    (h0 : ContDiff ℝ ∞ u0) (h1 : ContDiff ℝ ∞ u1) :
    Continuous (firstAngularCorrection beta u0 u1) := by
  have ha := (angularField_contDiff u1 h1).fderiv_right (m := ∞) (by simp)
  have hD := ha.clm_apply (h0.add (contDiff_const_smul beta))
  have hL := laplacian_contDiff h0
  have hc0 : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := (coordinateProjection 0).contDiff
  have hc1 : ContDiff ℝ ∞ (fun x : Space ↦ x 1) := (coordinateProjection 1).contDiff
  exact (hD.sub ((hc0.mul (hc1.comp hL)).sub (hc1.mul (hc0.comp hL)))).continuous

theorem secondAngularCorrection_continuous (u1 : InitialVelocity)
    (h1 : ContDiff ℝ ∞ u1) : Continuous (secondAngularCorrection u1) := by
  have h := firstAngularCorrection_continuous 0 u1 u1 h1 h1
  unfold firstAngularCorrection at h
  unfold secondAngularCorrection
  simpa using h

/-- A small viscosity coefficient cannot cancel a positive leading current with fixed finite
first and second corrections. This is an exact polynomial bound, not a stability estimate. -/
theorem polynomial_lower_bound (c0 c1 c2 mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hbudget : 2 * mu * (|c1| + |c2|) ≤ c0) :
    c0 / 2 ≤ c0 + mu * c1 + mu ^ 2 * c2 := by
  have h1 := mul_le_mul_of_nonneg_left (neg_le_abs c1) hmu
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs c2) (sq_nonneg mu)
  have hsq : mu ^ 2 ≤ mu := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right hsq (abs_nonneg c2)
  nlinarith

/-- The complete Cartesian differential operators supply a finite correction bound on the
whole pressure circle. The pressure itself is not part of this bound. -/
theorem exists_circle_correction_bound (beta : ℝ) (u0 u1 : InitialVelocity)
    (h0 : ContDiff ℝ ∞ u0) (h1 : ContDiff ℝ ∞ u1) (r z : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ theta ∈ Icc (0 : ℝ) (2 * Real.pi),
      |firstAngularCorrection beta u0 u1 (circlePath r z theta)| +
        |secondAngularCorrection u1 (circlePath r z theta)| ≤ B := by
  have hc := ((firstAngularCorrection_continuous beta u0 u1 h0 h1).abs.add
    (secondAngularCorrection_continuous u1 h1).abs).comp (continuous_circlePath r z)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  have hB' : ∀ theta ∈ Icc (0 : ℝ) (2 * Real.pi),
      |firstAngularCorrection beta u0 u1 (circlePath r z theta)| +
        |secondAngularCorrection u1 (circlePath r z theta)| ≤ B := by
    intro theta htheta
    have hn : 0 ≤ |firstAngularCorrection beta u0 u1 (circlePath r z theta)| +
        |secondAngularCorrection u1 (circlePath r z theta)| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa only [Function.comp_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hn]
      using hB theta htheta
  have hb0 := hB' 0 ⟨le_rfl, by positivity⟩
  exact ⟨B, (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hb0, hB'⟩

#print axioms affineVelocity_angular_residual
#print axioms polynomial_lower_bound
#print axioms exists_circle_correction_bound
end Soma.Holonics.Millennium.NavierStokesAffineAngularResidual
