import ElementaryHolonics.Millennium.NavierStokesGaussianCirculation
import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart

/-!
# The Gaussian circulation has a regular Cartesian core

The analytic divided difference supplies the angular velocity on the axis. The resulting field
is smooth and divergence-free, with its exact circulation. Its linear axial strain is explicitly
nonperiodic; the separate periodic potential owner supplies actual periodic initial data.
-/

noncomputable section
open ContDiff Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesGaussianCore
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesGaussianCirculation

def gaussianCoreVelocity (a Gamma q : ℝ) : InitialVelocity :=
  axisymmetricVelocity (fun _ ↦ -a / 2)
    (fun p ↦ gaussianAngularVelocity Gamma q p.1) (fun p ↦ a * p.2)

theorem gaussianCoreVelocity_contDiff (a Gamma q : ℝ) :
    ContDiff ℝ ∞ (gaussianCoreVelocity a Gamma q) := by
  have hO := gaussianAngularVelocity_contDiff Gamma q
  unfold gaussianCoreVelocity axisymmetricVelocity meridionalChart assemble
  fun_prop

theorem gaussianCoreVelocity_divergence (a Gamma q : ℝ) (x : Space) :
    divergence (gaussianCoreVelocity a Gamma q) x = 0 := by
  have hO : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ gaussianAngularVelocity Gamma q p.1)
      (meridionalChart x) :=
    ((gaussianAngularVelocity_contDiff Gamma q).comp contDiff_fst).differentiable
      (by simp) _
  have hW : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ a * p.2) (meridionalChart x) := by
    fun_prop
  rw [gaussianCoreVelocity, divergence_axisymmetricVelocity _ _ _ x
    (differentiableAt_const _) hO hW]
  have haxial : axialDerivative (fun p : ℝ × ℝ ↦ a * p.2) (meridionalChart x) = a := by
    let L : (ℝ × ℝ) →L[ℝ] ℝ := a • ContinuousLinearMap.snd ℝ ℝ ℝ
    change fderiv ℝ (fun p : ℝ × ℝ ↦ a * p.2) (meridionalChart x) (0, 1) = a
    have heq : (fun p : ℝ × ℝ ↦ a * p.2) = L := by funext p; rfl
    rw [heq, L.fderiv]
    simp [L]
  rw [haxial]
  simp [radialDerivative]
  ring

theorem gaussianCoreVelocity_angularMomentum (a Gamma q : ℝ) (x : Space) :
    x 0 * gaussianCoreVelocity a Gamma q x 1 -
        x 1 * gaussianCoreVelocity a Gamma q x 0 =
      gaussianCirculation Gamma q (x 0 ^ 2 + x 1 ^ 2) := by
  rw [← mul_gaussianAngularVelocity Gamma q (x 0 ^ 2 + x 1 ^ 2)]
  simp [gaussianCoreVelocity, axisymmetricVelocity, assemble, meridionalChart]
  ring

theorem gaussianCoreVelocity_axis (a Gamma q z : ℝ) :
    gaussianCoreVelocity a Gamma q (assemble 0 0 z) = assemble 0 0 (a * z) := by
  ext i
  fin_cases i <;> simp [gaussianCoreVelocity, axisymmetricVelocity, assemble, meridionalChart]

theorem gaussianCoreVelocity_not_periodic (a Gamma q : ℝ) (ha : a ≠ 0) :
    ¬IsOnePeriodic (gaussianCoreVelocity a Gamma q) := by
  intro hp
  have h := congrArg (fun v : Space ↦ v 2) (hp 0 2)
  simp [gaussianCoreVelocity, axisymmetricVelocity, assemble, meridionalChart] at h
  exact ha h

#print axioms gaussianCoreVelocity_contDiff
#print axioms gaussianCoreVelocity_divergence
#print axioms gaussianCoreVelocity_angularMomentum
#print axioms gaussianCoreVelocity_not_periodic
end Soma.Holonics.Millennium.NavierStokesGaussianCore
