import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Connection calculus primitives

The chart, directional derivative, and product/smoothness rules shared by ratio calculus and
curvature. Curvature identities and their physical/research consumers remain in their owners.
-/

noncomputable section

namespace Holonics.Geometry.HolonicConnectionCurvature

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- The base chart: `n` real coordinates. -/
abbrev Base (n : ℕ) := Fin n → ℝ

/-- The unit direction of one coordinate. -/
def direction (i : Fin n) : Base n := Pi.single i 1

/-- The differential along one coordinate direction. -/
def differential (i : Fin n) (f : Base n → 𝔤) : Base n → 𝔤 :=
  fun x => fderiv ℝ f x (direction i)

/-- A connection: one `𝔤`-valued component per coordinate direction. -/
abbrev Connection (n : ℕ) (𝔤 : Type*) := Fin n → Base n → 𝔤

theorem differential_eq_hasFDerivAt {f : Base n → 𝔤} {L : Base n →L[ℝ] 𝔤} {x : Base n}
    (hf : HasFDerivAt f L x) (i : Fin n) : differential i f x = L (direction i) := by
  simp [differential, hf.fderiv]

theorem differentiableAt_of_contDiff {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (x : Base n) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by decide)).differentiableAt

theorem differentiable_fderiv_of_contDiff {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by decide)).differentiable one_ne_zero

theorem hasFDerivAt_differential {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (j : Fin n)
    (x : Base n) :
    HasFDerivAt (differential j f) ((fderiv ℝ (fderiv ℝ f) x).flip (direction j)) x := by
  have h := ((differentiable_fderiv_of_contDiff hf) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (direction j) x)
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  exact h

theorem differentiableAt_differential {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (j : Fin n)
    (x : Base n) : DifferentiableAt ℝ (differential j f) x :=
  (hasFDerivAt_differential hf j x).differentiableAt

theorem differential_sub {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y - g y) x = differential i f x - differential i g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.sub hg.hasFDerivAt) i).trans ?_
  simp [differential]

theorem differential_add {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y + g y) x = differential i f x + differential i g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.add hg.hasFDerivAt) i).trans ?_
  simp [differential]

theorem differential_mul {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y * g y) x =
      f x * differential i g x + differential i f x * g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.mul' hg.hasFDerivAt) i).trans ?_
  simp [differential, smul_eq_mul, add_apply, smul_apply]

end Holonics.Geometry.HolonicConnectionCurvature
