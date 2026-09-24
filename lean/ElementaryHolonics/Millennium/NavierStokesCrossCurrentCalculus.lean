import ElementaryHolonics.Millennium.NavierStokesCurlCommutation
import ElementaryHolonics.Millennium.HolonicEntropyHeatCurrent

/-!
# Differential calculus of the existing oriented fluid cross-current

The continuous bilinear realization below is exactly `NavierStokesVorticity.cross`.
Its second spatial derivative retains both mixed terms before taking the Laplacian.
-/
noncomputable section
open scoped BigOperators Laplacian
open ContDiff

namespace Soma.Holonics.Millennium.NavierStokesCrossCurrentCalculus
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

@[simp] theorem cross_add_left (u v w : Space) : cross (u + v) w = cross u w + cross v w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_add_right (u v w : Space) : cross u (v + w) = cross u v + cross u w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_smul_left (c : ℝ) (u v : Space) : cross (c • u) v = c • cross u v := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_smul_right (c : ℝ) (u v : Space) : cross u (c • v) = c • cross u v := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_sub_left (u v w : Space) : cross (u - v) w = cross u w - cross v w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_sub_right (u v w : Space) : cross u (v - w) = cross u v - cross u w := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
@[simp] theorem cross_zero_left (u : Space) : cross 0 u = 0 := by
  ext i; fin_cases i <;> simp [cross, crossProduct]
@[simp] theorem cross_zero_right (u : Space) : cross u 0 = 0 := by
  ext i; fin_cases i <;> simp [cross, crossProduct]

private def crossLeftCLM (u : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap {
    toFun := cross u
    map_add' := cross_add_right u
    map_smul' := by intro c v; exact cross_smul_right c u v }

def crossBilinear : Space →L[ℝ] Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap {
    toFun := crossLeftCLM
    map_add' := by
      intro u v; ext w i
      exact congrArg (fun a : Space => a i) (cross_add_left u v w)
    map_smul' := by
      intro c v; ext w i
      exact congrArg (fun a : Space => a i) (cross_smul_left c v w) }

@[simp] theorem crossBilinear_apply (u v : Space) : crossBilinear u v = cross u v := rfl

section GeneralDomain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cross_contDiff {n : WithTop ℕ∞} {f g : E → Space}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => cross (f x) (g x)) := by
  exact (crossBilinear.contDiff.comp hf).clm_apply hg

theorem cross_differentiableAt {f g : E → Space} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => cross (f y) (g y)) x :=
  (crossBilinear.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).differentiableAt

theorem fderiv_cross_apply {f g : E → Space} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => cross (f y) (g y)) x v =
      cross (fderiv ℝ f x v) (g x) + cross (f x) (fderiv ℝ g x v) := by
  have h := congrArg (fun L : E →L[ℝ] Space => L v)
    (crossBilinear.fderiv_of_bilinear hf hg)
  simpa [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    add_comm] using h

end GeneralDomain

theorem cross_sum_left {ι : Type*} (s : Finset ι) (f : ι → Space) (g : Space) :
    cross (∑ i ∈ s, f i) g = ∑ i ∈ s, cross (f i) g := by
  change (crossBilinear.flip g) (∑ i ∈ s, f i) = _
  simp

theorem cross_sum_right {ι : Type*} (s : Finset ι) (f : Space) (g : ι → Space) :
    cross f (∑ i ∈ s, g i) = ∑ i ∈ s, cross f (g i) := by
  change crossBilinear f (∑ i ∈ s, g i) = _
  simp

private theorem fderiv_eval_derivative (f : Space → Space) (hf : ContDiff ℝ 2 f)
    (x d e : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y e) x d =
      fderiv ℝ (fderiv ℝ f) x d e := by
  have hDfSmooth : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hDfSmooth.differentiable (by norm_num) x
  have h := congrArg (fun L : Space →L[ℝ] Space => L d)
    (fderiv_clm_apply hDf (differentiableAt_const e))
  simpa using h

/-- Two ordinary derivative product terms generate two mixed second-derivative terms. -/
theorem secondFDeriv_cross_diagonal (f g : Space → Space)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x e : Space) :
    fderiv ℝ (fderiv ℝ (fun y => cross (f y) (g y))) x e e =
      cross (fderiv ℝ (fderiv ℝ f) x e e) (g x) +
      cross (f x) (fderiv ℝ (fderiv ℝ g) x e e) +
      (2 : ℝ) • cross (fderiv ℝ f x e) (fderiv ℝ g x e) := by
  have hDf : ContDiff ℝ 1 (fun y => fderiv ℝ f y e) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hDg : ContDiff ℝ 1 (fun y => fderiv ℝ g y e) :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hfun : (fun y => fderiv ℝ (fun z => cross (f z) (g z)) y e) =
      (fun y => cross (fderiv ℝ f y e) (g y) + cross (f y) (fderiv ℝ g y e)) := by
    funext y
    exact fderiv_cross_apply (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y) e
  rw [← fderiv_eval_derivative _ (cross_contDiff hf hg) x e e, hfun]
  rw [fderiv_fun_add
    (cross_differentiableAt (hDf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x))
    (cross_differentiableAt (hf.differentiable (by norm_num) x) (hDg.differentiable (by norm_num) x))]
  simp only [ContinuousLinearMap.add_apply]
  rw [fderiv_cross_apply (hDf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x),
      fderiv_cross_apply (hf.differentiable (by norm_num) x) (hDg.differentiable (by norm_num) x),
      fderiv_eval_derivative f hf, fderiv_eval_derivative g hg]
  module

/-- The full Euclidean Laplacian keeps the oriented mixed derivative current. -/
theorem laplacian_cross (f g : Space → Space) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Space) :
    Δ (fun y => cross (f y) (g y)) x =
      cross (Δ f x) (g x) + cross (f x) (Δ g x) +
      (2 : ℝ) • ∑ i : Fin 3,
        cross (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i))
          (fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  rw [laplacian_eq_sum_secondFDeriv, laplacian_eq_sum_secondFDeriv,
    laplacian_eq_sum_secondFDeriv]
  simp_rw [secondFDeriv_cross_diagonal f g hf hg]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [cross_sum_left, cross_sum_right]

#print axioms fderiv_cross_apply
#print axioms laplacian_cross
end Soma.Holonics.Millennium.NavierStokesCrossCurrentCalculus
