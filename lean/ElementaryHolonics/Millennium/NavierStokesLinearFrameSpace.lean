import ElementaryHolonics.Millennium.NavierStokesRescalingSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Anisotropic linear-frame spatial transport

This owner records the actual Cartesian chain rules for an invertible constant linear frame.  The
inverse relations are explicit hypotheses on the two continuous-linear maps; no isotropic or
diagonal specialization is built into the operators.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped Laplacian Pointwise

namespace Soma.Holonics.Millennium.NavierStokesLinearFrameSpace

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesRescalingSpace

def velocityPullback
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) : Space → Space :=
  fun y ↦ b • B (u (centre + A y))

def pressurePullback
    (b : ℝ) (A : Space →L[ℝ] Space) (centre : Space)
    (p : Space → ℝ) : Space → ℝ :=
  fun y ↦ b ^ 2 * p (centre + A y)

/-- The positive pressure metric induced by the transported map `B`. -/
def pressureMetric (B : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  B.comp (ContinuousLinearMap.adjoint B)

/-- The Laplacian formed from the transported Euclidean frame `B eᵢ`. -/
def weightedLaplacian (B : Space →L[ℝ] Space) (f : Space → Space) (y : Space) : Space :=
  ∑ i : Fin 3, iteratedFDeriv ℝ 2 f y
    ![B ((EuclideanSpace.basisFun (Fin 3) ℝ) i),
      B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)]

theorem fderiv_velocityPullback
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) (y : Space)
    (hu : DifferentiableAt ℝ u (centre + A y)) :
    fderiv ℝ (velocityPullback b A B centre u) y =
      b • (B.comp (fderiv ℝ u (centre + A y))).comp A := by
  have hframe : HasFDerivAt (fun z : Space ↦ centre + A z) A y := by
    exact A.hasFDerivAt.const_add centre
  have hinner := hu.hasFDerivAt.comp y hframe
  have hout := B.hasFDerivAt.comp y hinner
  have hscaled := hout.const_smul b
  change HasFDerivAt (velocityPullback b A B centre u) _ y at hscaled
  rw [hscaled.fderiv]
  rfl

theorem divergence_velocityPullback
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) (y : Space)
    (hu : DifferentiableAt ℝ u (centre + A y))
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space) :
    divergence (velocityPullback b A B centre u) y =
      b * divergence u (centre + A y) := by
  unfold divergence
  rw [fderiv_velocityPullback b A B centre u y hu]
  change LinearMap.trace ℝ Space
      ((b • (B.comp (fderiv ℝ u (centre + A y))).comp A).toLinearMap) = _
  rw [show (b • (B.comp (fderiv ℝ u (centre + A y))).comp A).toLinearMap =
      b • ((B.comp (fderiv ℝ u (centre + A y))).comp A).toLinearMap by rfl,
    LinearMap.map_smul]
  change b * LinearMap.trace ℝ Space
      (((B.comp (fderiv ℝ u (centre + A y))).comp A).toLinearMap) = _
  rw [show ((B.comp (fderiv ℝ u (centre + A y))).comp A).toLinearMap =
      B.toLinearMap ∘ₗ (fderiv ℝ u (centre + A y)).toLinearMap ∘ₗ A.toLinearMap by
        rfl]
  rw [LinearMap.trace_comp_cycle]
  have hAB' : A.toLinearMap ∘ₗ B.toLinearMap =
      (ContinuousLinearMap.id ℝ Space).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hAB
  rw [hAB']
  simp

theorem gradient_pressurePullback
    (b : ℝ) (A : Space →L[ℝ] Space) (centre : Space)
    (p : Space → ℝ) (y : Space)
    (hp : DifferentiableAt ℝ p (centre + A y)) :
    gradient (pressurePullback b A centre p) y =
      b ^ 2 • (ContinuousLinearMap.adjoint A) (gradient p (centre + A y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  unfold pressurePullback
  have hframe' : HasFDerivAt (fun z : Space ↦ centre + A z) A y := by
    exact A.hasFDerivAt.const_add centre
  rw [show (fun z : Space ↦ b ^ 2 * p (centre + A z)) =
      (fun z : Space ↦ b ^ 2 • p (centre + A z)) by
        funext z; simp [smul_eq_mul]]
  rw [show (fun z : Space ↦ b ^ 2 • p (centre + A z)) =
      b ^ 2 • (fun z : Space ↦ p (centre + A z)) by
        funext z; rfl,
    congrFun (fderiv_const_smul_field (b ^ 2)) y]
  simp only [Pi.smul_apply]
  have hcomp : (fun z : Space ↦ p (centre + A z)) =
      p ∘ (fun z : Space ↦ centre + A z) := rfl
  rw [hcomp, fderiv_comp y hp hframe'.differentiableAt, hframe'.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  have hgrad : fderiv ℝ p (centre + A y) (A v) =
      inner ℝ (gradient p (centre + A y)) (A v) := inner_gradient_left.symm
  rw [hgrad]
  simp [ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left]

theorem weightedLaplacian_eq_fderiv
    (B : Space →L[ℝ] Space) (f : Space → Space) (y : Space) :
    weightedLaplacian B f y =
      ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ f) y
        (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)))
        (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) := by
  unfold weightedLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_two_apply]
  simp

theorem weightedLaplacian_velocityPullback
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) (y : Space)
    (hu : ContDiff ℝ 2 u)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space) :
    weightedLaplacian B (velocityPullback b A B centre u) y =
      b • B (Δ u (centre + A y)) := by
  let translated : Space → Space := fun z ↦ u (centre + z)
  have htranslated : ContDiff ℝ 2 translated := by
    simpa [translated, Function.comp_def] using
      hu.comp (contDiff_const.add contDiff_id)
  have hiter : ∀ (m : Fin 2 → Space),
      iteratedFDeriv ℝ 2 (fun z : Space ↦ b • B (translated (A z))) y m =
        b • B (iteratedFDeriv ℝ 2 u (centre + A y)
          (fun j ↦ A (m j))) := by
    intro m
    have hright := A.iteratedFDeriv_comp_right htranslated y
      (i := 2) (by norm_num)
    have htranslatedA : ContDiff ℝ 2 (translated ∘ A) :=
      htranslated.comp_continuousLinearMap
    have hleft := (b • B).iteratedFDeriv_comp_left
      (x := y) htranslatedA.contDiffAt (i := 2) (by norm_num)
    have hright' := congrArg (fun H => H m) hright
    have hleft' := congrArg (fun H => H m) hleft
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe] at hleft'
    have hleft_eq :
        (iteratedFDeriv ℝ 2 (fun z : Space ↦ b • B (translated (A z))) y) m =
          b • B ((iteratedFDeriv ℝ 2 (translated ∘ A) y) m) := by
      simpa [Function.comp_def, smul_apply,
        ContinuousLinearMap.comp_apply] using hleft'
    rw [hright'] at hleft_eq
    rw [iteratedFDeriv_comp_add_left] at hleft_eq
    simpa [translated, velocityPullback, Function.comp_def,
      ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      smul_apply] using hleft_eq
  have hsum_inner :
      (∑ i : Fin 3,
        iteratedFDeriv ℝ 2 u (centre + A y)
          ![A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)),
            A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i))]) =
        Δ u (centre + A y) := by
    have hlap := congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
        (EuclideanSpace.basisFun (Fin 3) ℝ)) (centre + A y)
    calc
      (∑ i : Fin 3,
        iteratedFDeriv ℝ 2 u (centre + A y)
          ![A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)),
            A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i))]) =
          ∑ i : Fin 3,
            iteratedFDeriv ℝ 2 u (centre + A y)
              ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
                (EuclideanSpace.basisFun (Fin 3) ℝ) i] := by
        apply Finset.sum_congr rfl
        intro i hi
        have hABe : A (B (EuclideanSpace.single i (1 : ℝ))) =
            EuclideanSpace.single i (1 : ℝ) := by
          simpa using congrArg (fun L : Space →L[ℝ] Space =>
            L (EuclideanSpace.single i (1 : ℝ))) hAB
        simp [EuclideanSpace.basisFun_apply, hABe]
      _ = Δ u (centre + A y) := hlap.symm
  unfold weightedLaplacian
  calc
    ∑ i : Fin 3,
        (iteratedFDeriv ℝ 2 (velocityPullback b A B centre u) y)
          ![B ((EuclideanSpace.basisFun (Fin 3) ℝ) i),
            B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)] =
        ∑ i : Fin 3,
          b • B (iteratedFDeriv ℝ 2 u (centre + A y)
            ![A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)),
              A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i))]) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := hiter ![B ((EuclideanSpace.basisFun (Fin 3) ℝ) i),
        B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)]
      have hmap : (fun j : Fin 2 ↦ A
          (![B ((EuclideanSpace.basisFun (Fin 3) ℝ) i),
            B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)] j)) =
          ![A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)),
            A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i))] := by
        funext j
        fin_cases j <;> rfl
      rw [hmap] at hi'
      change (iteratedFDeriv ℝ 2 (fun z : Space ↦ b • B (translated (A z))) y)
          ![B ((EuclideanSpace.basisFun (Fin 3) ℝ) i),
            B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)] = _
      simpa [translated, Fin.prod_univ_two] using hi'
    _ = b • B (∑ i : Fin 3,
        iteratedFDeriv ℝ 2 u (centre + A y)
          ![A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i)),
            A (B ((EuclideanSpace.basisFun (Fin 3) ℝ) i))]) := by
      exact (Finset.smul_sum).symm.trans
        (congrArg (fun z => b • z) (map_sum B _ _).symm)
    _ = b • B (Δ u (centre + A y)) := by rw [hsum_inner]

theorem pressureMetric_apply
    (B : Space →L[ℝ] Space) (v : Space) :
    pressureMetric B v = B ((ContinuousLinearMap.adjoint B) v) := rfl

theorem pressureMetric_scaled_gradient
    (b : ℝ) (B : Space →L[ℝ] Space) (v : Space) :
    pressureMetric B (b ^ 2 • v) =
      b ^ 2 • B ((ContinuousLinearMap.adjoint B) v) := by
  unfold pressureMetric
  simp [ContinuousLinearMap.comp_apply, map_smul]

theorem velocityPullback_reconstruct
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) (hb : b ≠ 0)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space) :
    (fun x ↦ b⁻¹ • A (velocityPullback b A B centre u (B (x - centre)))) = u := by
  funext x
  unfold velocityPullback
  have hABx : A (B (x - centre)) = x - centre := by
    simpa using congrArg (fun L : Space →L[ℝ] Space => L (x - centre)) hAB
  have hABu : A (B (u x)) = u x := by
    simpa using congrArg (fun L : Space →L[ℝ] Space => L (u x)) hAB
  rw [map_smul, hABx, add_sub_cancel, hABu]
  simp [smul_smul, hb]

theorem velocityPullback_isPeriodic
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (u : Space → Space) (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hperiodic : IsOnePeriodic u) (i : Fin 3) :
    Function.Periodic (velocityPullback b A B centre u)
      (B (EuclideanSpace.single i (1 : ℝ))) := by
  intro y
  unfold velocityPullback
  have harg : centre + A (y + B (EuclideanSpace.single i (1 : ℝ))) =
      (centre + A y) + EuclideanSpace.single i 1 := by
    have hABe : A (B (EuclideanSpace.single i (1 : ℝ))) =
        EuclideanSpace.single i (1 : ℝ) := by
      simpa using congrArg (fun L : Space →L[ℝ] Space =>
        L (EuclideanSpace.single i (1 : ℝ))) hAB
    rw [map_add, hABe]
    abel
  rw [harg]
  exact congrArg (fun v => b • B v) (hperiodic (centre + A y) i)

theorem pressurePullback_isPeriodic
    (b : ℝ) (A B : Space →L[ℝ] Space) (centre : Space)
    (p : Space → ℝ) (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hperiodic : IsOnePeriodic p) (i : Fin 3) :
    Function.Periodic (pressurePullback b A centre p)
      (B (EuclideanSpace.single i (1 : ℝ))) := by
  intro y
  unfold pressurePullback
  have harg : centre + A (y + B (EuclideanSpace.single i (1 : ℝ))) =
      (centre + A y) + EuclideanSpace.single i 1 := by
    have hABe : A (B (EuclideanSpace.single i (1 : ℝ))) =
        EuclideanSpace.single i (1 : ℝ) := by
      simpa using congrArg (fun L : Space →L[ℝ] Space =>
        L (EuclideanSpace.single i (1 : ℝ))) hAB
    rw [map_add, hABe]
    abel
  rw [harg]
  exact congrArg (fun r => b ^ 2 * r) (hperiodic (centre + A y) i)

#print axioms fderiv_velocityPullback
#print axioms divergence_velocityPullback
#print axioms gradient_pressurePullback
#print axioms weightedLaplacian_eq_fderiv
#print axioms weightedLaplacian_velocityPullback
#print axioms pressureMetric_scaled_gradient
#print axioms velocityPullback_reconstruct
#print axioms velocityPullback_isPeriodic
#print axioms pressurePullback_isPeriodic

end Soma.Holonics.Millennium.NavierStokesLinearFrameSpace
