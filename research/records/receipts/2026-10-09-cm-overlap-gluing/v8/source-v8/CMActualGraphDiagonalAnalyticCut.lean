import CMActualFiniteCutCyclePushforward
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! SOURCE-ONLY; NO KERNEL ACCEPTANCE CLAIM.

Construct local complex parameter germs from the actual CM cubic chart equations.
Their evaluation maps land in the existing Y/Z coordinate rings; covariance is
proved for the actual transported coordinate maps, then for their actual scheme
inclusions. Thus the graph-minus-diagonal normal germ is (I - 1)t at each
actual fixed point. Its logarithmic winding is computed by a circle integral
and consumed by the accepted intrinsic finite-cut cycle and Serre coefficients.

agent-inferred: use the inverse function theorem on (parameter, equation),
rather than assume a global elliptic uniformization or a cycle-class comparison.
This closes a local source comparison; it does not construct global fundamental
currents, a Thom/Poincare comparison, or an ambient Betti cup product.

The helical pair interaction enters through the actual complex quarter-turn and
its winding receiver. Faces and placement, cell holonomy and tube are touched;
helix, pair and tower thread remain attached. Avoided recorded failures: an
unjoined source entering a consumer and an assigned answer replacing its law.
Refs #62. All compiler work belongs to the shared native queue.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

open CategoryTheory AlgebraicGeometry Polynomial Filter Topology
open scoped Topology ContDiff

namespace Holonics.Hodge.CMGraphSource

def cmYPlaneEquation (p : ℂ × ℂ) : ℂ := p.1 ^ 3 - p.1 * p.2 ^ 2 - p.2
def cmZPlaneEquation (p : ℂ × ℂ) : ℂ := p.2 ^ 2 - p.1 ^ 3 + p.1
def cmYPlaneAction (p : ℂ × ℂ) : ℂ × ℂ := (Complex.I * p.1, -Complex.I * p.2)
def cmZPlaneAction (p : ℂ × ℂ) : ℂ × ℂ := (-p.1, Complex.I * p.2)

private theorem cmI_cube : Complex.I ^ 3 = -Complex.I := by
  calc
    Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
    _ = -Complex.I := by rw [Complex.I_sq]; ring

theorem cmYPlaneEquation_action (p : ℂ × ℂ) :
    cmYPlaneEquation (cmYPlaneAction p) = -Complex.I * cmYPlaneEquation p := by
  unfold cmYPlaneEquation cmYPlaneAction
  ring_nf <;> simp only [Complex.I_sq, cmI_cube] <;> ring

theorem cmZPlaneEquation_action (p : ℂ × ℂ) :
    cmZPlaneEquation (cmZPlaneAction p) = -cmZPlaneEquation p := by
  unfold cmZPlaneEquation cmZPlaneAction
  ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem cmYPlaneEquation_eval (p : ℂ × ℂ) :
    yMonicCubic.eval₂ (aeval p.2 : ℂ[X] →ₐ[ℂ] ℂ).toRingHom p.1 = cmYPlaneEquation p := by
  have hx : (aeval p.2 : ℂ[X] →ₐ[ℂ] ℂ).toRingHom X = p.2 := by
    change (aeval p.2 : ℂ[X] →ₐ[ℂ] ℂ) X = p.2
    exact aeval_X p.2
  simp only [yMonicCubic, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C,
    eval₂_X, map_pow, hx]
  unfold cmYPlaneEquation
  ring

theorem cmZPlaneEquation_eval (p : ℂ × ℂ) :
    squareCurve.toAffine.polynomial.eval₂ (aeval p.1 : ℂ[X] →ₐ[ℂ] ℂ).toRingHom p.2 =
      cmZPlaneEquation p := by
  have hx : (aeval p.1 : ℂ[X] →ₐ[ℂ] ℂ).toRingHom X = p.1 := by
    change (aeval p.1 : ℂ[X] →ₐ[ℂ] ℂ) X = p.1
    exact aeval_X p.1
  rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, map_sub, map_pow, hx]
  unfold cmZPlaneEquation
  ring

def cmYPlaneReceiver (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    YChartCubicRing →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom yMonicCubic (aeval p.2) p.1
    ((cmYPlaneEquation_eval p).trans hp)

def cmZPlaneReceiver (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    ZChartSquareRing →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom squareCurve.toAffine.polynomial (aeval p.1) p.2
    ((cmZPlaneEquation_eval p).trans hp)

@[simp] theorem cmYPlaneReceiver_a (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    cmYPlaneReceiver p hp yA = p.1 := by
  rw [cmYPlaneReceiver, AdjoinRoot.liftAlgHom_root]

@[simp] theorem cmYPlaneReceiver_b (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    cmYPlaneReceiver p hp yB = p.2 := by
  rw [cmYPlaneReceiver, AdjoinRoot.liftAlgHom_of]
  exact aeval_X p.2

@[simp] theorem cmZPlaneReceiver_u (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    cmZPlaneReceiver p hp zU = p.1 := by
  rw [cmZPlaneReceiver, AdjoinRoot.liftAlgHom_of]
  exact aeval_X p.1

@[simp] theorem cmZPlaneReceiver_v (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    cmZPlaneReceiver p hp zV = p.2 := by
  rw [cmZPlaneReceiver, AdjoinRoot.liftAlgHom_root]

theorem cmYPlaneReceiver_origin :
    cmYPlaneReceiver 0 (by simp [cmYPlaneEquation]) = yOriginReceiver := by
  apply yCoordinateAlgebraMap_ext <;> simp

theorem cmZPlaneReceiver_origin :
    cmZPlaneReceiver 0 (by simp [cmZPlaneEquation]) = zOriginReceiver := by
  apply zCoordinateAlgebraMap_ext <;> simp

/-- A comparison of maps on the existing coordinate ring, not an independently
defined action identified with iota by an assumption. -/
theorem cmYPlaneReceiver_actual_action (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    (cmYPlaneReceiver p hp).comp yIotaAlgebraMap =
      cmYPlaneReceiver (cmYPlaneAction p)
        (by rw [cmYPlaneEquation_action, hp, mul_zero]) := by
  apply yCoordinateAlgebraMap_ext
  · change cmYPlaneReceiver p hp (yIotaCoordinateRing yB) = _
    rw [yIotaCoordinateRing_b, map_mul, AlgHom.commutes, cmYPlaneReceiver_b]
    simp [cmYPlaneAction]
  · change cmYPlaneReceiver p hp (yIotaCoordinateRing yA) = _
    rw [yIotaCoordinateRing_a, map_mul, AlgHom.commutes, cmYPlaneReceiver_a]
    simp [cmYPlaneAction]

theorem cmZPlaneReceiver_actual_action (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    (cmZPlaneReceiver p hp).comp zIotaAlgebraMap =
      cmZPlaneReceiver (cmZPlaneAction p)
        (by rw [cmZPlaneEquation_action, hp, neg_zero]) := by
  apply zCoordinateAlgebraMap_ext
  · change cmZPlaneReceiver p hp (zIotaCoordinateRing zU) = _
    rw [zIotaCoordinateRing_u, map_neg, cmZPlaneReceiver_u]
    simp [cmZPlaneAction]
  · change cmZPlaneReceiver p hp (zIotaCoordinateRing zV) = _
    rw [zIotaCoordinateRing_v, map_mul, AlgHom.commutes, cmZPlaneReceiver_v]
    simp [cmZPlaneAction]

def cmYPlanePoint (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    cmComplexPoint ⟶ CMProjectiveCubic :=
  Spec.map (CommRingCat.ofHom (cmYPlaneReceiver p hp).toRingHom) ≫ yCurveChartInclusion

def cmZPlanePoint (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    cmComplexPoint ⟶ CMProjectiveCubic :=
  Spec.map (CommRingCat.ofHom (cmZPlaneReceiver p hp).toRingHom) ≫ zCurveChartInclusion

theorem cmYPlanePoint_origin :
    cmYPlanePoint 0 (by simp [cmYPlaneEquation]) = yActualFixedPoint ≫ cmFixedInclusion := by
  rw [cmYPlanePoint, cmYPlaneReceiver_origin, cmActualYFixedPoint_inclusion_map]

theorem cmZPlanePoint_origin :
    cmZPlanePoint 0 (by simp [cmZPlaneEquation]) = zActualFixedPoint ≫ cmFixedInclusion := by
  rw [cmZPlanePoint, cmZPlaneReceiver_origin, cmActualZFixedPoint_inclusion_map]

theorem cmYPlanePoint_actual_action (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    cmYPlanePoint p hp ≫ cubicIotaHom =
      cmYPlanePoint (cmYPlaneAction p)
        (by rw [cmYPlaneEquation_action, hp, mul_zero]) := by
  have hc : CommRingCat.ofHom yIotaCoordinateRing ≫
      CommRingCat.ofHom (cmYPlaneReceiver p hp).toRingHom =
      CommRingCat.ofHom (cmYPlaneReceiver (cmYPlaneAction p)
        (by rw [cmYPlaneEquation_action, hp, mul_zero])).toRingHom := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (cmYPlaneReceiver_actual_action p hp)
  change (Spec.map _ ≫ yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≫
    cubicIotaHom = _
  simp only [Category.assoc]
  rw [yCubicChart_iota_inclusion_square, ← Spec.map_comp_assoc, hc]
  rfl

theorem cmZPlanePoint_actual_action (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    cmZPlanePoint p hp ≫ cubicIotaHom =
      cmZPlanePoint (cmZPlaneAction p)
        (by rw [cmZPlaneEquation_action, hp, neg_zero]) := by
  have hc : CommRingCat.ofHom zIotaCoordinateRing ≫
      CommRingCat.ofHom (cmZPlaneReceiver p hp).toRingHom =
      CommRingCat.ofHom (cmZPlaneReceiver (cmZPlaneAction p)
        (by rw [cmZPlaneEquation_action, hp, neg_zero])).toRingHom := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (cmZPlaneReceiver_actual_action p hp)
  change (Spec.map _ ≫ zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫ cubicIotaHom = _
  simp only [Category.assoc]
  rw [zCubicChart_iota_inclusion_square, ← Spec.map_comp_assoc, hc]
  rfl

def cmYParameterEquation (p : ℂ × ℂ) : ℂ × ℂ := (p.1, cmYPlaneEquation p)
def cmZParameterEquation (p : ℂ × ℂ) : ℂ × ℂ := (p.2, cmZPlaneEquation p)

def cmYParameterDerivative : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr (ContinuousLinearEquiv.neg ℂ)

def cmZParameterDerivative : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearEquiv.prodComm ℂ ℂ ℂ

theorem cmYParameterEquation_derivative :
    HasStrictFDerivAt cmYParameterEquation
      (cmYParameterDerivative : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := by
  have ha : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := hasStrictFDerivAt_fst
  have hb : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := hasStrictFDerivAt_snd
  have hP : HasStrictFDerivAt cmYPlaneEquation
      (-ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
    have hraw := ((ha.pow 3).sub (ha.mul (hb.pow 2))).sub hb
    change HasStrictFDerivAt cmYPlaneEquation _ 0 at hraw
    apply hraw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro h
    simp [smul_apply, smul_eq_mul]
  change HasStrictFDerivAt (fun p : ℂ × ℂ => (p.1, cmYPlaneEquation p)) _ 0
  apply (ha.prodMk hP).congr_fderiv
  ext p <;> rfl

theorem cmZParameterEquation_derivative :
    HasStrictFDerivAt cmZParameterEquation
      (cmZParameterDerivative : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := by
  have hu : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := hasStrictFDerivAt_fst
  have hv : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := hasStrictFDerivAt_snd
  have hP : HasStrictFDerivAt cmZPlaneEquation
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
    have hraw := ((hv.pow 2).sub (hu.pow 3)).add hu
    change HasStrictFDerivAt cmZPlaneEquation _ 0 at hraw
    apply hraw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro h
    simp [smul_apply, smul_eq_mul]
  change HasStrictFDerivAt (fun p : ℂ × ℂ => (p.2, cmZPlaneEquation p)) _ 0
  apply (hv.prodMk hP).congr_fderiv
  ext p <;> rfl

def cmYAnalyticGerm (t : ℂ) : ℂ × ℂ :=
  cmYParameterEquation_derivative.localInverse
    cmYParameterEquation cmYParameterDerivative 0 (t, 0)

def cmZAnalyticGerm (t : ℂ) : ℂ × ℂ :=
  cmZParameterEquation_derivative.localInverse
    cmZParameterEquation cmZParameterDerivative 0 (t, 0)

@[simp] theorem cmYAnalyticGerm_zero : cmYAnalyticGerm 0 = 0 := by
  simpa [cmYAnalyticGerm, cmYParameterEquation, cmYPlaneEquation] using
    cmYParameterEquation_derivative.localInverse_apply_image

@[simp] theorem cmZAnalyticGerm_zero : cmZAnalyticGerm 0 = 0 := by
  simpa [cmZAnalyticGerm, cmZParameterEquation, cmZPlaneEquation] using
    cmZParameterEquation_derivative.localInverse_apply_image

theorem cmYAnalyticGerm_contDiff : ContDiffAt ℂ ∞ cmYAnalyticGerm 0 := by
  have hs : ContDiffAt ℂ ∞ cmYParameterEquation 0 := by
    unfold cmYParameterEquation cmYPlaneEquation
    fun_prop
  have himage : cmYParameterEquation 0 = 0 := by
    simp [cmYParameterEquation, cmYPlaneEquation]
  have hback :
      (cmYParameterEquation_derivative.toOpenPartialHomeomorph cmYParameterEquation).symm 0 =
        0 := by
    change cmYParameterEquation_derivative.localInverse
      cmYParameterEquation cmYParameterDerivative 0 0 = 0
    simpa only [himage] using cmYParameterEquation_derivative.localInverse_apply_image
  have hi0 : ContDiffAt ℂ ∞
      (cmYParameterEquation_derivative.localInverse
        cmYParameterEquation cmYParameterDerivative 0) 0 := by
    change ContDiffAt ℂ ∞
      (cmYParameterEquation_derivative.toOpenPartialHomeomorph cmYParameterEquation).symm 0
    apply (cmYParameterEquation_derivative.toOpenPartialHomeomorph
      cmYParameterEquation).contDiffAt_symm (f₀' := cmYParameterDerivative)
    · simpa only [himage] using
        cmYParameterEquation_derivative.image_mem_toOpenPartialHomeomorph_target
    · simpa only [hback, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using
        cmYParameterEquation_derivative.hasFDerivAt
    · simpa only [hback, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hs
  have he : ContDiffAt ℂ ∞ (fun t : ℂ => (t, (0 : ℂ))) 0 := by fun_prop
  unfold cmYAnalyticGerm
  exact hi0.comp (f := fun t : ℂ => (t, (0 : ℂ))) 0 he

theorem cmZAnalyticGerm_contDiff : ContDiffAt ℂ ∞ cmZAnalyticGerm 0 := by
  have hs : ContDiffAt ℂ ∞ cmZParameterEquation 0 := by
    unfold cmZParameterEquation cmZPlaneEquation
    fun_prop
  have himage : cmZParameterEquation 0 = 0 := by
    simp [cmZParameterEquation, cmZPlaneEquation]
  have hback :
      (cmZParameterEquation_derivative.toOpenPartialHomeomorph cmZParameterEquation).symm 0 =
        0 := by
    change cmZParameterEquation_derivative.localInverse
      cmZParameterEquation cmZParameterDerivative 0 0 = 0
    simpa only [himage] using cmZParameterEquation_derivative.localInverse_apply_image
  have hi0 : ContDiffAt ℂ ∞
      (cmZParameterEquation_derivative.localInverse
        cmZParameterEquation cmZParameterDerivative 0) 0 := by
    change ContDiffAt ℂ ∞
      (cmZParameterEquation_derivative.toOpenPartialHomeomorph cmZParameterEquation).symm 0
    apply (cmZParameterEquation_derivative.toOpenPartialHomeomorph
      cmZParameterEquation).contDiffAt_symm (f₀' := cmZParameterDerivative)
    · simpa only [himage] using
        cmZParameterEquation_derivative.image_mem_toOpenPartialHomeomorph_target
    · simpa only [hback, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using
        cmZParameterEquation_derivative.hasFDerivAt
    · simpa only [hback, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hs
  have he : ContDiffAt ℂ ∞ (fun t : ℂ => (t, (0 : ℂ))) 0 := by fun_prop
  unfold cmZAnalyticGerm
  exact hi0.comp (f := fun t : ℂ => (t, (0 : ℂ))) 0 he

theorem cmYAnalyticGerm_coordinates :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmYAnalyticGerm t).1 = t ∧ cmYPlaneEquation (cmYAnalyticGerm t) = 0 := by
  have he : Tendsto (fun t : ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    have hc : Continuous (fun t : ℂ => (t, (0 : ℂ))) := continuous_id.prodMk continuous_const
    simpa only [Prod.mk_zero_zero] using (hc.continuousAt (x := (0 : ℂ))).tendsto
  have hr : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      cmYParameterEquation (cmYParameterEquation_derivative.localInverse
        cmYParameterEquation cmYParameterDerivative 0 p) = p := by
    simpa [cmYParameterEquation, cmYPlaneEquation, Prod.mk_zero_zero] using
      cmYParameterEquation_derivative.eventually_right_inverse
  have hi := he.eventually hr
  simpa only [cmYParameterEquation, cmYAnalyticGerm, Prod.mk.injEq] using hi

theorem cmZAnalyticGerm_coordinates :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmZAnalyticGerm t).2 = t ∧ cmZPlaneEquation (cmZAnalyticGerm t) = 0 := by
  have he : Tendsto (fun t : ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    have hc : Continuous (fun t : ℂ => (t, (0 : ℂ))) := continuous_id.prodMk continuous_const
    simpa only [Prod.mk_zero_zero] using (hc.continuousAt (x := (0 : ℂ))).tendsto
  have hr : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      cmZParameterEquation (cmZParameterEquation_derivative.localInverse
        cmZParameterEquation cmZParameterDerivative 0 p) = p := by
    simpa [cmZParameterEquation, cmZPlaneEquation, Prod.mk_zero_zero] using
      cmZParameterEquation_derivative.eventually_right_inverse
  have hi := he.eventually hr
  simpa only [cmZParameterEquation, cmZAnalyticGerm, Prod.mk.injEq] using hi

theorem cmYAnalyticGerm_action :
    ∀ᶠ t : ℂ in 𝓝 0,
      cmYAnalyticGerm (Complex.I * t) = cmYPlaneAction (cmYAnalyticGerm t) := by
  have hT : ContinuousAt (fun t => cmYPlaneAction (cmYAnalyticGerm t)) 0 := by
    apply ContinuousAt.comp
      (show ContinuousAt cmYPlaneAction (cmYAnalyticGerm 0) by
        unfold cmYPlaneAction; fun_prop)
    exact cmYAnalyticGerm_contDiff.continuousAt
  have ht : Tendsto (fun t => cmYPlaneAction (cmYAnalyticGerm t)) (𝓝 0) (𝓝 0) := by
    simpa [cmYPlaneAction, Prod.mk_zero_zero] using hT.tendsto
  have hl := ht.eventually cmYParameterEquation_derivative.eventually_left_inverse
  filter_upwards [cmYAnalyticGerm_coordinates, hl] with t hc hi
  have he : cmYParameterEquation (cmYPlaneAction (cmYAnalyticGerm t)) =
      (Complex.I * t, 0) := by
    apply Prod.ext
    · simp [cmYParameterEquation, cmYPlaneAction, hc.1]
    · change cmYPlaneEquation (cmYPlaneAction (cmYAnalyticGerm t)) = 0
      rw [cmYPlaneEquation_action, hc.2, mul_zero]
  rw [he] at hi
  exact hi

theorem cmZAnalyticGerm_action :
    ∀ᶠ t : ℂ in 𝓝 0,
      cmZAnalyticGerm (Complex.I * t) = cmZPlaneAction (cmZAnalyticGerm t) := by
  have hT : ContinuousAt (fun t => cmZPlaneAction (cmZAnalyticGerm t)) 0 := by
    apply ContinuousAt.comp
      (show ContinuousAt cmZPlaneAction (cmZAnalyticGerm 0) by
        unfold cmZPlaneAction; fun_prop)
    exact cmZAnalyticGerm_contDiff.continuousAt
  have ht : Tendsto (fun t => cmZPlaneAction (cmZAnalyticGerm t)) (𝓝 0) (𝓝 0) := by
    simpa [cmZPlaneAction, Prod.mk_zero_zero] using hT.tendsto
  have hl := ht.eventually cmZParameterEquation_derivative.eventually_left_inverse
  filter_upwards [cmZAnalyticGerm_coordinates, hl] with t hc hi
  have he : cmZParameterEquation (cmZPlaneAction (cmZAnalyticGerm t)) =
      (Complex.I * t, 0) := by
    apply Prod.ext
    · simp [cmZParameterEquation, cmZPlaneAction, hc.1]
    · change cmZPlaneEquation (cmZPlaneAction (cmZAnalyticGerm t)) = 0
      rw [cmZPlaneEquation_action, hc.2, neg_zero]
  rw [he] at hi
  exact hi

/-- The constructed local complex germ is evaluated into the actual global
projective cubic, and its parameter action is the existing cubic morphism. -/
theorem cmYAnalyticGerm_actual_source :
    ∀ᶠ t : ℂ in 𝓝 0,
      ∃ hp : cmYPlaneEquation (cmYAnalyticGerm t) = 0,
      ∃ hp' : cmYPlaneEquation (cmYAnalyticGerm (Complex.I * t)) = 0,
        cmYPlanePoint (cmYAnalyticGerm t) hp ≫ cubicIotaHom =
          cmYPlanePoint (cmYAnalyticGerm (Complex.I * t)) hp' := by
  filter_upwards [cmYAnalyticGerm_coordinates, cmYAnalyticGerm_action] with t hc he
  have hp' : cmYPlaneEquation (cmYAnalyticGerm (Complex.I * t)) = 0 := by
    rw [he, cmYPlaneEquation_action, hc.2, mul_zero]
  refine ⟨hc.2, hp', ?_⟩
  simpa only [he] using cmYPlanePoint_actual_action (cmYAnalyticGerm t) hc.2

theorem cmZAnalyticGerm_actual_source :
    ∀ᶠ t : ℂ in 𝓝 0,
      ∃ hp : cmZPlaneEquation (cmZAnalyticGerm t) = 0,
      ∃ hp' : cmZPlaneEquation (cmZAnalyticGerm (Complex.I * t)) = 0,
        cmZPlanePoint (cmZAnalyticGerm t) hp ≫ cubicIotaHom =
          cmZPlanePoint (cmZAnalyticGerm (Complex.I * t)) hp' := by
  filter_upwards [cmZAnalyticGerm_coordinates, cmZAnalyticGerm_action] with t hc he
  have hp' : cmZPlaneEquation (cmZAnalyticGerm (Complex.I * t)) = 0 := by
    rw [he, cmZPlaneEquation_action, hc.2, neg_zero]
  refine ⟨hc.2, hp', ?_⟩
  simpa only [he] using cmZPlanePoint_actual_action (cmZAnalyticGerm t) hc.2

/-- In the actual source parameter, graph minus diagonal is the linear normal
germ (I-1)t. The zero and parameter identities above are constructed, not input. -/
theorem cmYAnalyticGerm_graph_minus_diagonal :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmYPlaneAction (cmYAnalyticGerm t)).1 - (cmYAnalyticGerm t).1 =
        (Complex.I - 1) * t := by
  filter_upwards [cmYAnalyticGerm_coordinates] with t ht
  simp only [cmYPlaneAction, ht.1]
  ring

theorem cmZAnalyticGerm_graph_minus_diagonal :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmZPlaneAction (cmZAnalyticGerm t)).2 - (cmZAnalyticGerm t).2 =
        (Complex.I - 1) * t := by
  filter_upwards [cmZAnalyticGerm_coordinates] with t ht
  simp only [cmZPlaneAction, ht.1]
  ring

/-- A genuine common neighborhood exists for both source charts and their
quarter-turn covariance. A loop radius is then chosen smaller than this radius;
the unit circle is not assumed to lie inside either inverse chart. -/
theorem cmActualGraphDiagonal_small_radius :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      ((cmYAnalyticGerm t).1 = t ∧ cmYPlaneEquation (cmYAnalyticGerm t) = 0) ∧
      ((cmZAnalyticGerm t).2 = t ∧ cmZPlaneEquation (cmZAnalyticGerm t) = 0) ∧
      cmYAnalyticGerm (Complex.I * t) = cmYPlaneAction (cmYAnalyticGerm t) ∧
      cmZAnalyticGerm (Complex.I * t) = cmZPlaneAction (cmZAnalyticGerm t) := by
  have hh := cmYAnalyticGerm_coordinates.and
    (cmZAnalyticGerm_coordinates.and (cmYAnalyticGerm_action.and cmZAnalyticGerm_action))
  rcases Metric.eventually_nhds_iff.mp hh with ⟨r, hr, hh⟩
  refine ⟨r, hr, ?_⟩
  intro t ht
  exact hh (by simpa only [dist_zero_right] using ht)

private theorem cmNormalSlope_ne_zero : Complex.I - 1 ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

def cmGraphDiagonalNormal (t : ℂ) : ℂ := (Complex.I - 1) * t

theorem cmGraphDiagonalNormal_zero_iff (t : ℂ) :
    cmGraphDiagonalNormal t = 0 ↔ t = 0 := by
  simp [cmGraphDiagonalNormal, cmNormalSlope_ne_zero]

theorem cmGraphDiagonalNormal_logarithmicDerivative (t : ℂ) :
    (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1) = t⁻¹ := by
  rw [cmGraphDiagonalNormal, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ cmNormalSlope_ne_zero, mul_one]

/-- This is a computed local residue of the derived normal germ. It has not
yet been identified with a global cup/Betti intersection by a Thom comparison. -/
def cmGraphDiagonalLocalWinding (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∮ t in C(0, R), (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1))

theorem cmGraphDiagonalLocalWinding_one (R : ℝ) (hR : R ≠ 0) :
    cmGraphDiagonalLocalWinding R = 1 := by
  have hw : (∮ t in C(0, R), t⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    simpa using circleIntegral.integral_sub_center_inv 0 hR
  unfold cmGraphDiagonalLocalWinding
  simp_rw [cmGraphDiagonalNormal_logarithmicDerivative]
  rw [hw]
  exact inv_mul_cancel₀ (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

theorem cmGraphDiagonalLocalWinding_eq_Y_coefficient (R : ℝ) (hR : R ≠ 0) :
    cmGraphDiagonalLocalWinding R = (cmActualFiniteCutCycle cmActualYFixedPoint : ℂ) := by
  rw [cmGraphDiagonalLocalWinding_one R hR, cmActualFiniteCutCycle_coefficient]
  norm_num

theorem cmGraphDiagonalLocalWinding_eq_Z_coefficient (R : ℝ) (hR : R ≠ 0) :
    cmGraphDiagonalLocalWinding R = (cmActualFiniteCutCycle cmActualZFixedPoint : ℂ) := by
  rw [cmGraphDiagonalLocalWinding_one R hR, cmActualFiniteCutCycle_coefficient]
  norm_num

theorem cmGraphDiagonalLocalWinding_eq_Y_Serre (R : ℝ) (hR : R ≠ 0) :
    cmGraphDiagonalLocalWinding R = (cmActualYGraphDiagonalSerreMultiplicity : ℂ) := by
  rw [cmGraphDiagonalLocalWinding_eq_Y_coefficient R hR,
    cmActualFiniteCutCycle_Y_eq_Serre]

theorem cmGraphDiagonalLocalWinding_eq_Z_Serre (R : ℝ) (hR : R ≠ 0) :
    cmGraphDiagonalLocalWinding R = (cmActualZGraphDiagonalSerreMultiplicity : ℂ) := by
  rw [cmGraphDiagonalLocalWinding_eq_Z_coefficient R hR,
    cmActualFiniteCutCycle_Z_eq_Serre]

/-- Consumer on the already constructed finite-cut pushforward. The radii
may be chosen separately inside the two local source germs. -/
theorem cmActualFiniteCutPushforward_eq_two_localWindings
    (b : cmComplexPoint) (RY RZ : ℝ) (hY : RY ≠ 0) (hZ : RZ ≠ 0) :
    (cmActualFiniteCutPushforward b : ℂ) =
      cmGraphDiagonalLocalWinding RY + cmGraphDiagonalLocalWinding RZ := by
  rw [cmActualFiniteCutPushforward_coefficient,
    cmGraphDiagonalLocalWinding_one RY hY, cmGraphDiagonalLocalWinding_one RZ hZ]
  norm_num

/-- The actual graph-minus-diagonal functions on the constructed source germs.
They need not equal their linear model away from the admitted neighborhood. -/
def cmYActualNormal (t : ℂ) : ℂ :=
  (cmYPlaneAction (cmYAnalyticGerm t)).1 - (cmYAnalyticGerm t).1

def cmZActualNormal (t : ℂ) : ℂ :=
  (cmZPlaneAction (cmZAnalyticGerm t)).2 - (cmZAnalyticGerm t).2

theorem cmYActualNormal_eq_model : cmYActualNormal =ᶠ[𝓝 0] cmGraphDiagonalNormal :=
  cmYAnalyticGerm_graph_minus_diagonal

theorem cmZActualNormal_eq_model : cmZActualNormal =ᶠ[𝓝 0] cmGraphDiagonalNormal :=
  cmZAnalyticGerm_graph_minus_diagonal

theorem cmGraphDiagonalNormal_deriv (t : ℂ) :
    deriv cmGraphDiagonalNormal t = Complex.I - 1 := by
  exact deriv_const_mul_id (Complex.I - 1)

theorem cmYActualNormal_deriv :
    deriv cmYActualNormal =ᶠ[𝓝 0] fun _ => Complex.I - 1 := by
  filter_upwards [cmYActualNormal_eq_model.deriv] with t ht
  exact ht.trans (cmGraphDiagonalNormal_deriv t)

theorem cmZActualNormal_deriv :
    deriv cmZActualNormal =ᶠ[𝓝 0] fun _ => Complex.I - 1 := by
  filter_upwards [cmZActualNormal_eq_model.deriv] with t ht
  exact ht.trans (cmGraphDiagonalNormal_deriv t)

def cmYActualLocalWinding (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∮ t in C(0, R), (cmYActualNormal t)⁻¹ * deriv cmYActualNormal t)

def cmZActualLocalWinding (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∮ t in C(0, R), (cmZActualNormal t)⁻¹ * deriv cmZActualNormal t)

/-- Both logarithmic currents are computed from the actual normal germs,
including their actual derivatives, on sufficiently small positive circles. -/
theorem cmActualLocalWinding_source_radius :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      cmYActualLocalWinding R = cmGraphDiagonalLocalWinding R ∧
      cmZActualLocalWinding R = cmGraphDiagonalLocalWinding R := by
  have hY : ∀ᶠ t : ℂ in 𝓝 0,
      (cmYActualNormal t)⁻¹ * deriv cmYActualNormal t =
        (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1) := by
    filter_upwards [cmYActualNormal_eq_model, cmYActualNormal_deriv] with t hn hd
    rw [hn, hd]
  have hZ : ∀ᶠ t : ℂ in 𝓝 0,
      (cmZActualNormal t)⁻¹ * deriv cmZActualNormal t =
        (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1) := by
    filter_upwards [cmZActualNormal_eq_model, cmZActualNormal_deriv] with t hn hd
    rw [hn, hd]
  rcases Metric.eventually_nhds_iff.mp (hY.and hZ) with ⟨r, hr, hh⟩
  refine ⟨r, hr, ?_⟩
  intro R hR hRr
  have hcircle : ∀ t ∈ Metric.sphere (0 : ℂ) R,
      (cmYActualNormal t)⁻¹ * deriv cmYActualNormal t =
        (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1) ∧
      (cmZActualNormal t)⁻¹ * deriv cmZActualNormal t =
        (cmGraphDiagonalNormal t)⁻¹ * (Complex.I - 1) := by
    intro t ht
    apply hh
    rw [Metric.mem_sphere.mp ht]
    exact hRr
  constructor
  · unfold cmYActualLocalWinding cmGraphDiagonalLocalWinding
    congr 1
    exact circleIntegral.integral_congr hR.le (fun t ht => (hcircle t ht).1)
  · unfold cmZActualLocalWinding cmGraphDiagonalLocalWinding
    congr 1
    exact circleIntegral.integral_congr hR.le (fun t ht => (hcircle t ht).2)

/-- No geometric comparison is assumed: the local analytic source is
constructed above, its two residues equal the accepted Serre coefficients,
and their sum is read by the existing actual finite-cut pushforward. This
does not yet assert the ambient Betti cup-product pairing. -/
theorem cmActualFiniteCutPushforward_actual_analytic_source (b : cmComplexPoint) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t : ℂ, ‖t‖ < r →
        ((cmYAnalyticGerm t).1 = t ∧ cmYPlaneEquation (cmYAnalyticGerm t) = 0) ∧
        ((cmZAnalyticGerm t).2 = t ∧ cmZPlaneEquation (cmZAnalyticGerm t) = 0) ∧
        cmYAnalyticGerm (Complex.I * t) = cmYPlaneAction (cmYAnalyticGerm t) ∧
        cmZAnalyticGerm (Complex.I * t) = cmZPlaneAction (cmZAnalyticGerm t)) ∧
      ∀ RY RZ : ℝ,
      0 < RY → RY < r → 0 < RZ → RZ < r →
      cmYActualLocalWinding RY = (cmActualYGraphDiagonalSerreMultiplicity : ℂ) ∧
      cmZActualLocalWinding RZ = (cmActualZGraphDiagonalSerreMultiplicity : ℂ) ∧
      (cmActualFiniteCutPushforward b : ℂ) =
        cmYActualLocalWinding RY + cmZActualLocalWinding RZ := by
  rcases cmActualGraphDiagonal_small_radius with ⟨rc, hrc, hc⟩
  rcases cmActualLocalWinding_source_radius with ⟨rw, hrw, hh⟩
  refine ⟨min rc rw, lt_min hrc hrw, ?_, ?_⟩
  · intro t ht
    exact hc t (lt_of_lt_of_le ht (min_le_left rc rw))
  · intro RY RZ hY hYr hZ hZr
    rw [(hh RY hY (lt_of_lt_of_le hYr (min_le_right rc rw))).1,
      (hh RZ hZ (lt_of_lt_of_le hZr (min_le_right rc rw))).2]
    exact ⟨cmGraphDiagonalLocalWinding_eq_Y_Serre RY hY.ne',
      cmGraphDiagonalLocalWinding_eq_Z_Serre RZ hZ.ne',
      cmActualFiniteCutPushforward_eq_two_localWindings b RY RZ hY.ne' hZ.ne'⟩

#print axioms cmYPlanePoint_origin
#print axioms cmZPlanePoint_origin
#print axioms cmYPlanePoint_actual_action
#print axioms cmZPlanePoint_actual_action
#print axioms cmYAnalyticGerm_contDiff
#print axioms cmZAnalyticGerm_contDiff
#print axioms cmYAnalyticGerm_coordinates
#print axioms cmZAnalyticGerm_coordinates
#print axioms cmYAnalyticGerm_actual_source
#print axioms cmZAnalyticGerm_actual_source
#print axioms cmYAnalyticGerm_graph_minus_diagonal
#print axioms cmZAnalyticGerm_graph_minus_diagonal
#print axioms cmActualGraphDiagonal_small_radius
#print axioms cmGraphDiagonalLocalWinding_eq_Y_Serre
#print axioms cmGraphDiagonalLocalWinding_eq_Z_Serre
#print axioms cmActualFiniteCutPushforward_eq_two_localWindings
#print axioms cmActualLocalWinding_source_radius
#print axioms cmActualFiniteCutPushforward_actual_analytic_source

/-! ## The actual cubic chart overlap carries a nonvanishing tangent mode

These operations use the same plane equations and CM actions that feed the
coordinate-ring receivers above. The overlap is restricted by `p.2 ≠ 0`;
its inverse is restricted by `p.2 ≠ 0` in the Z chart. No scheme overlap,
global analytic carrier, period lattice or Betti comparison is assumed here.

The field is the rotated equation gradient. The equation multiplier and
Jacobian determinant on the overlap are both `-b⁻³`, so their factors cancel
in the tangent transport. Its dual reads the carried tangent coefficient.
This is an actual source compatibility equation, not a spectral-gap inference.
-/

def cmYToZOverlap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 / p.2, 1 / p.2)
def cmZToYOverlap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 / p.2, 1 / p.2)

def cmYToZOverlapTangent (p tangent : ℂ × ℂ) : ℂ × ℂ :=
  ((p.2 * tangent.1 - p.1 * tangent.2) / p.2 ^ 2, -tangent.2 / p.2 ^ 2)

def cmYTangentField (p : ℂ × ℂ) : ℂ × ℂ :=
  (2 * p.1 * p.2 + 1, 3 * p.1 ^ 2 - p.2 ^ 2)
def cmZTangentField (p : ℂ × ℂ) : ℂ × ℂ :=
  (-2 * p.2, 1 - 3 * p.1 ^ 2)

def cmYEquationTangentReading (p tangent : ℂ × ℂ) : ℂ :=
  (3 * p.1 ^ 2 - p.2 ^ 2) * tangent.1 + (-2 * p.1 * p.2 - 1) * tangent.2
def cmZEquationTangentReading (p tangent : ℂ × ℂ) : ℂ :=
  (1 - 3 * p.1 ^ 2) * tangent.1 + (2 * p.2) * tangent.2

/-- The complex coefficient read by the dual of a nonzero situated tangent
field. The coordinate choice keeps the second direction when the first is zero. -/
def cmTangentClockReading (field tangent : ℂ × ℂ) : ℂ :=
  if field.1 ≠ 0 then tangent.1 / field.1 else tangent.2 / field.2

theorem cmYToZOverlap_inverse (p : ℂ × ℂ) (hb : p.2 ≠ 0) :
    cmZToYOverlap (cmYToZOverlap p) = p := by
  have hi : (1 : ℂ) / p.2 ≠ 0 := div_ne_zero one_ne_zero hb
  apply Prod.ext <;> dsimp [cmYToZOverlap, cmZToYOverlap]
  · field_simp [hb]
  · field_simp [hb]

theorem cmZToYOverlap_inverse (p : ℂ × ℂ) (hv : p.2 ≠ 0) :
    cmYToZOverlap (cmZToYOverlap p) = p :=
  cmYToZOverlap_inverse p hv

theorem cmYToZOverlap_equation (p : ℂ × ℂ) (hb : p.2 ≠ 0) :
    cmZPlaneEquation (cmYToZOverlap p) = -cmYPlaneEquation p / p.2 ^ 3 := by
  dsimp [cmZPlaneEquation, cmYPlaneEquation, cmYToZOverlap]
  field_simp [hb]
  <;> ring

theorem cmYToZOverlap_actual_source (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    cmZPlaneEquation (cmYToZOverlap p) = 0 := by
  rw [cmYToZOverlap_equation p hb, hp, neg_zero, zero_div]

/-- The declared tangent transport is the actual derivative along arbitrary
complex coordinate paths; the denominator hypothesis is retained. -/
theorem cmYToZOverlap_hasDerivAt (a b : ℂ → ℂ) (da db t : ℂ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hbt : b t ≠ 0) :
    HasDerivAt (fun s => cmYToZOverlap (a s, b s))
      (cmYToZOverlapTangent (a t, b t) (da, db)) t := by
  have hfirst := ha.div hb hbt
  have hsecond := (hasDerivAt_const t (1 : ℂ)).div hb hbt
  apply HasDerivAt.congr_deriv (HasDerivAt.prodMk hfirst hsecond)
  apply Prod.ext
  · dsimp [cmYToZOverlapTangent]
    congr 1
    ring
  · simp [cmYToZOverlapTangent]

/-- Complete off-curve residual; dropping the equation before transport would
leave this term in the first coordinate. -/
theorem cmYToZOverlap_tangent_residual (p : ℂ × ℂ) (hb : p.2 ≠ 0) :
    cmYToZOverlapTangent p (cmYTangentField p) =
      ((cmZTangentField (cmYToZOverlap p)).1 -
          3 * cmYPlaneEquation p / p.2 ^ 2,
        (cmZTangentField (cmYToZOverlap p)).2) := by
  apply Prod.ext <;>
    dsimp [cmYToZOverlapTangent, cmYTangentField, cmZTangentField,
      cmYToZOverlap, cmYPlaneEquation]
  · field_simp [hb]
    <;> ring
  · field_simp [hb]
    <;> ring

/-- The source equation cancels exactly the retained overlap residual. -/
theorem cmYToZOverlap_tangent_returns (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    cmYToZOverlapTangent p (cmYTangentField p) =
      cmZTangentField (cmYToZOverlap p) := by
  rw [cmYToZOverlap_tangent_residual p hb, hp]
  simp

theorem cmYToZOverlap_actual_action (p : ℂ × ℂ) (hb : p.2 ≠ 0) :
    cmYToZOverlap (cmYPlaneAction p) = cmZPlaneAction (cmYToZOverlap p) := by
  apply Prod.ext <;> dsimp [cmYToZOverlap, cmYPlaneAction, cmZPlaneAction]
  · field_simp [hb, Complex.I_ne_zero]
    <;> simp only [Complex.I_sq]
    <;> ring
  · field_simp [hb, Complex.I_ne_zero]
    <;> simp only [Complex.I_sq]
    <;> ring

/-- Differentiating the complete source equation retains the moving equation
multiplier. Both its source and tangent residuals remain explicit off the cubic. -/
theorem cmYToZOverlap_equationTangent_residual (p tangent : ℂ × ℂ) (hb : p.2 ≠ 0) :
    cmZEquationTangentReading (cmYToZOverlap p) (cmYToZOverlapTangent p tangent) =
      -cmYEquationTangentReading p tangent / p.2 ^ 3 +
        3 * cmYPlaneEquation p * tangent.2 / p.2 ^ 4 := by
  dsimp [cmZEquationTangentReading, cmYEquationTangentReading,
    cmYToZOverlap, cmYToZOverlapTangent, cmYPlaneEquation]
  field_simp [hb] <;> ring

/-- The overlap actually sends the whole source tangent kernel to the target
tangent kernel. A scalar field witness is not substituted for that population. -/
theorem cmYToZOverlap_tangentKernel_returns (p tangent : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0)
    (htangent : cmYEquationTangentReading p tangent = 0) :
    cmZEquationTangentReading (cmYToZOverlap p) (cmYToZOverlapTangent p tangent) = 0 := by
  rw [cmYToZOverlap_equationTangent_residual p tangent hb, hp, htangent]
  simp

theorem cmYTangentField_tangent (p : ℂ × ℂ) :
    cmYEquationTangentReading p (cmYTangentField p) = 0 := by
  dsimp [cmYEquationTangentReading, cmYTangentField]
  ring

theorem cmZTangentField_tangent (p : ℂ × ℂ) :
    cmZEquationTangentReading p (cmZTangentField p) = 0 := by
  dsimp [cmZEquationTangentReading, cmZTangentField]
  ring

/-- Consume the existing native derivative-cover identity on the plane receiver:
this field cannot vanish anywhere on the Y cubic. -/
theorem cmYTangentField_bezout (p : ℂ × ℂ) :
    (1 + p.1 * p.2) * (cmYTangentField p).1 -
      p.1 ^ 2 * (cmYTangentField p).2 + 3 * p.1 * cmYPlaneEquation p = 1 := by
  calc
    _ = 3 * p.1 * (p.1 ^ 3 - p.1 * p.2 ^ 2 - p.2) -
        p.1 ^ 2 * (3 * p.1 ^ 2 - p.2 ^ 2) -
        (1 + p.1 * p.2) * (-2 * p.1 * p.2 - 1) := by
      dsimp [cmYTangentField, cmYPlaneEquation]
      ring
    _ = 1 := yDerivative_polynomial_identity p.1 p.2

/-- The existing native Z derivative-cover identity retains its exact
denominator-free source; 4 = 2² is a field unit. -/
theorem cmZTangentField_bezout (p : ℂ × ℂ) :
    9 * p.1 * p.2 * (cmZTangentField p).1 +
      (4 - 6 * p.1 ^ 2) * (cmZTangentField p).2 +
      18 * p.1 * cmZPlaneEquation p = 4 := by
  calc
    _ = 18 * p.1 * (p.2 ^ 2 - p.1 ^ 3 + p.1) +
        (4 - 6 * p.1 ^ 2) * (1 - 3 * p.1 ^ 2) -
        9 * p.1 * p.2 * (2 * p.2) := by
      dsimp [cmZTangentField, cmZPlaneEquation]
      ring
    _ = 4 := zDerivative_polynomial_identity p.1 p.2

theorem cmYTangentField_ne_zero (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) :
    cmYTangentField p ≠ 0 := by
  intro hzero
  have h := cmYTangentField_bezout p
  rw [hzero, hp] at h
  norm_num at h

theorem cmZTangentField_ne_zero (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) :
    cmZTangentField p ≠ 0 := by
  intro hzero
  have h := cmZTangentField_bezout p
  rw [hzero, hp] at h
  norm_num at h

theorem cmYTangentField_actual_action (p : ℂ × ℂ) :
    cmYPlaneAction (cmYTangentField p) =
      Complex.I • cmYTangentField (cmYPlaneAction p) := by
  apply Prod.ext <;>
    simp [cmYPlaneAction, cmYTangentField, smul_eq_mul, mul_pow, Complex.I_sq]
  <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem cmZTangentField_actual_action (p : ℂ × ℂ) :
    cmZPlaneAction (cmZTangentField p) =
      Complex.I • cmZTangentField (cmZPlaneAction p) := by
  apply Prod.ext <;>
    simp [cmZPlaneAction, cmZTangentField, smul_eq_mul, mul_pow, Complex.I_sq]
  <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem cmYToZOverlapTangent_smul (p tangent : ℂ × ℂ) (coefficient : ℂ) :
    cmYToZOverlapTangent p (coefficient • tangent) =
      coefficient • cmYToZOverlapTangent p tangent := by
  apply Prod.ext <;> simp [cmYToZOverlapTangent, smul_eq_mul]
  <;> ring

theorem cmTangentClockReading_smul (field : ℂ × ℂ) (hfield : field ≠ 0)
    (coefficient : ℂ) :
    cmTangentClockReading field (coefficient • field) = coefficient := by
  by_cases hfirst : field.1 ≠ 0
  · simp [cmTangentClockReading, hfirst, smul_eq_mul]
  · have hsecond : field.2 ≠ 0 := by
      intro hzero
      apply hfield
      apply Prod.ext
      · exact not_not.mp hfirst
      · exact hzero
    simp [cmTangentClockReading, hfirst, hsecond, smul_eq_mul]

/-- The clock reads the complete tangent population, including the direction
where its first coordinate vanishes; it is not a chosen-source-only reading. -/
theorem cmTangentClockReading_reconstructs (field tangent : ℂ × ℂ)
    (hfield : field ≠ 0)
    (htangent : field.2 * tangent.1 - field.1 * tangent.2 = 0) :
    cmTangentClockReading field tangent • field = tangent := by
  by_cases hfirst : field.1 ≠ 0
  · have heq : field.2 * tangent.1 = field.1 * tangent.2 :=
      sub_eq_zero.mp htangent
    apply Prod.ext
    · simp [cmTangentClockReading, hfirst, smul_eq_mul]
    · change cmTangentClockReading field tangent * field.2 = tangent.2
      rw [cmTangentClockReading, if_pos hfirst, div_mul_eq_mul_div₀]
      apply (div_eq_iff hfirst).mpr
      simpa [mul_comm] using heq
  · have hfirstZero : field.1 = 0 := not_not.mp hfirst
    have hsecond : field.2 ≠ 0 := by
      intro hzero
      apply hfield
      apply Prod.ext
      · exact hfirstZero
      · exact hzero
    have hproduct : field.2 * tangent.1 = 0 := by
      simpa [hfirstZero] using htangent
    have htangentFirst : tangent.1 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hsecond
    apply Prod.ext <;>
      simp [cmTangentClockReading, hfirst, hfirstZero, hsecond,
        htangentFirst, smul_eq_mul]

theorem cmYTangentClockReading_reconstructs (p tangent : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0)
    (htangent : cmYEquationTangentReading p tangent = 0) :
    cmTangentClockReading (cmYTangentField p) tangent • cmYTangentField p = tangent := by
  apply cmTangentClockReading_reconstructs _ _ (cmYTangentField_ne_zero p hp)
  have hread : (cmYTangentField p).2 * tangent.1 -
      (cmYTangentField p).1 * tangent.2 = cmYEquationTangentReading p tangent := by
    dsimp [cmYTangentField, cmYEquationTangentReading]
    ring
  rw [hread]
  exact htangent

theorem cmZTangentClockReading_reconstructs (p tangent : ℂ × ℂ)
    (hp : cmZPlaneEquation p = 0)
    (htangent : cmZEquationTangentReading p tangent = 0) :
    cmTangentClockReading (cmZTangentField p) tangent • cmZTangentField p = tangent := by
  apply cmTangentClockReading_reconstructs _ _ (cmZTangentField_ne_zero p hp)
  have hread : (cmZTangentField p).2 * tangent.1 -
      (cmZTangentField p).1 * tangent.2 = cmZEquationTangentReading p tangent := by
    dsimp [cmZTangentField, cmZEquationTangentReading]
    ring
  rw [hread]
  exact htangent

/-- The consuming equation: restriction to the other actual cubic chart keeps
every carried complex tangent coefficient, rather than only its magnitude. -/
theorem cmActualCubic_tangentClock_overlap (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) (coefficient : ℂ) :
    cmTangentClockReading (cmZTangentField (cmYToZOverlap p))
      (cmYToZOverlapTangent p (coefficient • cmYTangentField p)) =
      cmTangentClockReading (cmYTangentField p) (coefficient • cmYTangentField p) := by
  rw [cmYToZOverlapTangent_smul, cmYToZOverlap_tangent_returns p hp hb]
  rw [cmTangentClockReading_smul _
    (cmZTangentField_ne_zero _ (cmYToZOverlap_actual_source p hp hb)),
    cmTangentClockReading_smul _ (cmYTangentField_ne_zero p hp)]

/-- The actual equation-kernel consumer: every tangent, not only a supplied
scalar multiple, returns the same clock reading through the source overlap. -/
theorem cmActualCubic_tangentClock_overlap_of_tangent (p tangent : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0)
    (htangent : cmYEquationTangentReading p tangent = 0) :
    cmTangentClockReading (cmZTangentField (cmYToZOverlap p))
      (cmYToZOverlapTangent p tangent) = cmTangentClockReading (cmYTangentField p) tangent := by
  have hcurrent := cmYTangentClockReading_reconstructs p tangent hp htangent
  calc
    _ = cmTangentClockReading (cmZTangentField (cmYToZOverlap p))
        (cmYToZOverlapTangent p
          (cmTangentClockReading (cmYTangentField p) tangent • cmYTangentField p)) := by
      rw [hcurrent]
    _ = cmTangentClockReading (cmYTangentField p)
        (cmTangentClockReading (cmYTangentField p) tangent • cmYTangentField p) :=
      cmActualCubic_tangentClock_overlap p hp hb _
    _ = _ := cmTangentClockReading_smul _ (cmYTangentField_ne_zero p hp) _

/-- A coordinate path carrying the source field actually carries the same
field, with the same coefficient, after restricting to the Z chart. -/
theorem cmActualCubic_tangentPath_overlap (a b : ℂ → ℂ) (t coefficient : ℂ)
    (hp : cmYPlaneEquation (a t, b t) = 0) (hb : b t ≠ 0)
    (ha : HasDerivAt a (coefficient * (cmYTangentField (a t, b t)).1) t)
    (hderivb : HasDerivAt b (coefficient * (cmYTangentField (a t, b t)).2) t) :
    HasDerivAt (fun s => cmYToZOverlap (a s, b s))
      (coefficient • cmZTangentField (cmYToZOverlap (a t, b t))) t := by
  have h := cmYToZOverlap_hasDerivAt a b _ _ t ha hderivb hb
  have hvelocity :
      (coefficient * (cmYTangentField (a t, b t)).1,
        coefficient * (cmYTangentField (a t, b t)).2) =
      coefficient • cmYTangentField (a t, b t) := by
    ext <;> simp [smul_eq_mul]
  rw [hvelocity, cmYToZOverlapTangent_smul,
    cmYToZOverlap_tangent_returns (a t, b t) hp hb] at h
  exact h

theorem cmActualCubic_tangentClock_Y_action (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (coefficient : ℂ) :
    cmTangentClockReading (cmYTangentField (cmYPlaneAction p))
      (coefficient • cmYPlaneAction (cmYTangentField p)) = Complex.I * coefficient := by
  rw [cmYTangentField_actual_action, smul_smul]
  rw [cmTangentClockReading_smul _ (cmYTangentField_ne_zero _
    (by rw [cmYPlaneEquation_action, hp, mul_zero]))]
  ring

theorem cmActualCubic_tangentClock_Z_action (p : ℂ × ℂ)
    (hp : cmZPlaneEquation p = 0) (coefficient : ℂ) :
    cmTangentClockReading (cmZTangentField (cmZPlaneAction p))
      (coefficient • cmZPlaneAction (cmZTangentField p)) = Complex.I * coefficient := by
  rw [cmZTangentField_actual_action, smul_smul]
  rw [cmTangentClockReading_smul _ (cmZTangentField_ne_zero _
    (by rw [cmZPlaneEquation_action, hp, neg_zero]))]
  ring

/-- The overlap source feeds the existing coordinate-ring receiver, with its
actual source coordinates. This does not assert equality of the two scheme
point maps before their geometric overlap inclusion has been constructed. -/
theorem cmActualCubic_overlap_receiver_coordinates (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    (cmZPlaneReceiver (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb) zU,
      cmZPlaneReceiver (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb) zV) =
      (cmYPlaneReceiver p hp yA / cmYPlaneReceiver p hp yB,
        1 / cmYPlaneReceiver p hp yB) := by
  simp [cmYToZOverlap]

/-- The new source restriction consumes the existing actual scheme-iota square.
No independent quarter-turn is installed in its place. -/
theorem cmActualCubic_overlap_point_actual_action (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    cmZPlanePoint (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb) ≫
        cubicIotaHom =
      cmZPlanePoint (cmYToZOverlap (cmYPlaneAction p))
        (cmYToZOverlap_actual_source (cmYPlaneAction p)
          (by rw [cmYPlaneEquation_action, hp, mul_zero])
          (by simpa [cmYPlaneAction] using mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hb)) := by
  have h := cmZPlanePoint_actual_action (cmYToZOverlap p)
    (cmYToZOverlap_actual_source p hp hb)
  have hpoint :
      cmZPlanePoint (cmZPlaneAction (cmYToZOverlap p))
        (by rw [cmZPlaneEquation_action, cmYToZOverlap_actual_source p hp hb, neg_zero]) =
      cmZPlanePoint (cmYToZOverlap (cmYPlaneAction p))
        (cmYToZOverlap_actual_source (cmYPlaneAction p)
          (by rw [cmYPlaneEquation_action, hp, mul_zero])
          (by simpa [cmYPlaneAction] using
            mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hb)) := by
    have hcongr : ∀ (q r : ℂ × ℂ) (hq : cmZPlaneEquation q = 0)
        (hr : cmZPlaneEquation r = 0), q = r → cmZPlanePoint q hq = cmZPlanePoint r hr := by
      intro q r hq hr hqr
      cases hqr
      rfl
    exact hcongr _ _ _ _ (cmYToZOverlap_actual_action p hb).symm
  exact h.trans hpoint

#print axioms cmYToZOverlap_inverse
#print axioms cmZToYOverlap_inverse
#print axioms cmYToZOverlap_equation
#print axioms cmYToZOverlap_actual_source
#print axioms cmYToZOverlap_hasDerivAt
#print axioms cmYToZOverlap_tangent_residual
#print axioms cmYToZOverlap_tangent_returns
#print axioms cmYToZOverlap_actual_action
#print axioms cmYToZOverlap_equationTangent_residual
#print axioms cmYToZOverlap_tangentKernel_returns
#print axioms cmYTangentField_tangent
#print axioms cmZTangentField_tangent
#print axioms cmYTangentField_bezout
#print axioms cmZTangentField_bezout
#print axioms cmYTangentField_ne_zero
#print axioms cmZTangentField_ne_zero
#print axioms cmYTangentField_actual_action
#print axioms cmZTangentField_actual_action
#print axioms cmYToZOverlapTangent_smul
#print axioms cmTangentClockReading_smul
#print axioms cmTangentClockReading_reconstructs
#print axioms cmYTangentClockReading_reconstructs
#print axioms cmZTangentClockReading_reconstructs
#print axioms cmActualCubic_tangentClock_overlap
#print axioms cmActualCubic_tangentClock_overlap_of_tangent
#print axioms cmActualCubic_tangentPath_overlap
#print axioms cmActualCubic_tangentClock_Y_action
#print axioms cmActualCubic_tangentClock_Z_action
#print axioms cmActualCubic_overlap_receiver_coordinates
#print axioms cmActualCubic_overlap_point_actual_action


/-! ## The same source overlap in the actual localized coordinate rings

These are localizations of the existing chart rings, not another curve model.
The universal properties retain the admitted denominator, source equation and
complex coefficient map. The induced Spec comparison is affine-overlap data;
its equality with the original Proj chart-inclusion restrictions remains owed.
-/

abbrev CMYOverlapRing := Localization.Away yB
abbrev CMZOverlapRing := Localization.Away zV

def cmYOverlapBase : YChartCubicRing →+* CMYOverlapRing := algebraMap _ _
def cmZOverlapBase : ZChartSquareRing →+* CMZOverlapRing := algebraMap _ _
def cmYOverlapScalar : ℂ →+* CMYOverlapRing := cmYOverlapBase.comp (algebraMap ℂ _)
def cmZOverlapScalar : ℂ →+* CMZOverlapRing := cmZOverlapBase.comp (algebraMap ℂ _)
def cmYOverlapInverse : CMYOverlapRing := IsLocalization.Away.invSelf yB
def cmZOverlapInverse : CMZOverlapRing := IsLocalization.Away.invSelf zV

@[simp] theorem cmYOverlap_inverse_unit : cmYOverlapBase yB * cmYOverlapInverse = 1 :=
  IsLocalization.Away.mul_invSelf yB
@[simp] theorem cmZOverlap_inverse_unit : cmZOverlapBase zV * cmZOverlapInverse = 1 :=
  IsLocalization.Away.mul_invSelf zV

/-- The source polynomial identities hold in arbitrary rings receiving a unit
denominator; no division operation or field assumption is installed in them. -/
theorem cmOverlap_Y_source_of_Z {R : Type*} [CommRing R] (U V inverse : R)
    (hsource : V ^ 2 - U ^ 3 + U = 0) (hunit : V * inverse = 1) :
    (U * inverse) ^ 3 - (U * inverse) * inverse ^ 2 - inverse = 0 := by
  have hzero : U ^ 3 - U - V ^ 2 = 0 := by
    calc
      _ = -(V ^ 2 - U ^ 3 + U) := by ring
      _ = 0 := by rw [hsource, neg_zero]
  calc
    _ = inverse ^ 3 * (U ^ 3 - U - V ^ 2) +
        inverse * ((V * inverse) ^ 2 - 1) := by ring
    _ = 0 := by rw [hzero, hunit]; ring

theorem cmOverlap_Z_source_of_Y {R : Type*} [CommRing R] (A B inverse : R)
    (hsource : A ^ 3 - A * B ^ 2 - B = 0) (hunit : B * inverse = 1) :
    inverse ^ 2 - (A * inverse) ^ 3 + A * inverse = 0 := by
  calc
    _ = -inverse ^ 3 * (A ^ 3 - A * B ^ 2 - B) +
        A * inverse * (1 - (B * inverse) ^ 2) +
        inverse ^ 2 * (1 - B * inverse) := by ring
    _ = 0 := by rw [hsource, hunit]; ring

theorem cmYOverlap_source_relation :
    (cmYOverlapBase yA) ^ 3 - cmYOverlapBase yA * (cmYOverlapBase yB) ^ 2 -
      cmYOverlapBase yB = 0 := by
  have h : yA ^ 3 - yA * yB ^ 2 - yB = 0 := yDerivative_source_relation
  have hm := congrArg cmYOverlapBase h
  simpa only [map_sub, map_mul, map_pow, map_zero] using hm

theorem cmZOverlap_source_relation :
    (cmZOverlapBase zV) ^ 2 - (cmZOverlapBase zU) ^ 3 + cmZOverlapBase zU = 0 := by
  have h : zV ^ 2 - zU ^ 3 + zU = 0 := by
    have hc : zV ^ 2 = zU ^ 3 - zU := curve_relation
    rw [hc]
    ring
  have hm := congrArg cmZOverlapBase h
  simpa only [map_add, map_sub, map_pow, map_zero] using hm

/-- Pull Y-chart coordinates into the Z overlap. -/
def cmYOverlapCoordinates : CMZOverlapRing × CMZOverlapRing :=
  (cmZOverlapBase zU * cmZOverlapInverse, cmZOverlapInverse)

/-- Pull Z-chart coordinates into the Y overlap. -/
def cmZOverlapCoordinates : CMYOverlapRing × CMYOverlapRing :=
  (cmYOverlapBase yA * cmYOverlapInverse, cmYOverlapInverse)

theorem cmYOverlapCoordinates_source :
    yMonicCubic.eval₂
      (Polynomial.eval₂RingHom cmZOverlapScalar cmYOverlapCoordinates.2)
      cmYOverlapCoordinates.1 = 0 := by
  have h := cmOverlap_Y_source_of_Z (cmZOverlapBase zU) (cmZOverlapBase zV)
    cmZOverlapInverse cmZOverlap_source_relation cmZOverlap_inverse_unit
  have hx :
      (Polynomial.eval₂RingHom cmZOverlapScalar cmYOverlapCoordinates.2) X =
        cmYOverlapCoordinates.2 := eval₂_X _ _
  simp only [yMonicCubic, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    map_pow, hx]
  simpa only [cmYOverlapCoordinates, mul_comm] using h

theorem cmZOverlapCoordinates_source :
    squareCurve.toAffine.polynomial.eval₂
      (Polynomial.eval₂RingHom cmYOverlapScalar cmZOverlapCoordinates.1)
      cmZOverlapCoordinates.2 = 0 := by
  have h := cmOverlap_Z_source_of_Y (cmYOverlapBase yA) (cmYOverlapBase yB)
    cmYOverlapInverse cmYOverlap_source_relation cmYOverlap_inverse_unit
  have hx :
      (Polynomial.eval₂RingHom cmYOverlapScalar cmZOverlapCoordinates.1) X =
        cmZOverlapCoordinates.1 := eval₂_X _ _
  rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, map_sub, map_pow, hx]
  calc
    _ = cmYOverlapInverse ^ 2 -
        (cmYOverlapBase yA * cmYOverlapInverse) ^ 3 +
        cmYOverlapBase yA * cmYOverlapInverse := by
      dsimp only [cmZOverlapCoordinates]
      ring
    _ = 0 := h

def cmYChartToZOverlap : YChartCubicRing →+* CMZOverlapRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom cmZOverlapScalar cmYOverlapCoordinates.2)
    cmYOverlapCoordinates.1 cmYOverlapCoordinates_source

def cmZChartToYOverlap : ZChartSquareRing →+* CMYOverlapRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom cmYOverlapScalar cmZOverlapCoordinates.1)
    cmZOverlapCoordinates.2 cmZOverlapCoordinates_source

@[simp] theorem cmYChartToZOverlap_a :
    cmYChartToZOverlap yA = cmZOverlapBase zU * cmZOverlapInverse := by
  rw [cmYChartToZOverlap, AdjoinRoot.lift_root]
  rfl
@[simp] theorem cmYChartToZOverlap_b : cmYChartToZOverlap yB = cmZOverlapInverse := by
  change cmYChartToZOverlap (AdjoinRoot.of yMonicCubic X) = _
  rw [cmYChartToZOverlap, AdjoinRoot.lift_of]
  simp [cmYOverlapCoordinates]
@[simp] theorem cmZChartToYOverlap_u :
    cmZChartToYOverlap zU = cmYOverlapBase yA * cmYOverlapInverse := by
  change cmZChartToYOverlap (AdjoinRoot.of squareCurve.toAffine.polynomial X) = _
  rw [cmZChartToYOverlap, AdjoinRoot.lift_of]
  simp [cmZOverlapCoordinates]
@[simp] theorem cmZChartToYOverlap_v : cmZChartToYOverlap zV = cmYOverlapInverse := by
  rw [cmZChartToYOverlap, AdjoinRoot.lift_root]
  rfl

@[simp] theorem cmYChartToZOverlap_scalar (c : ℂ) :
    cmYChartToZOverlap (algebraMap ℂ YChartCubicRing c) = cmZOverlapScalar c := by
  change cmYChartToZOverlap (AdjoinRoot.of yMonicCubic (C c)) = _
  rw [cmYChartToZOverlap, AdjoinRoot.lift_of]
  simp
@[simp] theorem cmZChartToYOverlap_scalar (c : ℂ) :
    cmZChartToYOverlap (algebraMap ℂ ZChartSquareRing c) = cmYOverlapScalar c := by
  change cmZChartToYOverlap (AdjoinRoot.of squareCurve.toAffine.polynomial (C c)) = _
  rw [cmZChartToYOverlap, AdjoinRoot.lift_of]
  simp

theorem cmYChartToZOverlap_denominator_unit : IsUnit (cmYChartToZOverlap yB) := by
  rw [cmYChartToZOverlap_b]
  exact IsUnit.of_mul_eq_one (cmZOverlapBase zV)
    (by rw [mul_comm, cmZOverlap_inverse_unit])
theorem cmZChartToYOverlap_denominator_unit : IsUnit (cmZChartToYOverlap zV) := by
  rw [cmZChartToYOverlap_v]
  exact IsUnit.of_mul_eq_one (cmYOverlapBase yB)
    (by rw [mul_comm, cmYOverlap_inverse_unit])

def cmYOverlapToZOverlap : CMYOverlapRing →+* CMZOverlapRing :=
  IsLocalization.Away.lift yB (g := cmYChartToZOverlap) cmYChartToZOverlap_denominator_unit
def cmZOverlapToYOverlap : CMZOverlapRing →+* CMYOverlapRing :=
  IsLocalization.Away.lift zV (g := cmZChartToYOverlap) cmZChartToYOverlap_denominator_unit

@[simp] theorem cmYOverlapToZOverlap_base (r : YChartCubicRing) :
    cmYOverlapToZOverlap (cmYOverlapBase r) = cmYChartToZOverlap r :=
  IsLocalization.Away.lift_eq yB cmYChartToZOverlap_denominator_unit r
@[simp] theorem cmZOverlapToYOverlap_base (r : ZChartSquareRing) :
    cmZOverlapToYOverlap (cmZOverlapBase r) = cmZChartToYOverlap r :=
  IsLocalization.Away.lift_eq zV cmZChartToYOverlap_denominator_unit r

@[simp] theorem cmYOverlapToZOverlap_inverse :
    cmYOverlapToZOverlap cmYOverlapInverse = cmZOverlapBase zV := by
  have h := congrArg cmYOverlapToZOverlap cmYOverlap_inverse_unit
  simp only [map_mul, map_one, cmYOverlapToZOverlap_base, cmYChartToZOverlap_b] at h
  have hu : IsUnit cmZOverlapInverse := IsUnit.of_mul_eq_one (cmZOverlapBase zV)
    (by rw [mul_comm, cmZOverlap_inverse_unit])
  apply hu.mul_left_cancel
  rw [h, mul_comm cmZOverlapInverse (cmZOverlapBase zV), cmZOverlap_inverse_unit]

@[simp] theorem cmZOverlapToYOverlap_inverse :
    cmZOverlapToYOverlap cmZOverlapInverse = cmYOverlapBase yB := by
  have h := congrArg cmZOverlapToYOverlap cmZOverlap_inverse_unit
  simp only [map_mul, map_one, cmZOverlapToYOverlap_base, cmZChartToYOverlap_v] at h
  have hu : IsUnit cmYOverlapInverse := IsUnit.of_mul_eq_one (cmYOverlapBase yB)
    (by rw [mul_comm, cmYOverlap_inverse_unit])
  apply hu.mul_left_cancel
  rw [h, mul_comm cmYOverlapInverse (cmYOverlapBase yB), cmYOverlap_inverse_unit]

/-- The complex coefficient maps also commute through the localized overlap. -/
@[simp] theorem cmYOverlapToZOverlap_scalar (c : ℂ) :
    cmYOverlapToZOverlap (cmYOverlapScalar c) = cmZOverlapScalar c := by
  change cmYOverlapToZOverlap (cmYOverlapBase (algebraMap ℂ YChartCubicRing c)) = _
  simp
@[simp] theorem cmZOverlapToYOverlap_scalar (c : ℂ) :
    cmZOverlapToYOverlap (cmZOverlapScalar c) = cmYOverlapScalar c := by
  change cmZOverlapToYOverlap (cmZOverlapBase (algebraMap ℂ ZChartSquareRing c)) = _
  simp

theorem cmYOverlap_roundtrip :
    cmZOverlapToYOverlap.comp cmYOverlapToZOverlap = RingHom.id CMYOverlapRing := by
  apply IsLocalization.ringHom_ext (Submonoid.powers yB)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change cmZOverlapToYOverlap
        (cmYOverlapToZOverlap (cmYOverlapScalar c)) = cmYOverlapScalar c
      simp
    · change cmZOverlapToYOverlap
        (cmYOverlapToZOverlap (cmYOverlapBase yB)) = cmYOverlapBase yB
      simp
  · change cmZOverlapToYOverlap
      (cmYOverlapToZOverlap (cmYOverlapBase yA)) = cmYOverlapBase yA
    simp only [cmYOverlapToZOverlap_base, cmYChartToZOverlap_a, map_mul,
      cmZOverlapToYOverlap_base, cmZChartToYOverlap_u, cmZOverlapToYOverlap_inverse]
    rw [mul_assoc, mul_comm cmYOverlapInverse (cmYOverlapBase yB),
      cmYOverlap_inverse_unit, mul_one]

theorem cmZOverlap_roundtrip :
    cmYOverlapToZOverlap.comp cmZOverlapToYOverlap = RingHom.id CMZOverlapRing := by
  apply IsLocalization.ringHom_ext (Submonoid.powers zV)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change cmYOverlapToZOverlap
        (cmZOverlapToYOverlap (cmZOverlapScalar c)) = cmZOverlapScalar c
      simp
    · change cmYOverlapToZOverlap
        (cmZOverlapToYOverlap (cmZOverlapBase zU)) = cmZOverlapBase zU
      simp only [cmZOverlapToYOverlap_base, cmZChartToYOverlap_u, map_mul,
        cmYOverlapToZOverlap_base, cmYChartToZOverlap_a, cmYOverlapToZOverlap_inverse]
      rw [mul_assoc, mul_comm cmZOverlapInverse (cmZOverlapBase zV),
        cmZOverlap_inverse_unit, mul_one]
  · change cmYOverlapToZOverlap
      (cmZOverlapToYOverlap (cmZOverlapBase zV)) = cmZOverlapBase zV
    simp

def cmActualCubicOverlapRingEquiv : CMYOverlapRing ≃+* CMZOverlapRing :=
  RingEquiv.ofRingHom cmYOverlapToZOverlap cmZOverlapToYOverlap
    cmZOverlap_roundtrip cmYOverlap_roundtrip

def cmYOverlapReceiver (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    CMYOverlapRing →+* ℂ :=
  IsLocalization.Away.lift yB (g := (cmYPlaneReceiver p hp).toRingHom)
    (by simpa using (isUnit_iff_ne_zero.mpr hb : IsUnit p.2))

def cmZOverlapReceiver (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0) (hv : p.2 ≠ 0) :
    CMZOverlapRing →+* ℂ :=
  IsLocalization.Away.lift zV (g := (cmZPlaneReceiver p hp).toRingHom)
    (by simpa using (isUnit_iff_ne_zero.mpr hv : IsUnit p.2))

@[simp] theorem cmYOverlapReceiver_base (p : ℂ × ℂ) (hp : cmYPlaneEquation p = 0)
    (hb : p.2 ≠ 0) (r : YChartCubicRing) :
    cmYOverlapReceiver p hp hb (cmYOverlapBase r) = cmYPlaneReceiver p hp r :=
  IsLocalization.Away.lift_eq yB _ r
@[simp] theorem cmZOverlapReceiver_base (p : ℂ × ℂ) (hp : cmZPlaneEquation p = 0)
    (hv : p.2 ≠ 0) (r : ZChartSquareRing) :
    cmZOverlapReceiver p hp hv (cmZOverlapBase r) = cmZPlaneReceiver p hp r :=
  IsLocalization.Away.lift_eq zV _ r

@[simp] theorem cmYOverlapReceiver_scalar (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) (c : ℂ) :
    cmYOverlapReceiver p hp hb (cmYOverlapScalar c) = c := by
  change cmYOverlapReceiver p hp hb
    (cmYOverlapBase (algebraMap ℂ YChartCubicRing c)) = c
  rw [cmYOverlapReceiver_base, AlgHom.commutes]
  exact Algebra.algebraMap_self_apply c

@[simp] theorem cmZOverlapReceiver_scalar (p : ℂ × ℂ)
    (hp : cmZPlaneEquation p = 0) (hv : p.2 ≠ 0) (c : ℂ) :
    cmZOverlapReceiver p hp hv (cmZOverlapScalar c) = c := by
  change cmZOverlapReceiver p hp hv
    (cmZOverlapBase (algebraMap ℂ ZChartSquareRing c)) = c
  rw [cmZOverlapReceiver_base, AlgHom.commutes]
  exact Algebra.algebraMap_self_apply c

@[simp] theorem cmYOverlapReceiver_inverse (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    cmYOverlapReceiver p hp hb cmYOverlapInverse = 1 / p.2 := by
  have h := congrArg (cmYOverlapReceiver p hp hb) cmYOverlap_inverse_unit
  simp only [map_mul, map_one, cmYOverlapReceiver_base, cmYPlaneReceiver_b] at h
  apply (isUnit_iff_ne_zero.mpr hb).mul_left_cancel
  rw [h, mul_one_div_cancel hb]

@[simp] theorem cmZOverlapReceiver_inverse (p : ℂ × ℂ)
    (hp : cmZPlaneEquation p = 0) (hv : p.2 ≠ 0) :
    cmZOverlapReceiver p hp hv cmZOverlapInverse = 1 / p.2 := by
  have h := congrArg (cmZOverlapReceiver p hp hv) cmZOverlap_inverse_unit
  simp only [map_mul, map_one, cmZOverlapReceiver_base, cmZPlaneReceiver_v] at h
  apply (isUnit_iff_ne_zero.mpr hv).mul_left_cancel
  rw [h, mul_one_div_cancel hv]

/-- Every function on the localized Y source returns the same reading after
the constructed ring transition; this is not just a coordinate-pair test. -/
theorem cmActualCubicOverlap_evaluation_square (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    (cmZOverlapReceiver (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb)
      (by simp [cmYToZOverlap, hb])).comp cmYOverlapToZOverlap =
      cmYOverlapReceiver p hp hb := by
  let q : ℂ × ℂ := cmYToZOverlap p
  have hq : cmZPlaneEquation q = 0 := cmYToZOverlap_actual_source p hp hb
  have hv : q.2 ≠ 0 := by
    dsimp only [q, cmYToZOverlap]
    exact one_div_ne_zero hb
  change (cmZOverlapReceiver q hq hv).comp cmYOverlapToZOverlap =
    cmYOverlapReceiver p hp hb
  apply IsLocalization.ringHom_ext (Submonoid.powers yB)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change cmZOverlapReceiver q hq hv (cmYOverlapToZOverlap (cmYOverlapScalar c)) =
        cmYOverlapReceiver p hp hb (cmYOverlapScalar c)
      rw [cmYOverlapToZOverlap_scalar, cmZOverlapReceiver_scalar,
        cmYOverlapReceiver_scalar]
    · change cmZOverlapReceiver q hq hv
        (cmYOverlapToZOverlap (cmYOverlapBase yB)) =
        cmYOverlapReceiver p hp hb (cmYOverlapBase yB)
      simp only [cmYOverlapToZOverlap_base, cmYChartToZOverlap_b,
        cmZOverlapReceiver_inverse, cmYOverlapReceiver_base, cmYPlaneReceiver_b]
      change 1 / (1 / p.2) = p.2
      exact one_div_one_div
  · change cmZOverlapReceiver q hq hv
      (cmYOverlapToZOverlap (cmYOverlapBase yA)) =
      cmYOverlapReceiver p hp hb (cmYOverlapBase yA)
    simp only [cmYOverlapToZOverlap_base, cmYChartToZOverlap_a, map_mul,
      cmZOverlapReceiver_base, cmZPlaneReceiver_u, cmZOverlapReceiver_inverse,
      cmYOverlapReceiver_base, cmYPlaneReceiver_a]
    change (p.1 / p.2) * (1 / (1 / p.2)) = p.1
    rw [one_div_one_div]
    exact div_mul_cancel₀ p.1 hb

/-- The all-function receiver equation is consumed contravariantly by the
actual affine Spec transition, without identifying the two Proj inclusions. -/
theorem cmActualCubicOverlap_spec_evaluation_square (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    Spec.map (CommRingCat.ofHom
        (cmZOverlapReceiver (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb)
          (by simp [cmYToZOverlap, hb]))) ≫
      Spec.map (CommRingCat.ofHom cmYOverlapToZOverlap) =
        Spec.map (CommRingCat.ofHom (cmYOverlapReceiver p hp hb)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((cmZOverlapReceiver (cmYToZOverlap p) (cmYToZOverlap_actual_source p hp hb)
      (by simp [cmYToZOverlap, hb])).comp cmYOverlapToZOverlap)) = _
  rw [cmActualCubicOverlap_evaluation_square]

/-- The localized point returns the existing actual Y point under its source
inclusion. No separate equation-to-scheme evaluation is assumed. -/
theorem cmYOverlapReceiver_actual_point (p : ℂ × ℂ)
    (hp : cmYPlaneEquation p = 0) (hb : p.2 ≠ 0) :
    Spec.map (CommRingCat.ofHom (cmYOverlapReceiver p hp hb)) ≫
        Spec.map (CommRingCat.ofHom cmYOverlapBase) ≫ yCurveChartInclusion =
      cmYPlanePoint p hp := by
  have h : (cmYOverlapReceiver p hp hb).comp cmYOverlapBase =
      (cmYPlaneReceiver p hp).toRingHom := by
    apply RingHom.ext
    intro r
    exact cmYOverlapReceiver_base p hp hb r
  rw [← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((cmYOverlapReceiver p hp hb).comp cmYOverlapBase)) ≫
    yCurveChartInclusion = _
  rw [h]
  rfl

theorem cmZOverlapReceiver_actual_point (p : ℂ × ℂ)
    (hp : cmZPlaneEquation p = 0) (hv : p.2 ≠ 0) :
    Spec.map (CommRingCat.ofHom (cmZOverlapReceiver p hp hv)) ≫
        Spec.map (CommRingCat.ofHom cmZOverlapBase) ≫ zCurveChartInclusion =
      cmZPlanePoint p hp := by
  have h : (cmZOverlapReceiver p hp hv).comp cmZOverlapBase =
      (cmZPlaneReceiver p hp).toRingHom := by
    apply RingHom.ext
    intro r
    exact cmZOverlapReceiver_base p hp hv r
  rw [← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((cmZOverlapReceiver p hp hv).comp cmZOverlapBase)) ≫
    zCurveChartInclusion = _
  rw [h]
  rfl

#print axioms cmOverlap_Y_source_of_Z
#print axioms cmOverlap_Z_source_of_Y
#print axioms cmYOverlapCoordinates_source
#print axioms cmZOverlapCoordinates_source
#print axioms cmYOverlap_roundtrip
#print axioms cmZOverlap_roundtrip
#print axioms cmActualCubicOverlapRingEquiv
#print axioms cmActualCubicOverlap_evaluation_square
#print axioms cmActualCubicOverlap_spec_evaluation_square
#print axioms cmYOverlapReceiver_actual_point
#print axioms cmZOverlapReceiver_actual_point


end Holonics.Hodge.CMGraphSource
