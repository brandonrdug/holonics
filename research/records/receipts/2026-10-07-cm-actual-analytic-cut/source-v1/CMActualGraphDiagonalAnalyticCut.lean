import CMActualFiniteCutCyclePushforward
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
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
open scoped Topology

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
  simp only [cmYPlaneEquation, cmYPlaneAction, mul_pow, neg_pow,
    Complex.I_sq, cmI_cube]
  ring

theorem cmZPlaneEquation_action (p : ℂ × ℂ) :
    cmZPlaneEquation (cmZPlaneAction p) = -cmZPlaneEquation p := by
  simp only [cmZPlaneEquation, cmZPlaneAction, mul_pow, neg_pow, Complex.I_sq]
  ring

theorem cmYPlaneEquation_eval (p : ℂ × ℂ) :
    yMonicCubic.eval₂ (aeval p.2) p.1 = cmYPlaneEquation p := by
  simp only [yMonicCubic, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C,
    eval₂_X, map_pow, aeval_X]
  unfold cmYPlaneEquation
  ring

theorem cmZPlaneEquation_eval (p : ℂ × ℂ) :
    squareCurve.toAffine.polynomial.eval₂ (aeval p.1) p.2 = cmZPlaneEquation p := by
  rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, map_sub, map_pow, aeval_X]
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
    simpa [cmYPlaneEquation] using ((ha.pow 3).sub (ha.mul (hb.pow 2))).sub hb
  convert ha.prodMk hP using 1
  ext p <;> simp [cmYParameterEquation, cmYParameterDerivative]

theorem cmZParameterEquation_derivative :
    HasStrictFDerivAt cmZParameterEquation
      (cmZParameterDerivative : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := by
  have hu : HasStrictFDerivAt (fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := hasStrictFDerivAt_fst
  have hv : HasStrictFDerivAt (fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := hasStrictFDerivAt_snd
  have hP : HasStrictFDerivAt cmZPlaneEquation
      (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
    simpa [cmZPlaneEquation] using ((hv.pow 2).sub (hu.pow 3)).add hu
  convert hv.prodMk hP using 1
  ext p <;> simp [cmZParameterEquation, cmZParameterDerivative]

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
  have hi := hs.to_localInverse cmYParameterEquation_derivative.hasFDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi0 : ContDiffAt ℂ ∞ (hs.localInverse
      cmYParameterEquation_derivative.hasFDerivAt (by simp)) 0 := by
    simpa [cmYParameterEquation, cmYPlaneEquation] using hi
  have he : ContDiffAt ℂ ∞ (fun t : ℂ => (t, (0 : ℂ))) 0 := by fun_prop
  simpa [ContDiffAt.localInverse, cmYAnalyticGerm] using hi0.comp 0 he

theorem cmZAnalyticGerm_contDiff : ContDiffAt ℂ ∞ cmZAnalyticGerm 0 := by
  have hs : ContDiffAt ℂ ∞ cmZParameterEquation 0 := by
    unfold cmZParameterEquation cmZPlaneEquation
    fun_prop
  have hi := hs.to_localInverse cmZParameterEquation_derivative.hasFDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi0 : ContDiffAt ℂ ∞ (hs.localInverse
      cmZParameterEquation_derivative.hasFDerivAt (by simp)) 0 := by
    simpa [cmZParameterEquation, cmZPlaneEquation] using hi
  have he : ContDiffAt ℂ ∞ (fun t : ℂ => (t, (0 : ℂ))) 0 := by fun_prop
  simpa [ContDiffAt.localInverse, cmZAnalyticGerm] using hi0.comp 0 he

theorem cmYAnalyticGerm_coordinates :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmYAnalyticGerm t).1 = t ∧ cmYPlaneEquation (cmYAnalyticGerm t) = 0 := by
  have he : Tendsto (fun t : ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    fun_prop
  have hr : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      cmYParameterEquation (cmYParameterEquation_derivative.localInverse
        cmYParameterEquation cmYParameterDerivative 0 p) = p := by
    simpa [cmYParameterEquation, cmYPlaneEquation] using
      cmYParameterEquation_derivative.eventually_right_inverse
  have hi := he.eventually hr
  simpa only [cmYParameterEquation, cmYAnalyticGerm, Prod.mk.injEq] using hi

theorem cmZAnalyticGerm_coordinates :
    ∀ᶠ t : ℂ in 𝓝 0,
      (cmZAnalyticGerm t).2 = t ∧ cmZPlaneEquation (cmZAnalyticGerm t) = 0 := by
  have he : Tendsto (fun t : ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    fun_prop
  have hr : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      cmZParameterEquation (cmZParameterEquation_derivative.localInverse
        cmZParameterEquation cmZParameterDerivative 0 p) = p := by
    simpa [cmZParameterEquation, cmZPlaneEquation] using
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
    simpa [cmYPlaneAction] using hT.tendsto
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
    simpa [cmZPlaneAction] using hT.tendsto
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
  have hd : HasDerivAt cmGraphDiagonalNormal (Complex.I - 1) t := by
    simpa [cmGraphDiagonalNormal] using (hasDerivAt_id t).const_mul (Complex.I - 1)
  exact hd.deriv

theorem cmYActualNormal_deriv :
    deriv cmYActualNormal =ᶠ[𝓝 0] fun _ => Complex.I - 1 := by
  simpa only [cmGraphDiagonalNormal_deriv] using cmYActualNormal_eq_model.deriv

theorem cmZActualNormal_deriv :
    deriv cmZActualNormal =ᶠ[𝓝 0] fun _ => Complex.I - 1 := by
  simpa only [cmGraphDiagonalNormal_deriv] using cmZActualNormal_eq_model.deriv

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

end Holonics.Hodge.CMGraphSource
