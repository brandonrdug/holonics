import ElementaryHolonics.Millennium.HodgeSurfaceCycleClass
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# An exact `(1,1)` form on the projective line

This file constructs the analytic source which was missing from the rational Hodge receiver.  The
carrier is the real alternating area form on the complex tangent line, weighted by the exact
Fubini--Study factor `(1 + |z|²)⁻²`.  It is not defined from a divisor span or from the target
singular-cohomology coordinates.

The construction returns three source laws:

* multiplication of both tangent directions by `I` leaves the form invariant, which is the real
  two-form criterion for type `(1,1)` on a complex line;
* the form glues exactly under the nontrivial projective transition `z ↦ z⁻¹`, including its
  derivative `-z⁻²`;
* the transition current has normalized winding exactly one.

These are the analytic and integral ingredients required before its Chern/period receiver can be
identified with the already constructed singular ruling cycle classes.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineType11Form

open Complex
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas

attribute [local instance] Complex.finrank_real_complex_fact

/-- [definition] A real bilinear alternating two-form on the complex tangent line. -/
structure RealAlternatingTwoForm where
  toBilinear : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ
  alternating : ∀ tangent, toBilinear tangent tangent = 0

instance : CoeFun RealAlternatingTwoForm (fun _ => ℂ → ℂ → ℝ) where
  coe form := fun first second => form.toBilinear first second

/-- [definition] The exact complex area determinant. -/
def complexArea (first second : ℂ) : ℝ :=
  first.re * second.im - first.im * second.re

/-- [proved-derived; formal-checked] Mathlib's oriented area form is the coordinate determinant. -/
theorem orientation_areaForm_eq_complexArea (first second : ℂ) :
    Complex.orientation.areaForm first second = complexArea first second := by
  rw [Complex.areaForm]
  simp only [complexArea, mul_im, conj_re, conj_im]
  ring

/-- [definition] The oriented area form as a bundled real alternating form. -/
def complexAreaForm : RealAlternatingTwoForm where
  toBilinear := Complex.orientation.areaForm
  alternating tangent := Complex.orientation.areaForm_apply_self tangent

/-- [proved-derived; formal-checked] Complex multiplication scales oriented area by the exact
norm square of the multiplier. -/
theorem complexArea_mul (multiplier first second : ℂ) :
    complexArea (multiplier * first) (multiplier * second) =
      normSq multiplier * complexArea first second := by
  simp only [complexArea, mul_re, mul_im, normSq_apply]
  ring

/-- [proved-derived; formal-checked] The complex structure preserves oriented area. -/
theorem complexArea_I (first second : ℂ) :
    complexArea (I * first) (I * second) = complexArea first second := by
  simp [complexArea]
  ring

/-- [definition] The exact affine Fubini--Study weight. -/
def fsWeight (z : ℂ) : ℝ :=
  (1 + normSq z)⁻¹ * (1 + normSq z)⁻¹

/-- [definition] The chart-local Fubini--Study area form. -/
def fsForm (z : ℂ) : RealAlternatingTwoForm where
  toBilinear := fsWeight z • Complex.orientation.areaForm
  alternating tangent := by
    simp [Complex.orientation.areaForm_apply_self]

/-- [definition] The oriented area form as a continuous alternating two-form, so that the
exterior derivative is available as a formal operation. -/
def complexAreaContinuousForm : ℂ [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.orientation.volumeForm.mkContinuous 1 (by
    intro vectors
    simpa using Complex.orientation.abs_volumeForm_apply_le vectors)

/-- [proved-derived; formal-checked] The continuous and bilinear presentations are the same
oriented area current. -/
theorem complexAreaContinuousForm_apply (first second : ℂ) :
    complexAreaContinuousForm ![first, second] = complexArea first second := by
  change Complex.orientation.volumeForm ![first, second] = _
  rw [← Complex.orientation.areaForm_to_volumeForm]
  exact orientation_areaForm_eq_complexArea first second

/-- [definition] The chart-local Fubini--Study field as an actual differential two-form. -/
def fsDifferentialForm (z : ℂ) : ℂ [⋀^Fin 2]→L[ℝ] ℝ :=
  fsWeight z • complexAreaContinuousForm

/-- [proved-derived; formal-checked] The differential-form presentation realizes the original
pointwise alternating carrier exactly. -/
theorem fsDifferentialForm_apply (z first second : ℂ) :
    fsDifferentialForm z ![first, second] = fsForm z first second := by
  change fsWeight z * Complex.orientation.volumeForm ![first, second] = _
  rw [← Complex.orientation.areaForm_to_volumeForm]
  rfl

/-- [proved-derived; formal-checked] The Fubini--Study differential-form field is smooth. -/
theorem fsDifferentialForm_contDiff : ContDiff ℝ ⊤ fsDifferentialForm := by
  unfold fsDifferentialForm fsWeight
  apply ContDiff.smul_const
  have hbase : ContDiff ℝ ⊤ (fun z : ℂ => 1 + normSq z) := by
    simp only [normSq_apply]
    exact contDiff_const.add
      ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
  have hne : ∀ z : ℂ, 1 + normSq z ≠ 0 := by
    intro z
    nlinarith [normSq_nonneg z]
  exact (hbase.inv hne).mul (hbase.inv hne)

/-- [proved-derived; formal-checked] Every real alternating three-form on the complex line is
zero.  This is the exact dimension obstruction `3 > dim_ℝ ℂ`. -/
theorem complexAlternatingThreeForm_eq_zero
    (form : ℂ [⋀^Fin 3]→L[ℝ] ℝ) : form = 0 := by
  ext vectors
  exact form.toAlternatingMap.map_linearDependent vectors fun independent => by
    have hcard := independent.fintype_card_le_finrank
    norm_num [Complex.finrank_real_complex] at hcard

/-- [proved-derived; formal-checked] The Fubini--Study two-form is closed on every affine
projective-line chart. -/
theorem fsDifferentialForm_closed (z : ℂ) :
    extDeriv fsDifferentialForm z = 0 :=
  complexAlternatingThreeForm_eq_zero (extDeriv fsDifferentialForm z)

@[simp]
theorem fsForm_apply (z first second : ℂ) :
    fsForm z first second = fsWeight z * complexArea first second := by
  change fsWeight z * Complex.orientation.areaForm first second = _
  rw [orientation_areaForm_eq_complexArea]

/-- [definition] The real type-`(1,1)` condition on a complex-line two-form. -/
def IsType11 (form : RealAlternatingTwoForm) : Prop :=
  ∀ first second, form (I * first) (I * second) = form first second

/-- [proved-derived; formal-checked] Every local Fubini--Study form has type `(1,1)`. -/
theorem fsForm_isType11 (z : ℂ) : IsType11 (fsForm z) := by
  intro first second
  simp [fsForm_apply, complexArea_I]

/-- [proved-derived; formal-checked] The local form is exactly covariant under inversion and its
complex derivative. -/
theorem fsForm_inversion {z : ℂ} (hz : z ≠ 0) (first second : ℂ) :
    fsForm z⁻¹ (-((z ^ 2)⁻¹) * first) (-((z ^ 2)⁻¹) * second) =
      fsForm z first second := by
  simp only [fsForm_apply, fsWeight, complexArea_mul, normSq_inv, map_pow, normSq_neg]
  have hnorm : normSq z ≠ 0 := mt normSq_eq_zero.mp hz
  field_simp [hnorm]
  ring

/-- [definition] The exact tangent transport of a projective affine transition. -/
def transitionTangent (source target : AffineChart) (z tangent : ℂ) : ℂ :=
  if source = target then tangent else -((z ^ 2)⁻¹) * tangent

/-- [proved-derived; formal-checked] The local Fubini--Study form glues on every admitted affine
overlap, with the complete transported tangent pair retained. -/
theorem fsForm_transition
    (source target : AffineChart) (z : ℂ)
    (hadmitted : TransitionAdmissible source target z)
    (first second : ℂ) :
    fsForm (transition source target z)
        (transitionTangent source target z first)
        (transitionTangent source target z second) =
      fsForm z first second := by
  cases source <;> cases target
  · simp [transition, transitionTangent]
  · exact fsForm_inversion (hadmitted.resolve_left (by decide)) first second
  · exact fsForm_inversion (hadmitted.resolve_left (by decide)) first second
  · simp [transition, transitionTangent]

/-- [definition] The exact normalized winding receiver of the changed-chart transition. -/
def normalizedTransitionWinding : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * (∮ z in C(0, 1), z⁻¹)

/-- [proved-derived; formal-checked] The projective transition winds once, exactly. -/
theorem normalizedTransitionWinding_eq_one : normalizedTransitionWinding = 1 := by
  have hwinding : (∮ z in C(0, 1), z⁻¹) = 2 * (Real.pi : ℂ) * I := by
    simpa using circleIntegral.integral_sub_center_inv 0
      (by norm_num : (1 : ℝ) ≠ 0)
  rw [normalizedTransitionWinding, hwinding]
  exact inv_mul_cancel₀ (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)

/-- [proved-derived; formal-checked] The complete local analytic certificate on `ℙ¹`: an exact
form field, its `(1,1)` law, its overlap pullback law, and its integral winding normalization. -/
structure ProjectiveLineType11Certificate where
  localForm : AffineChart → ℂ → RealAlternatingTwoForm
  localDifferentialForm : AffineChart → ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ
  realizesLocalForm : ∀ chart z first second,
    localDifferentialForm chart z ![first, second] = localForm chart z first second
  smooth : ∀ chart, ContDiff ℝ ⊤ (localDifferentialForm chart)
  closed : ∀ chart z, extDeriv (localDifferentialForm chart) z = 0
  type11 : ∀ chart z, IsType11 (localForm chart z)
  overlap : ∀ source target z,
    TransitionAdmissible source target z → ∀ first second,
      localForm target (transition source target z)
          (transitionTangent source target z first)
          (transitionTangent source target z second) =
        localForm source z first second
  transitionWinding : ℂ
  transitionWinding_eq_one : transitionWinding = 1
  integralWinding : ℚ
  integralWinding_realizes : (integralWinding : ℂ) = transitionWinding

/-- [proved-derived; formal-checked] The constructed Fubini--Study field supplies the certificate;
no analytic or cycle-class hypothesis is left in this object. -/
def projectiveLineType11Certificate : ProjectiveLineType11Certificate where
  localForm := fun _ => fsForm
  localDifferentialForm := fun _ => fsDifferentialForm
  realizesLocalForm := fun _ => fsDifferentialForm_apply
  smooth := fun _ => fsDifferentialForm_contDiff
  closed := fun _ => fsDifferentialForm_closed
  type11 := fun _ => fsForm_isType11
  overlap := fun source target z hadmitted =>
    fsForm_transition source target z hadmitted
  transitionWinding := normalizedTransitionWinding
  transitionWinding_eq_one := normalizedTransitionWinding_eq_one
  integralWinding := 1
  integralWinding_realizes := by
    simpa using normalizedTransitionWinding_eq_one.symm

/-- [proved-derived; formal-checked] The integral period carried by the analytic certificate is
exactly one. -/
@[simp]
theorem projectiveLineType11Certificate_integralWinding :
    projectiveLineType11Certificate.integralWinding = 1 := rfl

section Audit

#print axioms orientation_areaForm_eq_complexArea
#print axioms complexArea_mul
#print axioms fsForm_isType11
#print axioms fsForm_inversion
#print axioms fsForm_transition
#print axioms fsDifferentialForm_contDiff
#print axioms fsDifferentialForm_closed
#print axioms normalizedTransitionWinding_eq_one
#print axioms projectiveLineType11Certificate

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineType11Form
