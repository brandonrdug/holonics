import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LHopital
import ElementaryHolonics.Millennium.NavierStokesAxialPrimitive
import ElementaryHolonics.Millennium.NavierStokesAxisRegularization

/-!
# The first axial jet

The zero-axis derivative is obtained from the actual interval primitives.  The proof uses the
quotient `J/(z I)` and one L'Hôpital step; the quotient of its derivative population is reduced to
the quotient of the two continuous `dslope` populations at the axis.
-/

noncomputable section

open ContDiff Set Filter MeasureTheory
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesAxisFirstJet

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive
open Soma.Holonics.Millennium.NavierStokesAxisRegularization

theorem hasDerivAt_axialH_zero
    (alpha beta : ℝ) (A F : ℝ → ℝ)
    (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F)
    (hpositive : ∀ z, 0 < F z) (hk : alpha + 2 * beta ≠ 0)
    (hA0 : deriv A 0 = 0) :
    HasDerivAt (axialH alpha beta A F)
      (deriv (deriv A) 0 / (4 * (alpha + 2 * beta))) 0 := by
  let f : ℝ → ℝ := fun t ↦ (F t)⁻¹
  let g : ℝ → ℝ := fun t ↦ deriv A t / F t
  let I : ℝ → ℝ := intervalPrimitive f
  let J : ℝ → ℝ := intervalPrimitive g
  let Q : ℝ → ℝ := fun z ↦ z * I z
  let D : ℝ → ℝ := fun z ↦ I z + z * f z
  have hf : Continuous f := by
    exact hF.continuous.inv₀ (fun z ↦ (hpositive z).ne')
  have hAd : ContDiff ℝ 1 (deriv A) := hA.deriv' (n := 1)
  have hFdiff : Differentiable ℝ F :=
    (hF.of_le (by norm_num)).differentiable_one
  have hAdDiff : Differentiable ℝ (deriv A) := hAd.differentiable_one
  have hg : Continuous g := by
    exact hAd.continuous.div hF.continuous (fun z ↦ (hpositive z).ne')
  have hI : ∀ z, HasDerivAt I (f z) z := by
    intro z
    exact hasDerivAt_intervalPrimitive f hf z
  have hJ : ∀ z, HasDerivAt J (g z) z := by
    intro z
    exact hasDerivAt_intervalPrimitive g hg z
  have hQ : ∀ z, HasDerivAt Q (D z) z := by
    intro z
    have h := (hasDerivAt_id z).mul (hI z)
    change HasDerivAt (fun y : ℝ => y * I y) (D z) z
    have hfun : (id * I) = (fun y : ℝ => y * I y) := by
      funext y
      simp only [Pi.mul_apply, id_eq]
    rw [hfun] at h
    simpa [D, mul_comm, add_comm, add_left_comm, add_assoc] using h
  have hfDiff : Differentiable ℝ f := by
    intro z
    exact DifferentiableAt.inv (hFdiff z) (hpositive z).ne'
  have hDderiv : ∀ z, HasDerivAt D (f z + (f z + z * deriv f z)) z := by
    intro z
    have h := (hI z).add ((hasDerivAt_id z).mul (hfDiff z).hasDerivAt)
    have hfun : (I + id * f) = (fun y : ℝ => I y + y * f y) := by
      funext y
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    rw [hfun] at h
    simpa [D, mul_comm, add_comm, add_left_comm, add_assoc] using h
  have hI0 : I 0 = 0 := by simp [I, intervalPrimitive]
  have hJ0 : J 0 = 0 := by simp [J, intervalPrimitive]
  have hG0 : g 0 = 0 := by simp [g, hA0]
  have hQ0 : Q 0 = 0 := by simp [Q, I, intervalPrimitive]
  have hD0 : D 0 = 0 := by simp [D, I, intervalPrimitive]
  have hDderiv0 : deriv D 0 = 2 * f 0 := by
    rw [(hDderiv 0).deriv]
    simp
    ring
  have hDderiv0_ne : deriv D 0 ≠ 0 := by
    rw [hDderiv0]
    exact mul_ne_zero (by norm_num) (inv_ne_zero (hpositive 0).ne')
  have hgd0 : deriv g 0 = deriv (deriv A) 0 / F 0 := by
    have hgderiv := DifferentiableAt.hasDerivAt (hAdDiff 0)
    have hquot := hgderiv.div
      (DifferentiableAt.hasDerivAt (hFdiff 0))
      (hpositive 0).ne'
    have heq := hquot.deriv
    simp [hA0] at heq
    field_simp [hpositive 0 |>.ne'] at heq
    apply (eq_div_iff (hpositive 0).ne').2
    change deriv (deriv A / F) 0 * F 0 = deriv (deriv A) 0
    exact heq
  have hgd0_div : deriv g 0 / deriv D 0 =
      deriv (deriv A) 0 / 2 := by
    rw [hgd0, hDderiv0]
    simp [f]
    field_simp [hpositive 0 |>.ne']
  have hgdiff : DifferentiableAt ℝ g 0 :=
    (hAdDiff 0).div (hFdiff 0) (hpositive 0).ne'
  have hgslope : ContinuousAt (dslope g 0) 0 :=
    continuousAt_dslope_same.mpr hgdiff
  have hDslope : ContinuousAt (dslope D 0) 0 :=
    continuousAt_dslope_same.mpr ((hDderiv 0).differentiableAt)
  have hDslope0 : dslope D 0 0 ≠ 0 := by
    rw [dslope_same, hDderiv0]
    simpa [hDderiv0] using hDderiv0_ne
  have hratioSlope : Tendsto
      (fun z ↦ dslope g 0 z / dslope D 0 z) (𝓝 0)
      (𝓝 (deriv g 0 / deriv D 0)) := by
    have ht := (hgslope.div hDslope hDslope0).tendsto
    have hval : (dslope g 0 / dslope D 0) 0 = deriv g 0 / deriv D 0 := by
      simp [dslope_same]
    rw [hval] at ht
    exact ht
  have hDneSlope : ∀ᶠ z in 𝓝[≠] (0 : ℝ), dslope D 0 z ≠ 0 := by
    have h := hDslope.preimage_mem_nhds (isOpen_ne.mem_nhds hDslope0)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h
  have hDne : ∀ᶠ z in 𝓝[≠] (0 : ℝ), D z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hDneSlope] with z hz hds
    intro hzero
    apply hds
    rw [dslope_of_ne D hz]
    simp [slope, hD0, hzero]
  have hratioGD : Tendsto (fun z ↦ g z / D z) (𝓝[≠] (0 : ℝ))
      (𝓝 (deriv g 0 / deriv D 0)) := by
    apply (tendsto_congr' ?_).2
    · exact hratioSlope.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hDne] with z hz hDz
    rw [dslope_of_ne g hz, dslope_of_ne D hz]
    simp [slope, hG0, hD0, vsub_eq_sub, sub_zero, smul_eq_mul]
    field_simp [hz, hDz]
    rw [mul_div_cancel_right₀ (g z) hz]
  have hJtendsto : Tendsto J (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hJ0] using (hJ 0).continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hQtendsto : Tendsto Q (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hQ0] using (hQ 0).continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hquotient : Tendsto (fun z ↦ J z / Q z) (𝓝[≠] (0 : ℝ))
      (𝓝 (deriv g 0 / deriv D 0)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
    · exact Filter.Eventually.of_forall (fun z ↦ hJ z)
    · exact Filter.Eventually.of_forall (fun z ↦ hQ z)
    · exact hDne
    · exact hJtendsto
    · exact hQtendsto
    · exact hratioGD
  have hHzero : axialH alpha beta A F 0 = 0 := by
    exact (axialH_eq_regularized alpha beta A F hA hF hpositive hk hA0 0).trans
      (axialHRegularized_zero_eq_zero hA hF hpositive hA0)
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : Tendsto
      (slope (axialH alpha beta A F) 0) (𝓝[≠] (0 : ℝ))
      (𝓝 (deriv (deriv A) 0 / (4 * (alpha + 2 * beta)))) := by
    have heq : slope (axialH alpha beta A F) 0 =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun z ↦ (1 / (2 * (alpha + 2 * beta))) * (J z / Q z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [slope, hHzero, sub_zero, vsub_eq_sub, sub_zero, smul_eq_mul]
      rw [axialH_eq_regularized alpha beta A F hA hF hpositive hk hA0 z]
      rw [axialHRegularized, regularizedIntegralRatio_eq_integralRatio_of_ne
        f g hf (fun t ↦ inv_pos.mpr (hpositive t)) hz]
      simp [f, g, I, J, Q, div_eq_mul_inv]
      field_simp [hz]
    apply (tendsto_congr' heq).2
    have ht : Tendsto
        (fun z : ℝ => (1 / (2 * (alpha + 2 * beta))) * (J z / Q z))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((1 / (2 * (alpha + 2 * beta))) *
          (deriv g 0 / deriv D 0))) :=
      hquotient.const_mul (1 / (2 * (alpha + 2 * beta)))
    convert ht using 1
    rw [hgd0_div]
    congr 1
    field_simp [hk]
    ring
  exact hslope

#print axioms hasDerivAt_axialH_zero

end Soma.Holonics.Millennium.NavierStokesAxisFirstJet
