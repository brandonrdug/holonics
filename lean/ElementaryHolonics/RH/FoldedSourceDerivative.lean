import Mathlib
import ElementaryHolonics.RH.FoldedSource

/-!
# Differentiating one folded source event

The positive-index event integral is differentiated in its complex spectral variable.  The
derivative is controlled on a unit neighbourhood by one extra exponential factor in `u`; this is
absorbed by the already proved source majorant with its height parameter increased by one.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedSourceDerivative

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.FoldedSourceBounds
open Soma.Holonics.RH.FoldedSource

/-- The actual complex derivative of one folded source integrand. -/
def foldedSourceTermDeriv (t : ℝ) (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  -(u : ℂ) * (Real.exp (t * u ^ 2) : ℂ) * (foldedPhiTerm n u : ℂ) *
    Complex.sin (z * (u : ℂ))

theorem hasDerivAt_foldedSourceTerm (t : ℝ) (z : ℂ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => foldedSourceTerm t w n u)
      (foldedSourceTermDeriv t z n u) z := by
  let amplitude : ℂ := (Real.exp (t * u ^ 2) : ℂ) * (foldedPhiTerm n u : ℂ)
  have harg : HasDerivAt (fun w : ℂ => w * (u : ℂ)) (u : ℂ) z :=
    by simpa only [id_eq, one_mul] using (hasDerivAt_id z).mul_const (u : ℂ)
  have hcos : HasDerivAt (fun w : ℂ => Complex.cos (w * (u : ℂ)))
      (-Complex.sin (z * (u : ℂ)) * (u : ℂ)) z := by
    simpa only [Function.comp_def] using
      (Complex.hasDerivAt_cos (z * (u : ℂ))).comp z harg
  change HasDerivAt (fun w : ℂ => amplitude * Complex.cos (w * (u : ℂ)))
    (-(u : ℂ) * (Real.exp (t * u ^ 2) : ℂ) * (foldedPhiTerm n u : ℂ) *
      Complex.sin (z * (u : ℂ))) z
  have hprod : HasDerivAt (fun w : ℂ => amplitude * Complex.cos (w * (u : ℂ)))
      (amplitude * (-Complex.sin (z * (u : ℂ)) * (u : ℂ))) z :=
    hcos.const_mul amplitude
  apply hprod.congr_deriv
  simp only [amplitude]
  ring

theorem norm_sin_le_exp_abs_im (w : ℂ) :
    ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  calc
    ‖Complex.sin w‖ = ‖(Complex.exp (-w * Complex.I) -
        Complex.exp (w * Complex.I)) * Complex.I‖ / 2 := by
      rw [← Complex.two_sin]
      norm_num
    _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
      gcongr
      rw [norm_mul]
      norm_num
      exact norm_sub_le _ _
    _ = (Real.exp (-w.im) + Real.exp (w.im)) / 2 := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp [Complex.mul_re, add_comm]
    _ ≤ Real.exp |w.im| := by
      have h₁ : Real.exp (-w.im) ≤ Real.exp |w.im| :=
        Real.exp_le_exp.mpr (neg_le_abs _)
      have h₂ : Real.exp w.im ≤ Real.exp |w.im| :=
        Real.exp_le_exp.mpr (le_abs_self _)
      nlinarith [Real.exp_pos |w.im|]

theorem norm_sin_mul_real_le_exp {z : ℂ} {u : ℝ} :
    ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (|z.im| * |u|) := by
  have h := norm_sin_le_exp_abs_im (z * (u : ℂ))
  simpa [Complex.mul_im, abs_mul] using h

theorem foldedPhiTerm_le_sourceCoefficient_majorant {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    foldedPhiTerm n u ≤ sourceCoefficient n *
      Real.exp (9 * u - π * Real.exp (4 * u) / 2) := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsplit : (n + 1 : ℝ) ^ 2 / 2 + Real.exp (4 * u) / 2 ≤
      (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) := by
    have hprod : 0 ≤ ((n + 1 : ℝ) ^ 2 - 1) * (Real.exp (4 * u) - 1) :=
      mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr he)
    have hboth : 1 ≤ (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) := by
      simpa using (mul_le_mul hn he (by positivity) (by positivity))
    nlinarith
  have hexp : Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u)) ≤
      Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
        Real.exp (-π * Real.exp (4 * u) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hphi := foldedPhiTerm_le_exp_source (n := n) hu
  calc
    foldedPhiTerm n u ≤
        2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
          Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u)) := hphi
    _ ≤ 2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
        (Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
          Real.exp (-π * Real.exp (4 * u) / 2)) := by
      gcongr
    _ = sourceCoefficient n * Real.exp (9 * u - π * Real.exp (4 * u) / 2) := by
      unfold sourceCoefficient
      have hexp : Real.exp (9 * u - π * Real.exp (4 * u) / 2) =
          Real.exp (9 * u) * Real.exp (-π * Real.exp (4 * u) / 2) := by
        rw [show 9 * u - π * Real.exp (4 * u) / 2 =
            9 * u + (-π * Real.exp (4 * u) / 2) by ring, Real.exp_add]
      rw [hexp]
      ring

theorem norm_foldedSourceTermDeriv_le
    {T R t : ℝ} {z : ℂ} {n : ℕ} {u : ℝ}
    (_hT : 0 ≤ T) (hR : 0 ≤ R) (hu : 0 ≤ u)
    (ht : |t| ≤ T) (hz : |z.im| ≤ R) :
    ‖foldedSourceTermDeriv t z n u‖ ≤
      sourceCoefficient n * sourceMajorant T (R + 1) u := by
  have hsin : ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (R * u) := by
    apply le_trans norm_sin_mul_real_le_exp
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hu]
    exact mul_le_mul hz le_rfl (by positivity) hR
  have htu : t * u ^ 2 ≤ T * u ^ 2 := by
    apply mul_le_mul_of_nonneg_right
    exact (le_trans (le_abs_self t) ht)
    positivity
  have hu_exp : u ≤ Real.exp u := by
    have := add_one_le_exp u
    linarith
  have hphi := foldedPhiTerm_le_sourceCoefficient_majorant (n := n) hu
  unfold foldedSourceTermDeriv
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (foldedPhiTerm_nonneg hu)]
  calc
    u * Real.exp (t * u ^ 2) * foldedPhiTerm n u *
        ‖Complex.sin (z * (u : ℂ))‖ ≤
      Real.exp u * Real.exp (T * u ^ 2) *
        (sourceCoefficient n * Real.exp (9 * u - π * Real.exp (4 * u) / 2)) *
          Real.exp (R * u) := by
      gcongr
      · unfold sourceCoefficient
        positivity
      · exact foldedPhiTerm_nonneg hu
    _ = sourceCoefficient n * sourceMajorant T (R + 1) u := by
      unfold sourceMajorant
      have htarget : Real.exp (T * u ^ 2 + (R + 1 + 9) * u -
            π * Real.exp (4 * u) / 2) =
          Real.exp (T * u ^ 2) * Real.exp u * Real.exp (9 * u) *
          Real.exp (R * u) * Real.exp (-π * Real.exp (4 * u) / 2) := by
        rw [show T * u ^ 2 + (R + 1 + 9) * u - π * Real.exp (4 * u) / 2 =
            T * u ^ 2 + u + 9 * u + R * u + (-π * Real.exp (4 * u) / 2) by ring,
          Real.exp_add, Real.exp_add, Real.exp_add]
        rw [Real.exp_add]
      rw [show 9 * u - π * Real.exp (4 * u) / 2 =
          9 * u + (-π * Real.exp (4 * u) / 2) by ring, Real.exp_add]
      rw [htarget]
      ring

theorem hasDerivAt_integral_foldedSourceTerm (t : ℝ) (z : ℂ) (n : ℕ) :
    HasDerivAt (fun w : ℂ => ∫ u in Ioi (0 : ℝ), foldedSourceTerm t w n u)
      (∫ u in Ioi (0 : ℝ), foldedSourceTermDeriv t z n u) z := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let bound : ℝ → ℝ := fun u => sourceCoefficient n * sourceMajorant |t| (|z.im| + 1 + 1) u
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (foldedSourceTerm t w n) μ :=
    Filter.Eventually.of_forall fun w ↦ (continuous_foldedSourceTerm t w n).aestronglyMeasurable
  have hint : Integrable (foldedSourceTerm t z n) μ := integrableOn_foldedSourceTerm t z n
  have hcont : Continuous (foldedSourceTermDeriv t z n) := by
    unfold foldedSourceTermDeriv foldedPhiTerm
    fun_prop
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z 1,
      ‖foldedSourceTermDeriv t w n u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwim : |w.im| ≤ |z.im| + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have him : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have him' : |w.im| ≤ |z.im| + ‖w - z‖ := by
        calc
          |w.im| = |z.im + (w - z).im| := by rw [sub_im]; congr 1; ring
          _ ≤ |z.im| + |(w - z).im| := abs_add_le _ _
          _ ≤ |z.im| + ‖w - z‖ := by
            simpa [add_comm] using add_le_add_left (Complex.abs_im_le_norm (w - z)) |z.im|
      linarith
    have hbound : ‖foldedSourceTermDeriv t w n u‖ ≤
        sourceCoefficient n * sourceMajorant |t| (|z.im| + 1 + 1) u := by
      exact norm_foldedSourceTermDeriv_le (n := n) (t := t) (z := w)
        (T := abs t) (R := |z.im| + 1)
        (_hT := abs_nonneg t) (hR := by positivity) (hu := hu.le)
        (ht := le_rfl) (hz := by linarith)
    exact hbound
  have hboundInt : Integrable bound μ := by
    simpa [μ, bound] using
      (integrableOn_sourceMajorant (abs_nonneg t) (by positivity)).const_mul
        (sourceCoefficient n)
  have hderiv : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun v ↦ foldedSourceTerm t v n u) (foldedSourceTermDeriv t w n u) w :=
    Filter.Eventually.of_forall fun u w _hw ↦ hasDerivAt_foldedSourceTerm t w n u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun w u => foldedSourceTerm t w n u)
    (x₀ := z) (s := Metric.ball z 1)
    (F' := fun w u => foldedSourceTermDeriv t w n u)
    (bound := bound) (Metric.ball_mem_nhds z one_pos)
    hmeas hint hcont.aestronglyMeasurable hbound hboundInt hderiv
  simpa [μ] using hmain.2

section Audit

#print axioms hasDerivAt_foldedSourceTerm
#print axioms norm_sin_le_exp_abs_im
#print axioms foldedPhiTerm_le_sourceCoefficient_majorant
#print axioms norm_foldedSourceTermDeriv_le
#print axioms hasDerivAt_integral_foldedSourceTerm

end Audit

end Soma.Holonics.RH.FoldedSourceDerivative
