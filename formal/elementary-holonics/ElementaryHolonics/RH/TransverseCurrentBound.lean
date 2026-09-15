import ElementaryHolonics.RH.PairPopulation
import ElementaryHolonics.RH.PairDescent

/-!
# A bounded transverse current

This file records a local estimate in the centred coordinate.  With
`Gτ = heatE (-τ, ξ)`, the heat equation has `∂τ G = +Gss`; the zero velocity is
`-Gss/Gs`.  The statements below are finite-current statements and make no claim about the
global zero set.  The reflection `s ↦ 1 − conj s` preserves the imaginary coordinate,
whereas the opposite member `1 − s` reverses it; these two denominators are kept distinct.
-/

open Complex Finset Set
open scoped ComplexConjugate
open Soma.Holonics.RH.PairPopulation

namespace Soma.Holonics.RH.TransverseCurrentBound

/-! ## The centred reciprocal -/

theorem sub_reflect_eq_ofReal {s : ℂ} :
    s - reflect s = ((2 * (s.re - 1 / 2) : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [reflect] <;> ring

/-- The conserved normal centre leaves the longitudinal coordinate free. -/
theorem reflected_pair_center (s : ℂ) :
    (s + reflect s) / 2 = 1 / 2 + Complex.I * (s.im : ℂ) := by
  apply Complex.ext <;> simp [reflect, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

theorem two_re_inv_sub_reflect {s : ℂ} (hd : 0 < s.re - 1 / 2) :
    2 * (1 / (s - reflect s)).re = 1 / (s.re - 1 / 2) := by
  rw [sub_reflect_eq_ofReal]
  norm_num [one_div, inv_re, normSq_apply]
  field_simp

theorem two_re_inv_sub_one_sub {s : ℂ} (hd : 0 < s.re - 1 / 2) :
    2 * (1 / (s - (1 - s))).re =
      (s.re - 1 / 2) / ((s.re - 1 / 2) ^ 2 + s.im ^ 2) := by
  norm_num [one_div, inv_re, normSq_apply]
  field_simp
  ring

/-! ## Finite surplus -/

noncomputable def surplus (Z : Finset ℂ) (s : ℂ) : ℝ :=
  2 * Z.sum (fun w => (s.re - w.re) / Complex.normSq (s - w))

theorem surplus_nonneg {Z : Finset ℂ} {s : ℂ}
    (hleft : ∀ w ∈ Z, w.re ≤ s.re) : 0 ≤ surplus Z s := by
  unfold surplus
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro w hw
  exact div_nonneg (sub_nonneg.mpr (hleft w hw)) (normSq_nonneg _)

/-- Actual divisor populations retain their multiplicities. -/
noncomputable def weightedSurplus (Z : Finset ℂ) (multiplicity : ℂ → ℕ) (s : ℂ) : ℝ :=
  2 * Z.sum (fun w => (multiplicity w : ℝ) * (s.re - w.re) / Complex.normSq (s - w))

theorem weightedSurplus_nonneg {Z : Finset ℂ} {multiplicity : ℂ → ℕ} {s : ℂ}
    (hleft : ∀ w ∈ Z, w.re ≤ s.re) : 0 ≤ weightedSurplus Z multiplicity s := by
  unfold weightedSurplus
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro w hw
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hleft w hw)))
    (normSq_nonneg _)

/-- Project the full oriented finite-current error to the normal component. -/
theorem re_velocity_le_of_complex_error {v c : ℂ} {d J eps : ℝ}
    (herror : ‖v - (-2 * c)‖ ≤ eps)
    (hsplit : (2 * c).re = 1 / d + J) :
    v.re ≤ -1 / d - J + eps := by
  have h := (Complex.re_le_norm (v - (-2 * c))).trans herror
  have heq : (v - (-2 * c)).re = v.re + (2 * c).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re]
    norm_num
  rw [heq, hsplit] at h
  simp only [neg_div]
  linarith

/-! ## The integrated current estimate -/

theorem sq_add_two_mul_le_of_current (d d' J : ℝ → ℝ) {T a eps : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt d (d' t) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < d t)
    (hderiv : ∀ t ∈ Icc 0 T, d' t ≤ -1 / d t - J t + eps)
    (hgap : ∀ t ∈ Icc 0 T, d t * (J t - eps) ≥ a)
    (ha : 0 ≤ a) : d T ^ 2 + 2 * (1 + a) * T ≤ d 0 ^ 2 := by
  have hgd : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun t => d t ^ 2 + 2 * (1 + a) * t)
        (2 * d t * d' t + 2 * (1 + a)) t := by
    intro t ht
    have h1 := (hd t ht).pow 2
    have h2 : HasDerivAt (fun t : ℝ => 2 * (1 + a) * t) (2 * (1 + a)) t := by
      simpa [mul_assoc] using (hasDerivAt_id t).const_mul (2 * (1 + a))
    refine (h1.add h2).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hanti : AntitoneOn (fun t => d t ^ 2 + 2 * (1 + a) * t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hgd t ht').deriv]
      have hdp := hpos t ht'
      have hde := hderiv t ht'
      have hgp := hgap t ht'
      have hmul : d t * d' t ≤ -(1 + a) := by
        have h1 : d t * d' t ≤ d t * (-1 / d t - J t + eps) :=
          mul_le_mul_of_nonneg_left hde hdp.le
        have hcancel : d t * (-1 / d t) = -1 := by field_simp
        nlinarith
      nlinarith
  have h := hanti (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  simpa using h

theorem no_positive_trajectory {d d' J : ℝ → ℝ} {T a eps : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt d (d' t) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < d t)
    (hderiv : ∀ t ∈ Icc 0 T, d' t ≤ -1 / d t - J t + eps)
    (hgap : ∀ t ∈ Icc 0 T, d t * (J t - eps) ≥ a)
    (ha : 0 ≤ a) (hsmall : d 0 ^ 2 < 2 * (1 + a) * T) : False := by
  have h := sq_add_two_mul_le_of_current d d' J hT hd hpos hderiv hgap ha
  nlinarith [sq_nonneg (d T)]

/-! ## Finite flux / residual interface -/

theorem deriv_le_of_flux_residual {v d J F eps : ℝ} (hF : |F| ≤ eps)
    (hactual : F = v + 1 / d + J) : v ≤ -1 / d - J + eps := by
  have habs : F ≤ eps := (abs_le.mp hF).2
  rw [hactual] at habs
  calc
    v = (v + 1 / d + J) - (1 / d + J) := by ring
    _ ≤ eps - (1 / d + J) := sub_le_sub_right habs _
    _ = -1 / d - J + eps := by ring

end Soma.Holonics.RH.TransverseCurrentBound

#print axioms Soma.Holonics.RH.TransverseCurrentBound.two_re_inv_sub_reflect
#print axioms Soma.Holonics.RH.TransverseCurrentBound.reflected_pair_center
#print axioms Soma.Holonics.RH.TransverseCurrentBound.weightedSurplus_nonneg
#print axioms Soma.Holonics.RH.TransverseCurrentBound.re_velocity_le_of_complex_error
#print axioms Soma.Holonics.RH.TransverseCurrentBound.surplus_nonneg
#print axioms Soma.Holonics.RH.TransverseCurrentBound.sq_add_two_mul_le_of_current
#print axioms Soma.Holonics.RH.TransverseCurrentBound.no_positive_trajectory
#print axioms Soma.Holonics.RH.TransverseCurrentBound.deriv_le_of_flux_residual
