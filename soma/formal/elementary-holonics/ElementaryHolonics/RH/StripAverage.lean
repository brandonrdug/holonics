import Mathlib
import ElementaryHolonics.RH.ConjIndex
import ElementaryHolonics.RH.TranslationAverage
import ElementaryHolonics.RH.KernelAverage

/-!
# DB3 (iv): the translation average contracts the strip of a Foster-class member

For a member `f` with conjugation symmetry and no real zero, whose zeros lie in
`|Re z − ½| ≤ Δ`, every zero of `avg μ f` has `(Re − ½)² ≤ max(Δ² − μ², 0)`: de Bruijn's
Theorem 8 in the tree's coordinate. The finite products over symmetric finsets obey the paired
factor inequality with a margin from one fixed pair; the margin survives the limit to `f`.
-/

noncomputable section

namespace Soma.Holonics.RH.StripAverage

open Complex ComplexConjugate Set Filter Topology
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.LineApproximation
open Soma.Holonics.RH.ConjIndex
open Soma.Holonics.RH.TranslationAverage
open Soma.Holonics.RH.KernelAverage

/-! ## The seam coordinate `x = −i(z − ½)` -/

def xc (w : ℂ) : ℂ := -I * (w - 1 / 2)

theorem xc_add_ofReal (w : ℂ) (μ : ℝ) : xc (w + μ) = xc w - I * μ := by
  unfold xc; ring

theorem xc_sub_ofReal (w : ℂ) (μ : ℝ) : xc (w - μ) = xc w + I * μ := by
  unfold xc; ring

theorem xc_conj (w : ℂ) : xc (conj w) = -conj (xc w) := by
  unfold xc
  rw [map_mul, map_neg, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
  ring

theorem xc_im (w : ℂ) : (xc w).im = 1 / 2 - w.re := by
  unfold xc
  simp [Complex.mul_im, Complex.sub_re]

/-- The non-strict Lemma 1. -/
theorem pair_sq_le {x y lam a b : ℝ} (hy : 0 ≤ y) (hlam : 0 ≤ lam)
    (h : b ^ 2 - lam ^ 2 ≤ (x - a) ^ 2 + y ^ 2) :
    ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) ≤
      ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) := by
  have hid : ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) -
      ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) =
      8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by ring
  have hpos : 0 ≤ 8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by
    apply mul_nonneg (by positivity)
    linarith
  linarith

theorem pair_norm_le {ζ r : ℂ} {lam : ℝ} (hy : 0 ≤ ζ.im) (hlam : 0 ≤ lam)
    (h : r.im ^ 2 - lam ^ 2 ≤ ζ.im ^ 2) :
    ‖ζ - I * lam - r‖ * ‖ζ - I * lam - conj r‖ ≤ ‖ζ + I * lam - r‖ * ‖ζ + I * lam - conj r‖ := by
  have h1 : 0 ≤ ‖ζ - I * lam - r‖ * ‖ζ - I * lam - conj r‖ := by positivity
  have h2 : 0 ≤ ‖ζ + I * lam - r‖ * ‖ζ + I * lam - conj r‖ := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) h2
  rw [mul_pow, mul_pow, norm_sq_eq, norm_sq_eq, norm_sq_eq, norm_sq_eq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, one_mul, sub_zero, zero_sub, add_zero, zero_add]
  have := pair_sq_le (x := ζ.re) (y := ζ.im) (lam := lam) (a := r.re) (b := r.im) hy hlam
    (by nlinarith [sq_nonneg (ζ.re - r.re)])
  ring_nf at this ⊢
  linarith

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-! ## The factors in the seam coordinate -/

theorem norm_one_add_a (i : Idx f) (w : ℂ) :
    ‖1 + a i w‖ = ‖xc w - I * ctr i‖ * ‖xc w + I * ctr i‖ / ‖ctr i‖ ^ 2 := by
  rw [one_add_a_eq, norm_div, norm_mul, norm_pow]
  have e1 : ctr i - (w - 1 / 2) = -I * (xc w + I * ctr i) := by
    unfold xc
    linear_combination (ctr i - (w - 1 / 2)) * Complex.I_sq
  have e2 : ctr i + (w - 1 / 2) = I * (xc w - I * ctr i) := by
    unfold xc
    linear_combination (ctr i + (w - 1 / 2)) * Complex.I_sq
  rw [e1, e2, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, one_mul, mul_comm]

theorem norm_one_add_a_σ' (hc : ConjSymm f) (i : ↥(upper f)) (w : ℂ) :
    ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) w‖ =
      ‖xc w - I * conj (ctr (i : Idx f))‖ * ‖xc w + I * conj (ctr (i : Idx f))‖ /
        ‖ctr (i : Idx f)‖ ^ 2 := by
  rw [a_σ']
  have : (1 : ℂ) + conj (a (i : Idx f) (conj w)) = conj (1 + a (i : Idx f) (conj w)) := by
    rw [map_add, map_one]
  rw [this, Complex.norm_conj, norm_one_add_a, xc_conj]
  have e1 : -conj (xc w) - I * ctr (i : Idx f) = -conj (xc w - I * conj (ctr (i : Idx f))) := by
    rw [map_sub, map_mul, Complex.conj_I, Complex.conj_conj]
    ring
  have e2 : -conj (xc w) + I * ctr (i : Idx f) = -conj (xc w + I * conj (ctr (i : Idx f))) := by
    rw [map_add, map_mul, Complex.conj_I, Complex.conj_conj]
    ring
  rw [e1, e2, norm_neg, norm_neg, Complex.norm_conj, Complex.norm_conj]

/-- The paired factor `G i w = ‖1 + a i w‖ ‖1 + a (σ i) w‖`, as two Lemma-1 pairs. -/
theorem norm_pair_eq (hc : ConjSymm f) (i : ↥(upper f)) (w : ℂ) :
    ‖1 + a (i : Idx f) w‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) w‖ =
      (‖xc w - I * ctr (i : Idx f)‖ * ‖xc w - conj (I * ctr (i : Idx f))‖) *
        (‖xc w - (-(I * ctr (i : Idx f)))‖ * ‖xc w - conj (-(I * ctr (i : Idx f)))‖) /
        ‖ctr (i : Idx f)‖ ^ 4 := by
  rw [norm_one_add_a, norm_one_add_a_σ' hc]
  have e1 : conj (I * ctr (i : Idx f)) = -(I * conj (ctr (i : Idx f))) := by
    rw [map_mul, Complex.conj_I]
    ring
  have e2 : conj (-(I * ctr (i : Idx f))) = I * conj (ctr (i : Idx f)) := by
    rw [map_neg, e1, neg_neg]
  rw [e1, e2, sub_neg_eq_add, sub_neg_eq_add]
  have hc0 : (0 : ℝ) < ‖ctr (i : Idx f)‖ := norm_ctr_pos _
  field_simp
  first | done | ring

theorem im_I_mul_ctr (i : Idx f) : (I * ctr i).im = ((i.1 : Zero f) : ℂ).re - 1 / 2 := by
  simp [ctr, Complex.mul_im]

/-- **One paired factor contracts** (Lemma 1, strictly), for `Re ζ < ½` outside the shrunken
strip. -/
theorem pair_lt (hc : ConjSymm f) {Δ μ : ℝ} (hμ : 0 < μ)
    (hΔ : ∀ z, f z = 0 → |z.re - 1 / 2| ≤ Δ) (i : ↥(upper f)) {ζ : ℂ} (hζ : ζ.re < 1 / 2)
    (hs : Δ ^ 2 - μ ^ 2 < (ζ.re - 1 / 2) ^ 2) :
    ‖1 + a (i : Idx f) (ζ + μ)‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ + μ)‖ <
      ‖1 + a (i : Idx f) (ζ - μ)‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ - μ)‖ := by
  rw [norm_pair_eq hc, norm_pair_eq hc, xc_add_ofReal, xc_sub_ofReal]
  have hc0 : (0 : ℝ) < ‖ctr (i : Idx f)‖ ^ 4 := by
    have := norm_ctr_pos (i : Idx f); positivity
  apply div_lt_div_of_pos_right _ hc0
  have hy : 0 < (xc ζ).im := by rw [xc_im]; linarith
  have hu := hΔ _ (f_eq_zero_of_mult_ne_zero (f := f) (i : Idx f).1.2)
  have hu2 : ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2) ^ 2 ≤ Δ ^ 2 := by
    have := abs_le.mp hu
    nlinarith [abs_nonneg ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2),
      sq_abs ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2), le_trans (abs_nonneg _) hu]
  have hζ2 : (ζ.re - 1 / 2) ^ 2 = (xc ζ).im ^ 2 := by rw [xc_im]; ring
  have h1 := pair_norm_lt (ζ := xc ζ) (r := I * ctr (i : Idx f)) hy hμ
    (by rw [im_I_mul_ctr, ← hζ2]; linarith)
  have h2 := pair_norm_lt (ζ := xc ζ) (r := -(I * ctr (i : Idx f))) hy hμ
    (by rw [Complex.neg_im, neg_sq, im_I_mul_ctr, ← hζ2]; linarith)
  exact mul_lt_mul'' h1 h2 (by positivity) (by positivity)

/-- The non-strict form. -/
theorem pair_le (hc : ConjSymm f) {Δ μ : ℝ} (hμ : 0 < μ)
    (hΔ : ∀ z, f z = 0 → |z.re - 1 / 2| ≤ Δ) (i : ↥(upper f)) {ζ : ℂ} (hζ : ζ.re < 1 / 2)
    (hs : Δ ^ 2 - μ ^ 2 ≤ (ζ.re - 1 / 2) ^ 2) :
    ‖1 + a (i : Idx f) (ζ + μ)‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ + μ)‖ ≤
      ‖1 + a (i : Idx f) (ζ - μ)‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ - μ)‖ := by
  rw [norm_pair_eq hc, norm_pair_eq hc, xc_add_ofReal, xc_sub_ofReal]
  have hc0 : (0 : ℝ) < ‖ctr (i : Idx f)‖ ^ 4 := by
    have := norm_ctr_pos (i : Idx f); positivity
  apply div_le_div_of_nonneg_right _ hc0.le
  have hy : 0 ≤ (xc ζ).im := by rw [xc_im]; linarith
  have hu := hΔ _ (f_eq_zero_of_mult_ne_zero (f := f) (i : Idx f).1.2)
  have hu2 : ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2) ^ 2 ≤ Δ ^ 2 := by
    have := abs_le.mp hu
    nlinarith [abs_nonneg ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2),
      sq_abs ((((i : Idx f).1 : Zero f) : ℂ).re - 1 / 2), le_trans (abs_nonneg _) hu]
  have hζ2 : (ζ.re - 1 / 2) ^ 2 = (xc ζ).im ^ 2 := by rw [xc_im]; ring
  have h1 := pair_norm_le (ζ := xc ζ) (r := I * ctr (i : Idx f)) hy hμ.le
    (by rw [im_I_mul_ctr, ← hζ2]; linarith)
  have h2 := pair_norm_le (ζ := xc ζ) (r := -(I * ctr (i : Idx f))) hy hμ.le
    (by rw [Complex.neg_im, neg_sq, im_I_mul_ctr, ← hζ2]; linarith)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ## Symmetric finite products, with a margin from one pair -/

theorem prod_σ'_of_invariant (hc : ConjSymm f) {t : Finset ↥(upper f)}
    (ht : ∀ i, σ' hc i ∈ t ↔ i ∈ t) (F : ↥(upper f) → ℝ) :
    ∏ i ∈ t, F (σ' hc i) = ∏ i ∈ t, F i := by
  apply Finset.prod_nbij' (σ' hc) (σ' hc)
  · intro i hi; exact (ht i).mpr hi
  · intro i hi; exact (ht i).mpr hi
  · intro i _; exact σ'_σ' hc i
  · intro i _; exact σ'_σ' hc i
  · intro i _; rfl

theorem sym_invariant (hc : ConjSymm f) (s : Finset ↥(upper f)) (i : ↥(upper f)) :
    σ' hc i ∈ sym hc s ↔ i ∈ sym hc s := σ'_mem_sym_iff hc s i

/-- The square of a symmetric product is the product of the paired factors. -/
theorem sq_prod_eq (hc : ConjSymm f) {t : Finset ↥(upper f)} (ht : ∀ i, σ' hc i ∈ t ↔ i ∈ t)
    (w : ℂ) :
    (∏ i ∈ t, ‖1 + a (i : Idx f) w‖) ^ 2 =
      ∏ i ∈ t, (‖1 + a (i : Idx f) w‖ * ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) w‖) := by
  rw [sq, Finset.prod_mul_distrib]
  congr 1
  exact (prod_σ'_of_invariant hc ht (fun i => ‖1 + a (i : Idx f) w‖)).symm

/-- **The symmetric product contracts with the margin of the pair `i₀`.** -/
theorem prod_le_margin (hc : ConjSymm f) {Δ μ : ℝ} (hμ : 0 < μ)
    (hΔ : ∀ z, f z = 0 → |z.re - 1 / 2| ≤ Δ) {ζ : ℂ} (hζ : ζ.re < 1 / 2)
    (hs : Δ ^ 2 - μ ^ 2 ≤ (ζ.re - 1 / 2) ^ 2) (i₀ : ↥(upper f)) {t : Finset ↥(upper f)}
    (ht : ∀ i, σ' hc i ∈ t ↔ i ∈ t) (hi₀ : i₀ ∈ t) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ‖1 + a (i₀ : Idx f) (ζ + μ)‖ * ‖1 + a ((σ' hc i₀ : ↥(upper f)) : Idx f) (ζ + μ)‖ ≤
      ρ ^ 2 * (‖1 + a (i₀ : Idx f) (ζ - μ)‖ * ‖1 + a ((σ' hc i₀ : ↥(upper f)) : Idx f) (ζ - μ)‖)) :
    ∏ i ∈ t, ‖1 + a (i : Idx f) (ζ + μ)‖ ≤ ρ * ∏ i ∈ t, ‖1 + a (i : Idx f) (ζ - μ)‖ := by
  have hP0 : 0 ≤ ∏ i ∈ t, ‖1 + a (i : Idx f) (ζ - μ)‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, sq_prod_eq hc ht, sq_prod_eq hc ht, ← Finset.mul_prod_erase t _ hi₀,
    ← Finset.mul_prod_erase t _ hi₀]
  have hrest : ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ + μ)‖ *
      ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ + μ)‖) ≤
      ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ - μ)‖ *
      ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ - μ)‖) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact pair_le hc hμ hΔ i hζ hs
  have h0 : 0 ≤ ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ + μ)‖ *
      ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ + μ)‖) :=
    Finset.prod_nonneg fun i _ => by positivity
  calc (‖1 + a (i₀ : Idx f) (ζ + μ)‖ * ‖1 + a ((σ' hc i₀ : ↥(upper f)) : Idx f) (ζ + μ)‖) *
        ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ + μ)‖ *
          ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ + μ)‖)
      ≤ (ρ ^ 2 * (‖1 + a (i₀ : Idx f) (ζ - μ)‖ *
          ‖1 + a ((σ' hc i₀ : ↥(upper f)) : Idx f) (ζ - μ)‖)) *
        ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ - μ)‖ *
          ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ - μ)‖) :=
        mul_le_mul hρ hrest h0 (by positivity)
    _ = ρ ^ 2 * ((‖1 + a (i₀ : Idx f) (ζ - μ)‖ *
          ‖1 + a ((σ' hc i₀ : ↥(upper f)) : Idx f) (ζ - μ)‖) *
        ∏ i ∈ t.erase i₀, (‖1 + a (i : Idx f) (ζ - μ)‖ *
          ‖1 + a ((σ' hc i : ↥(upper f)) : Idx f) (ζ - μ)‖)) := by ring

end Soma.Holonics.RH.StripAverage
