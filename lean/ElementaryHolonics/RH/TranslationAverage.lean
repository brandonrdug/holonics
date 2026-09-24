import Mathlib
import ElementaryHolonics.RH.PolyaStep

/-!
# DB2: the translation average on real polynomials (de Bruijn, Lemma 1 and Theorem 3)

For a real polynomial `q` of positive degree with every complex root in `|Im r| ≤ Δ`, and
`λ > 0`, every root of `ξ q(z + iλ) + ξ* q(z − iλ)` (`ξ ≠ 0`) has `(Im z)² ≤ max(Δ² − λ², 0)`.
The proof is factorwise: for `Im z = y > 0` with `y² > Δ² − λ²`, each conjugate pair of roots
satisfies `|z − iλ − r| |z − iλ − r̄| < |z + iλ − r| |z + iλ − r̄|` (Lemma 1), and the root
multiset of a real polynomial is conjugation-invariant, so `|q(z − iλ)| < |q(z + iλ)|`.
-/

noncomputable section

namespace Soma.Holonics.RH.TranslationAverage

open Complex Polynomial ComplexConjugate
open Soma.Holonics.RH.PolyaStep

/-! ## Lemma 1 -/

/-- **de Bruijn's Lemma 1**, in coordinates: for `r = a + ib`, `z = x + iy`, `y > 0`, `λ > 0`,
and `(x − a)² + y² > b² − λ²`, the paired factor at `z − iλ` is smaller than at `z + iλ`. -/
theorem pair_sq_lt {x y lam a b : ℝ} (hy : 0 < y) (hlam : 0 < lam)
    (h : b ^ 2 - lam ^ 2 < (x - a) ^ 2 + y ^ 2) :
    ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) <
      ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) := by
  have hid : ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) -
      ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) =
      8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by ring
  have hpos : 0 < 8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by
    apply mul_pos (by positivity)
    linarith
  linarith

theorem norm_sq_eq (w r : ℂ) : ‖w - r‖ ^ 2 = (w.re - r.re) ^ 2 + (w.im - r.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The paired factor inequality for complex numbers. -/
theorem pair_norm_lt {ζ r : ℂ} {lam : ℝ} (hy : 0 < ζ.im) (hlam : 0 < lam)
    (h : r.im ^ 2 - lam ^ 2 < ζ.im ^ 2) :
    ‖ζ - I * lam - r‖ * ‖ζ - I * lam - conj r‖ < ‖ζ + I * lam - r‖ * ‖ζ + I * lam - conj r‖ := by
  have h1 : 0 ≤ ‖ζ - I * lam - r‖ * ‖ζ - I * lam - conj r‖ := by positivity
  have h2 : 0 ≤ ‖ζ + I * lam - r‖ * ‖ζ + I * lam - conj r‖ := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 h2
  rw [mul_pow, mul_pow, norm_sq_eq, norm_sq_eq, norm_sq_eq, norm_sq_eq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, one_mul, sub_zero, zero_sub, add_zero, zero_add]
  have := pair_sq_lt (x := ζ.re) (y := ζ.im) (lam := lam) (a := r.re) (b := r.im) hy hlam
    (by nlinarith [sq_nonneg (ζ.re - r.re)])
  ring_nf at this ⊢
  linarith

/-! ## Products over the conjugation-invariant root multiset -/

theorem prod_le_prod_of_le {F G : ℂ → ℝ} (s : Multiset ℂ) (hF : ∀ r ∈ s, 0 ≤ F r)
    (hFG : ∀ r ∈ s, F r ≤ G r) : (s.map F).prod ≤ (s.map G).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    have hFa := hF a (Multiset.mem_cons_self a s)
    have hGa := hFG a (Multiset.mem_cons_self a s)
    have hs : (s.map F).prod ≤ (s.map G).prod :=
      ih (fun r hr => hF r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hFG r (Multiset.mem_cons_of_mem hr))
    have hFs : 0 ≤ (s.map F).prod := Multiset.prod_nonneg (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact hF r (Multiset.mem_cons_of_mem hr))
    calc F a * (s.map F).prod ≤ G a * (s.map F).prod := mul_le_mul_of_nonneg_right hGa hFs
      _ ≤ G a * (s.map G).prod := mul_le_mul_of_nonneg_left hs (hFa.trans hGa)

theorem prod_lt_prod_of_lt {F G : ℂ → ℝ} (s : Multiset ℂ) (hne : s ≠ 0)
    (hF : ∀ r ∈ s, 0 ≤ F r) (hFG : ∀ r ∈ s, F r < G r) : (s.map F).prod < (s.map G).prod := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s _ =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    have hFa := hF a (Multiset.mem_cons_self a s)
    have hGa := hFG a (Multiset.mem_cons_self a s)
    have hs : (s.map F).prod ≤ (s.map G).prod :=
      prod_le_prod_of_le s (fun r hr => hF r (Multiset.mem_cons_of_mem hr))
        (fun r hr => (hFG r (Multiset.mem_cons_of_mem hr)).le)
    have hGs : 0 < (s.map G).prod := Multiset.prod_pos (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact lt_of_le_of_lt (hF r (Multiset.mem_cons_of_mem hr)) (hFG r (Multiset.mem_cons_of_mem hr)))
    calc F a * (s.map F).prod ≤ F a * (s.map G).prod := mul_le_mul_of_nonneg_left hs hFa
      _ < G a * (s.map G).prod := mul_lt_mul_of_pos_right hGa hGs

/-- The complexified real polynomial and its root multiset. -/
theorem eval_eq_prod (q : ℝ[X]) (w : ℂ) :
    (q.map ofRealHom).eval w =
      (q.map ofRealHom).leadingCoeff * ((q.map ofRealHom).roots.map fun r => w - r).prod := by
  have hcard : Multiset.card (q.map ofRealHom).roots = (q.map ofRealHom).natDegree := by
    rw [card_roots_map, natDegree_map_eq_of_injective Complex.ofReal_injective]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 2
  apply Multiset.map_congr rfl
  intro r _
  simp

theorem norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun r => ‖f r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, norm_mul, ih]

theorem norm_eval_eq (q : ℝ[X]) (w : ℂ) :
    ‖(q.map ofRealHom).eval w‖ =
      ‖(q.map ofRealHom).leadingCoeff‖ * ((q.map ofRealHom).roots.map fun r => ‖w - r‖).prod := by
  rw [eval_eq_prod, norm_mul, norm_prod_map]

/-- Reindexing the root product by conjugation. -/
theorem prod_norm_conj (q : ℝ[X]) (w : ℂ) :
    ((q.map ofRealHom).roots.map fun r => ‖w - conj r‖).prod =
      ((q.map ofRealHom).roots.map fun r => ‖w - r‖).prod := by
  conv_rhs => rw [← roots_map_conj q]
  rw [Multiset.map_map]
  rfl

/-- **Theorem 3, the inequality.** For `Im ζ > 0` with `(Im ζ)² > Δ² − λ²`,
`|q(ζ − iλ)| < |q(ζ + iλ)|`. -/
theorem norm_eval_lt {q : ℝ[X]} (hdeg : 0 < q.natDegree) {Δ lam : ℝ} (hlam : 0 < lam)
    (hroots : ∀ r ∈ (q.map ofRealHom).roots, |r.im| ≤ Δ) {ζ : ℂ} (hy : 0 < ζ.im)
    (hstrip : Δ ^ 2 - lam ^ 2 < ζ.im ^ 2) :
    ‖(q.map ofRealHom).eval (ζ - I * lam)‖ < ‖(q.map ofRealHom).eval (ζ + I * lam)‖ := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact lt_irrefl _ hdeg
  have hp0 : q.map ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hq0
  have hlc : 0 < ‖(q.map ofRealHom).leadingCoeff‖ :=
    norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp0)
  have hne : (q.map ofRealHom).roots ≠ 0 := by
    intro h
    have := card_roots_map q
    rw [h, Multiset.card_zero] at this
    omega
  -- the squares as paired products
  have hsq : ∀ w : ℂ, (((q.map ofRealHom).roots.map fun r => ‖w - r‖).prod) ^ 2 =
      ((q.map ofRealHom).roots.map fun r => ‖w - r‖ * ‖w - conj r‖).prod := by
    intro w
    rw [sq]
    conv_lhs => rhs; rw [← prod_norm_conj q w]
    rw [← Multiset.prod_map_mul]
  have hlt : ((q.map ofRealHom).roots.map fun r => ‖ζ - I * lam - r‖ * ‖ζ - I * lam - conj r‖).prod <
      ((q.map ofRealHom).roots.map fun r => ‖ζ + I * lam - r‖ * ‖ζ + I * lam - conj r‖).prod := by
    apply prod_lt_prod_of_lt _ hne
    · intro r _
      positivity
    · intro r hr
      have hr' := hroots r hr
      have hb2 : r.im ^ 2 ≤ Δ ^ 2 := by
        have := abs_le.mp hr'
        nlinarith [abs_nonneg r.im, sq_abs r.im, le_trans (abs_nonneg r.im) hr']
      exact pair_norm_lt hy hlam (by linarith)
  have hPm0 : 0 ≤ ((q.map ofRealHom).roots.map fun r => ‖ζ - I * lam - r‖).prod :=
    Multiset.prod_nonneg (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_nonneg _)
  have hPp0 : 0 ≤ ((q.map ofRealHom).roots.map fun r => ‖ζ + I * lam - r‖).prod :=
    Multiset.prod_nonneg (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_nonneg _)
  have hP : (((q.map ofRealHom).roots.map fun r => ‖ζ - I * lam - r‖).prod) ^ 2 <
      (((q.map ofRealHom).roots.map fun r => ‖ζ + I * lam - r‖).prod) ^ 2 := by
    rw [hsq, hsq]
    exact hlt
  have hPP := lt_of_pow_lt_pow_left₀ 2 hPp0 hP
  rw [norm_eval_eq, norm_eval_eq]
  exact mul_lt_mul_of_pos_left hPP hlc

/-- Real polynomials commute with conjugation. -/
theorem eval_conj (q : ℝ[X]) (w : ℂ) :
    (q.map ofRealHom).eval (conj w) = conj ((q.map ofRealHom).eval w) := by
  rw [eval_map, eval_map, Polynomial.hom_eval₂]
  congr 1
  ext x
  simp

/-- Conjugation exchanges the two translates. -/
theorem conj_add_I_mul (ζ : ℂ) (lam : ℝ) : conj (ζ + I * lam) = conj ζ - I * lam := by
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_sub_I_mul (ζ : ℂ) (lam : ℝ) : conj (ζ - I * lam) = conj ζ + I * lam := by
  rw [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Theorem 3 (de Bruijn), strip form.** If every complex root of the real polynomial `q` of
positive degree has `|Im r| ≤ Δ`, then every root `ζ` of `ξ q(z + iλ) + ξ* q(z − iλ)`, `ξ ≠ 0`,
has `(Im ζ)² ≤ max(Δ² − λ², 0)`. -/
theorem im_sq_le_of_avg_eq_zero {q : ℝ[X]} (hdeg : 0 < q.natDegree) {Δ lam : ℝ} (hlam : 0 < lam)
    (hroots : ∀ r ∈ (q.map ofRealHom).roots, |r.im| ≤ Δ) {ξ : ℂ} (hξ : ξ ≠ 0) {ζ : ℂ}
    (h0 : ξ * (q.map ofRealHom).eval (ζ + I * lam) +
      conj ξ * (q.map ofRealHom).eval (ζ - I * lam) = 0) :
    ζ.im ^ 2 ≤ max (Δ ^ 2 - lam ^ 2) 0 := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < ζ.im ^ 2 := lt_of_le_of_lt (le_max_right _ _) hc
  have hstrip : Δ ^ 2 - lam ^ 2 < ζ.im ^ 2 := lt_of_le_of_lt (le_max_left _ _) hc
  have hnorm : ‖(q.map ofRealHom).eval (ζ + I * lam)‖ =
      ‖(q.map ofRealHom).eval (ζ - I * lam)‖ := by
    have h1 : ξ * (q.map ofRealHom).eval (ζ + I * lam) =
        -(conj ξ * (q.map ofRealHom).eval (ζ - I * lam)) := eq_neg_of_add_eq_zero_left h0
    have h2 := congrArg norm h1
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_conj] at h2
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hξ) h2
  have him : ζ.im ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  rcases lt_or_gt_of_ne him with hneg | hposim
  · have hy : 0 < (conj ζ).im := by
      rw [Complex.conj_im]
      linarith
    have hstrip' : Δ ^ 2 - lam ^ 2 < (conj ζ).im ^ 2 := by
      rw [Complex.conj_im, neg_sq]
      exact hstrip
    have hlt := norm_eval_lt hdeg hlam hroots hy hstrip'
    rw [← conj_add_I_mul, ← conj_sub_I_mul, eval_conj, eval_conj, Complex.norm_conj,
      Complex.norm_conj] at hlt
    linarith
  · have hlt := norm_eval_lt hdeg hlam hroots hposim hstrip
    linarith

end Soma.Holonics.RH.TranslationAverage
