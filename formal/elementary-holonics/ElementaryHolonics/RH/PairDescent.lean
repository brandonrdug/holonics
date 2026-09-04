import ElementaryHolonics.RH.HeatFlowOfPolynomials

/-!
# The highest pair of a real polynomial descends under the backward heat flow

For a real polynomial the roots are closed under conjugation, so a non-real root `z` has its
partner `z̄` in the comb, contributing `2/(z − z̄) = −i/Im z` to the flux; every other root `w`
with `Im w ≤ Im z` contributes a nonpositive imaginary part.  Hence the highest pair descends
with `d/dt Im z ≤ −1/Im z`, and its height squared loses at least `2t`:
`Im z(T)² + 2T ≤ Im z(0)²`.  The pair population of `heat t p` is therefore empty once
`t ≥ (max height)²/2`, de Bruijn's bound at the polynomial face, now derived from the flow.
-/

open Polynomial Complex Finset Set
open scoped ComplexConjugate
open Soma.Holonics.RH.HeatFlowOfPolynomials

namespace Soma.Holonics.RH.PairDescent

/-! ## The imaginary part of the flux -/

theorem im_one_div_sub_nonpos {z w : ℂ} (h : w.im ≤ z.im) : (1 / (z - w)).im ≤ 0 := by
  rw [one_div, inv_im, sub_im]
  have h1 : -(z.im - w.im) ≤ 0 := by linarith
  have h2 := normSq_nonneg (z - w)
  rw [div_nonpos_iff]
  exact Or.inr ⟨h1, h2⟩

theorem im_one_div_sub_conj {z : ℂ} (hz : 0 < z.im) :
    (1 / (z - conj z)).im = -1 / (2 * z.im) := by
  rw [one_div, inv_im, sub_im, conj_im, normSq_apply, sub_re, conj_re, sub_self, sub_im, conj_im]
  field_simp
  ring

theorem im_multiset_sum_nonpos (s : Multiset ℂ) (h : ∀ x ∈ s, x.im ≤ 0) : s.sum.im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, add_im]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    linarith

/-- **The highest pair descends.**  If `z̄` is a root and every root has imaginary part at most
`Im z > 0`, the flux at `z` has imaginary part at most `−1/Im z`. -/
theorem im_flux_le (p : ℂ[X]) {z : ℂ} (hzr : conj z ∈ p.roots) (hz : 0 < z.im)
    (hmax : ∀ w ∈ p.roots, w.im ≤ z.im) :
    (2 * ((p.roots.erase z).map fun w => 1 / (z - w)).sum).im ≤ -1 / z.im := by
  classical
  have hne : conj z ≠ z := by
    intro h
    have := congrArg Complex.im h
    rw [conj_im] at this
    linarith
  have hmem : conj z ∈ p.roots.erase z := (Multiset.mem_erase_of_ne hne).mpr hzr
  rw [← Multiset.sum_map_erase hmem]
  simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, add_im]
  rw [im_one_div_sub_conj hz]
  have hrest : (((p.roots.erase z).erase (conj z)).map fun w => 1 / (z - w)).sum.im ≤ 0 := by
    apply im_multiset_sum_nonpos
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' : w ∈ p.roots := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hw)
    exact im_one_div_sub_nonpos (hmax w hw')
  have : 2 * (-1 / (2 * z.im)) = -1 / z.im := by field_simp
  linarith

/-! ## Real polynomials: conjugation-closed roots, and the flow is real -/

theorem eval_map_conj (q : ℝ[X]) (z : ℂ) :
    (q.map ofRealHom).eval (conj z) = conj ((q.map ofRealHom).eval z) := by
  rw [eval_map, eval_map, hom_eval₂]
  congr 1
  ext x
  simp

theorem conj_mem_roots (q : ℝ[X]) {z : ℂ} (hz : z ∈ (q.map ofRealHom).roots) :
    conj z ∈ (q.map ofRealHom).roots := by
  rw [mem_roots'] at hz ⊢
  refine ⟨hz.1, ?_⟩
  rw [IsRoot.def, eval_map_conj, IsRoot.def.mp hz.2, map_zero]

/-- The backward heat flow over `ℝ`. -/
noncomputable def heatR (t : ℝ) (q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (q.natDegree + 1), C ((-t) ^ k / (k.factorial : ℝ)) * (derivative^[2 * k] q)

theorem heat_map (t : ℝ) (q : ℝ[X]) : heat t (q.map ofRealHom) = (heatR t q).map ofRealHom := by
  unfold heat heatR
  rw [Polynomial.map_sum, natDegree_map_eq_of_injective Complex.ofReal_injective]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.map_mul, Polynomial.map_C, iterate_derivative_map]
  congr 2
  rw [Complex.ofRealHom_eq_coe]
  push_cast
  ring

theorem conj_mem_roots_heat (t : ℝ) (q : ℝ[X]) {z : ℂ}
    (hz : z ∈ (heat t (q.map ofRealHom)).roots) : conj z ∈ (heat t (q.map ofRealHom)).roots := by
  rw [heat_map] at hz ⊢
  exact conj_mem_roots _ hz

/-! ## The descent -/

theorem sq_add_two_mul_le' (y y' : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt y (y' t) t) (hpos : ∀ t ∈ Icc 0 T, 0 < y t)
    (hle : ∀ t ∈ Icc 0 T, y' t ≤ -1 / y t) : y T ^ 2 + 2 * T ≤ y 0 ^ 2 := by
  have hgd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => y t ^ 2 + 2 * t) (2 * y t * y' t + 2) t := by
    intro t ht
    have h1 := (hd t ht).pow 2
    have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    refine (h1.add h2).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hanti : AntitoneOn (fun t => y t ^ 2 + 2 * t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hgd t ht').deriv]
      have hy := hpos t ht'
      have h1 := hle t ht'
      have h3 : y t * (-1 / y t) = -1 := by field_simp
      have h4 : y t * y' t ≤ -1 := by
        calc y t * y' t ≤ y t * (-1 / y t) := mul_le_mul_of_nonneg_left h1 hy.le
          _ = -1 := h3
      linarith
  have := hanti (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  simpa using this

/-- **The highest pair of a real polynomial descends under the backward heat flow**: along a `C¹`
curve of simple zeros `z(t)` of `heat t p` that stays highest among the roots,
`Im z(T)² + 2T ≤ Im z(0)²`. -/
theorem highest_pair_descent (q : ℝ[X]) {z : ℝ → ℂ} {z' : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ s, (heat s (q.map ofRealHom)).eval (z s) = 0)
    (hzd : ∀ t ∈ Icc 0 T, HasDerivAt z (z' t) t)
    (hs : ∀ t ∈ Icc 0 T, (derivative (heat t (q.map ofRealHom))).eval (z t) ≠ 0)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (z t).im)
    (hmax : ∀ t ∈ Icc 0 T, ∀ w ∈ (heat t (q.map ofRealHom)).roots, w.im ≤ (z t).im) :
    (z T).im ^ 2 + 2 * T ≤ (z 0).im ^ 2 := by
  apply sq_add_two_mul_le' (fun t => (z t).im) (fun t => (z' t).im) hT
  · intro t ht
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hzd t ht)
    exact this
  · exact hpos
  · intro t ht
    have hne : heat t (q.map ofRealHom) ≠ 0 := by
      intro h
      apply hs t ht
      rw [h, derivative_zero, eval_zero]
    have hroot : z t ∈ (heat t (q.map ofRealHom)).roots := by
      rw [mem_roots']
      exact ⟨hne, hz t⟩
    have hconj := conj_mem_roots_heat t q hroot
    have hflux := zero_curve_flux (q.map ofRealHom) hz (hzd t ht) (hs t ht)
    show (z' t).im ≤ -1 / (z t).im
    rw [hflux]
    exact im_flux_le _ hconj (hpos t ht) (hmax t ht)

/-- **De Bruijn's bound at the polynomial face**: a highest pair of initial height `y₀` cannot
persist past `t = y₀²/2`. -/
theorem highest_pair_dead (q : ℝ[X]) {z : ℝ → ℂ} {z' : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ s, (heat s (q.map ofRealHom)).eval (z s) = 0)
    (hzd : ∀ t ∈ Icc 0 T, HasDerivAt z (z' t) t)
    (hs : ∀ t ∈ Icc 0 T, (derivative (heat t (q.map ofRealHom))).eval (z t) ≠ 0)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (z t).im)
    (hmax : ∀ t ∈ Icc 0 T, ∀ w ∈ (heat t (q.map ofRealHom)).roots, w.im ≤ (z t).im) :
    T < (z 0).im ^ 2 / 2 := by
  have h := highest_pair_descent q hT hz hzd hs hpos hmax
  have hT' := hpos T (right_mem_Icc.mpr hT)
  have : 0 < (z T).im ^ 2 := by positivity
  linarith

end Soma.Holonics.RH.PairDescent
