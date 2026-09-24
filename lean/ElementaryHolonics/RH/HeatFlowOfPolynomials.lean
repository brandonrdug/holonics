import Mathlib

/-!
# The backward heat flow of a polynomial moves every simple zero by the comb flux

`heat t p = e^{−tD²} p = Σ_k (−t)^k/k! · p^{(2k)}` is the backward heat flow on polynomials, the
finite-dimensional face of the de Bruijn--Newman flow `H_t`.  It satisfies `∂_t = −∂_z²`, and a
`C¹` curve of simple zeros `z(t)` of `heat t p` obeys
`ż = (heat t p)''(z) / (heat t p)'(z) = 2 Σ_{w ≠ z} 1/(z − w)`,
the sum over the other roots with multiplicity: the comb flux of the phase-flow ledger, now a
theorem of the flow rather than a postulate.  The pair population (the non-real roots, in
conjugate pairs for real `p`) moves by this law.
-/

open Polynomial Complex Finset

namespace Soma.Holonics.RH.HeatFlowOfPolynomials

/-- The backward heat flow `e^{−tD²} p`, truncated at the degree (all higher derivatives vanish). -/
noncomputable def heat (t : ℝ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ range (p.natDegree + 1),
    C (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) * (derivative^[2 * k] p)

theorem heat_zero (p : ℂ[X]) : heat 0 p = p := by
  unfold heat
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem eval_heat (t : ℝ) (p : ℂ[X]) (z : ℂ) :
    (heat t p).eval z = ∑ k ∈ range (p.natDegree + 1),
      ((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ) * (derivative^[2 * k] p).eval z := by
  simp [heat, eval_finsetSum]

theorem derivative_heat (t : ℝ) (p : ℂ[X]) :
    derivative (heat t p) = ∑ k ∈ range (p.natDegree + 1),
      C (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) * (derivative^[2 * k + 1] p) := by
  unfold heat
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_C_mul, Function.iterate_succ_apply']

theorem second_derivative_heat (t : ℝ) (p : ℂ[X]) :
    derivative^[2] (heat t p) = ∑ k ∈ range (p.natDegree + 1),
      C (((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) * (derivative^[2 * (k + 1)] p) := by
  unfold heat
  rw [iterate_derivative_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_derivative_C_mul, ← Function.iterate_add_apply]
  congr 2
  ring

/-- The joint derivative along a `C¹` curve: `d/dt (heat t p)(z(t)) = −(heat t p)''(z) + (heat t p)'(z) ż`. -/
theorem hasDerivAt_eval_heat_comp (p : ℂ[X]) {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hzd : HasDerivAt z z' t) :
    HasDerivAt (fun s : ℝ => (heat s p).eval (z s))
      (-((derivative^[2] (heat t p)).eval (z t)) + (derivative (heat t p)).eval (z t) * z') t := by
  set n := p.natDegree with hn
  -- the term-by-term derivatives
  have hterm : ∀ k ∈ range (n + 1), HasDerivAt
      (fun s : ℝ => ((-s : ℝ) : ℂ) ^ k / (k.factorial : ℂ) * (derivative^[2 * k] p).eval (z s))
      ((k : ℂ) * ((-t : ℝ) : ℂ) ^ (k - 1) * (-1) / (k.factorial : ℂ) * (derivative^[2 * k] p).eval (z t) +
        ((-t : ℝ) : ℂ) ^ k / (k.factorial : ℂ) * ((derivative (derivative^[2 * k] p)).eval (z t) * z')) t := by
    intro k _
    have h1 : HasDerivAt (fun s : ℝ => ((-s : ℝ) : ℂ) ^ k / (k.factorial : ℂ))
        ((k : ℂ) * ((-t : ℝ) : ℂ) ^ (k - 1) * (-1) / (k.factorial : ℂ)) t := by
      have h0 : HasDerivAt (fun s : ℝ => ((-s : ℝ) : ℂ)) (-1) t := by
        have := (hasDerivAt_id t).neg.ofReal_comp
        simpa using this
      have := (h0.pow k).div_const (k.factorial : ℂ)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have h2 : HasDerivAt (fun s : ℝ => (derivative^[2 * k] p).eval (z s))
        ((derivative (derivative^[2 * k] p)).eval (z t) * z') t :=
      ((derivative^[2 * k] p).hasDerivAt (z t)).comp t hzd
    exact h1.mul h2
  have hsum := HasDerivAt.sum hterm
  have key : (fun s : ℝ => (heat s p).eval (z s)) =
      ∑ k ∈ range (n + 1), fun s : ℝ =>
        ((-s : ℝ) : ℂ) ^ k / (k.factorial : ℂ) * (derivative^[2 * k] p).eval (z s) := by
    funext s
    rw [eval_heat, Finset.sum_apply]
  rw [key]
  refine hsum.congr_deriv ?_
  rw [second_derivative_heat, derivative_heat, eval_finsetSum, eval_finsetSum,
    Finset.sum_add_distrib, Finset.sum_mul, ← hn]
  have hB : ∑ x ∈ range (n + 1), ((-t : ℝ) : ℂ) ^ x / (x.factorial : ℂ) *
      ((derivative (derivative^[2 * x] p)).eval (z t) * z') =
      ∑ i ∈ range (n + 1),
        (C (((-t : ℝ) : ℂ) ^ i / (i.factorial : ℂ)) * (derivative^[2 * i + 1] p)).eval (z t) * z' := by
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_mul, eval_C, Function.iterate_succ_apply']
    ring
  have hA : ∑ x ∈ range (n + 1), ((x : ℂ) * ((-t : ℝ) : ℂ) ^ (x - 1) * (-1) / (x.factorial : ℂ) *
      (derivative^[2 * x] p).eval (z t)) =
      -∑ i ∈ range (n + 1),
        (C (((-t : ℝ) : ℂ) ^ i / (i.factorial : ℂ)) * (derivative^[2 * (i + 1)] p)).eval (z t) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hlast : (C (((-t : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) *
        (derivative^[2 * (n + 1)] p)).eval (z t) = 0 := by
      rw [iterate_derivative_eq_zero (by omega : p.natDegree < 2 * (n + 1))]
      simp
    rw [hlast, add_zero]
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [eval_mul, eval_C, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hA, hB]

/-! ## The flux at a simple root -/

/-- The log derivative of a product of linear factors at a non-root. -/
theorem derivative_multiset_prod_div (s : Multiset ℂ) {z : ℂ} (hz : z ∉ s) :
    (derivative ((s.map fun a => X - C a).prod)).eval z /
        ((s.map fun a => X - C a).prod).eval z =
      (s.map fun w => 1 / (z - w)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    have hzw : z ≠ w := fun h => hz (h ▸ Multiset.mem_cons_self w s)
    have hzs : z ∉ s := fun h => hz (Multiset.mem_cons_of_mem h)
    have hP : ((s.map fun a => X - C a).prod).eval z ≠ 0 := by
      rw [eval_multiset_prod]
      apply Multiset.prod_ne_zero
      intro h
      rw [Multiset.mem_map] at h
      obtain ⟨a, ha, h0⟩ := h
      rw [Multiset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at h0
      exact hzs (h0 ▸ hb)
    rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_X, eval_C,
      Multiset.map_cons, Multiset.sum_cons, ← ih hzs]
    have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
    field_simp

/-- **The flux at a simple root**: `p''(z)/p'(z) = 2 Σ_{w ∈ other roots} 1/(z − w)`. -/
theorem second_div_first_eq (p : ℂ[X]) {z : ℂ} (hz : p.IsRoot z)
    (hs : (derivative p).eval z ≠ 0) :
    (derivative^[2] p).eval z / (derivative p).eval z =
      2 * ((p.roots.erase z).map fun w => 1 / (z - w)).sum := by
  classical
  set q := p /ₘ (X - C z) with hq
  have hpq : (X - C z) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hz
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, derivative_zero, eval_zero] at hs
    exact hs rfl
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpq
    exact hp0 hpq.symm
  -- p' = q + (X − z) q', p'' = 2 q' + (X − z) q''
  have hd1 : derivative p = q + (X - C z) * derivative q := by
    rw [← hpq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hd2 : derivative^[2] p = 2 * derivative q + (X - C z) * derivative^[2] q := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hd1, derivative_add, derivative_mul,
      derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, Function.iterate_succ_apply',
      Function.iterate_one]
    ring
  have he1 : (derivative p).eval z = q.eval z := by
    rw [hd1, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have he2 : (derivative^[2] p).eval z = 2 * (derivative q).eval z := by
    rw [hd2, eval_add, eval_mul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
    simp
  have hqz : q.eval z ≠ 0 := by rwa [he1] at hs
  -- q = c ∏ (X − w) over its roots
  have hsplit : Multiset.card q.roots = q.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits q)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hznot : z ∉ q.roots := by
    intro h
    rw [mem_roots hq0] at h
    exact hqz h
  have hroots : p.roots.erase z = q.roots := by
    rw [← hpq, roots_mul (hpq ▸ hp0), roots_X_sub_C, Multiset.singleton_add, Multiset.erase_cons_head]
  have hlog : (derivative q).eval z / q.eval z = (q.roots.map fun w => 1 / (z - w)).sum := by
    have hc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    conv_lhs => rw [← hfac, derivative_C_mul, eval_mul, eval_mul, eval_C, mul_div_mul_left _ _ hc]
    exact derivative_multiset_prod_div q.roots hznot
  rw [he1, he2, hroots, ← hlog]
  ring

/-! ## The zero curve moves by the flux -/

/-- **The pair population moves by the comb flux.**  A `C¹` curve of simple zeros of the backward
heat flow satisfies `ż = 2 Σ_{w ≠ z} 1/(z − w)`, the sum over the other roots with multiplicity. -/
theorem zero_curve_flux (p : ℂ[X]) {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : ∀ s, (heat s p).eval (z s) = 0) (hzd : HasDerivAt z z' t)
    (hs : (derivative (heat t p)).eval (z t) ≠ 0) :
    z' = 2 * (((heat t p).roots.erase (z t)).map fun w => 1 / (z t - w)).sum := by
  have hF := hasDerivAt_eval_heat_comp p hzd
  have hconst : HasDerivAt (fun s : ℝ => (heat s p).eval (z s)) 0 t := by
    have : (fun s : ℝ => (heat s p).eval (z s)) = fun _ => (0 : ℂ) := funext hz
    rw [this]
    exact hasDerivAt_const t (0 : ℂ)
  have h0 := hF.unique hconst
  have hz' : z' = (derivative^[2] (heat t p)).eval (z t) / (derivative (heat t p)).eval (z t) := by
    rw [eq_div_iff hs]
    linear_combination h0
  rw [hz', second_div_first_eq (heat t p) (by simpa [IsRoot] using hz t) hs]

end Soma.Holonics.RH.HeatFlowOfPolynomials
