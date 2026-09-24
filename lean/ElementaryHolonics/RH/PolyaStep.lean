import Mathlib

/-!
# The Hermite–Poulain step: `1 + aD` and `1 − λD²` never increase the non-real root count

For a real polynomial `p` the non-real roots come in conjugate pairs, so their number
`nonreal p = deg p − #(real roots)` is even.  Rolle applied to `e^{ax} p(x)` gives a root of
`p + a p′` strictly between consecutive real roots of `p`, and every real root of multiplicity `k`
survives with multiplicity at least `k − 1`; hence `#real(p + a p′) ≥ #real(p) − 1`, and by
parity `nonreal (p + a p′) ≤ nonreal p`.  Factoring `1 − λD² = (1 − √λ D)(1 + √λ D)` gives the
same for the heat step `p ↦ p − λ p″`.  This is the mechanism by which the backward heat flow
never creates a pair.
-/

open Polynomial Complex Finset Set
open scoped ComplexConjugate

namespace Soma.Holonics.RH.PolyaStep

/-! ## Parity: non-real roots come in pairs -/

/-- A conjugation-invariant multiset of non-real numbers has even cardinality. -/
theorem even_card_of_conj_invariant (s : Multiset ℂ) (hs : s.map conj = s)
    (hfix : ∀ x ∈ s, conj x ≠ x) : Even (Multiset.card s) := by
  classical
  induction h : Multiset.card s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases Multiset.empty_or_exists_mem s with hempty | ⟨x, hx⟩
    · subst hempty
      simp at h
      subst h
      exact ⟨0, rfl⟩
    · have hcx : conj x ∈ s := by
        rw [← hs]
        exact Multiset.mem_map_of_mem _ hx
      have hne : conj x ≠ x := hfix x hx
      set s' := (s.erase x).erase (conj x) with hs'
      have hcxe : conj x ∈ s.erase x := (Multiset.mem_erase_of_ne hne).mpr hcx
      have hcard : Multiset.card s' = n - 2 := by
        rw [hs', Multiset.card_erase_of_mem hcxe, Multiset.card_erase_of_mem hx, h]
        simp only [Nat.pred_eq_sub_one]
        omega
      have hn2 : 2 ≤ n := by
        have h1 := Multiset.card_pos_iff_exists_mem.mpr ⟨conj x, hcxe⟩
        rw [Multiset.card_erase_of_mem hx, h] at h1
        simp only [Nat.pred_eq_sub_one] at h1
        omega
      have hinv : s'.map conj = s' := by
        rw [hs', Multiset.map_erase _ (starRingEnd ℂ).injective, Multiset.map_erase _
          (starRingEnd ℂ).injective, hs, Complex.conj_conj, Multiset.erase_comm]
      have hfix' : ∀ y ∈ s', conj y ≠ y := fun y hy =>
        hfix y (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hy))
      have := ih (n - 2) (by omega) s' hinv hfix' hcard
      obtain ⟨k, hk⟩ := this
      exact ⟨k + 1, by omega⟩

/-- The real roots of `p`, counted with multiplicity, are the real-valued complex roots of `p`. -/
theorem roots_map_ofReal (p : ℝ[X]) :
    (p.map ofRealHom).roots.filter (fun z => z.im = 0) =
      p.roots.map (fun r : ℝ => (r : ℂ)) := by
  classical
  ext z
  rw [Multiset.count_filter]
  split_ifs with hz
  · obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = z := ⟨z.re, by apply Complex.ext <;> simp [hz]⟩
    have hm := eq_rootMultiplicity_map (p := p) (f := ofRealHom) ofRealHom.injective x
    rw [Complex.ofRealHom_eq_coe] at hm
    rw [count_roots, ← hm, Multiset.count_map_eq_count' _ _ Complex.ofReal_injective, count_roots]
  · rw [eq_comm, Multiset.count_eq_zero]
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨x, _, rfl⟩ := hmem
    exact hz (by simp)

/-- The non-real root count of a real polynomial. -/
noncomputable def nonreal (p : ℝ[X]) : ℕ := p.natDegree - Multiset.card p.roots

theorem card_roots_map (p : ℝ[X]) : Multiset.card (p.map ofRealHom).roots = p.natDegree := by
  rw [splits_iff_card_roots.mp (IsAlgClosed.splits _),
    natDegree_map_eq_of_injective Complex.ofReal_injective]

theorem nonreal_eq_card_filter (p : ℝ[X]) :
    nonreal p = Multiset.card ((p.map ofRealHom).roots.filter fun z => ¬ z.im = 0) := by
  classical
  unfold nonreal
  have hcard : Multiset.card ((p.map ofRealHom).roots.filter fun z => z.im = 0) +
      Multiset.card ((p.map ofRealHom).roots.filter fun z => ¬ z.im = 0) =
      Multiset.card (p.map ofRealHom).roots := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  rw [roots_map_ofReal, Multiset.card_map, card_roots_map] at hcard
  omega

theorem roots_map_conj (p : ℝ[X]) :
    (p.map ofRealHom).roots.map conj = (p.map ofRealHom).roots := by
  have hconj : (p.map ofRealHom).map (starRingEnd ℂ) = p.map ofRealHom := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp
  have h := roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (card_roots_map p ▸ (natDegree_map_eq_of_injective Complex.ofReal_injective p).symm)
  rw [hconj] at h
  exact h

/-- **Parity**: the non-real root count of a real polynomial is even. -/
theorem even_nonreal (p : ℝ[X]) : Even (nonreal p) := by
  classical
  rw [nonreal_eq_card_filter]
  apply even_card_of_conj_invariant
  · conv_rhs => rw [← roots_map_conj p]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro z _
    simp
  · intro x hx
    rw [Multiset.mem_filter] at hx
    intro h
    have := congrArg Complex.im h
    rw [conj_im] at this
    exact hx.2 (by linarith)

/-! ## The weighted Rolle count -/

/-- The linear operator `p ↦ p + a p′`. -/
noncomputable def step (a : ℝ) (p : ℝ[X]) : ℝ[X] := p + C a * derivative p

theorem derivative_eq_zero_of_natDegree_eq_zero {p : ℝ[X]} (h0 : p.natDegree = 0) :
    derivative p = 0 := by
  rw [eq_C_of_natDegree_eq_zero h0]
  simp

theorem natDegree_step (a : ℝ) (p : ℝ[X]) : (step a p).natDegree = p.natDegree := by
  unfold step
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [derivative_eq_zero_of_natDegree_eq_zero h0, mul_zero, add_zero]
  · exact natDegree_add_eq_left_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_C_mul_le _ _) (natDegree_derivative_lt (by omega)))

theorem step_ne_zero {p : ℝ[X]} (hp : p ≠ 0) (a : ℝ) : step a p ≠ 0 := by
  intro h
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · unfold step at h
    rw [derivative_eq_zero_of_natDegree_eq_zero h0, mul_zero, add_zero] at h
    exact hp h
  · have := natDegree_step a p
    rw [h, natDegree_zero] at this
    omega

/-- A real root of multiplicity `k` survives the step with multiplicity at least `k − 1`. -/
theorem rootMultiplicity_sub_one_le_step {p : ℝ[X]} (hp : p ≠ 0) (a r : ℝ) :
    rootMultiplicity r p - 1 ≤ rootMultiplicity r (step a p) := by
  rw [le_rootMultiplicity_iff (step_ne_zero hp a)]
  obtain ⟨g, hg, -⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  rcases Nat.eq_zero_or_pos (rootMultiplicity r p) with hk | hk
  · rw [hk]
    simp
  · obtain ⟨m, hm⟩ : ∃ m, rootMultiplicity r p = m + 1 := ⟨rootMultiplicity r p - 1, by omega⟩
    rw [hm] at hg
    rw [hm, Nat.add_sub_cancel]
    unfold step
    rw [hg, derivative_mul, derivative_X_sub_C_pow, Nat.add_sub_cancel]
    have t1 : (X - C r) ^ m ∣ (X - C r) ^ (m + 1) * g :=
      dvd_mul_of_dvd_left (pow_dvd_pow _ (Nat.le_succ m)) g
    have t2 : (X - C r) ^ m ∣
        C a * (C ((m + 1 : ℕ) : ℝ) * (X - C r) ^ m * g + (X - C r) ^ (m + 1) * derivative g) :=
      dvd_mul_of_dvd_right (dvd_add
        (dvd_mul_of_dvd_left (dvd_mul_left _ _) g)
        (dvd_mul_of_dvd_left (pow_dvd_pow _ (Nat.le_succ m)) _)) (C a)
    exact dvd_add t1 t2

/-- Rolle for `e^{x/a} p(x)`: a root of `p + a p′` strictly between two roots of `p`. -/
theorem exists_step_root_between (p : ℝ[X]) {a : ℝ} (ha : a ≠ 0) {x y : ℝ} (hxy : x < y)
    (hx : p.IsRoot x) (hy : p.IsRoot y) : ∃ z ∈ Ioo x y, (step a p).IsRoot z := by
  have hf : ∀ t, HasDerivAt (fun t => Real.exp (t / a) * p.eval t)
      (Real.exp (t / a) / a * (step a p).eval t) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (t / a)) (Real.exp (t / a) * (1 / a)) t := by
      simpa using ((hasDerivAt_id t).div_const a).exp
    have := h1.mul (p.hasDerivAt t)
    refine this.congr_deriv ?_
    simp only [step, eval_add, eval_mul, eval_C]
    field_simp
  obtain ⟨z, hz, hz0⟩ := exists_hasDerivAt_eq_zero hxy
    (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (by simp [hx.eq_zero, hy.eq_zero]) (fun t _ => hf t)
  refine ⟨z, hz, ?_⟩
  exact (mul_eq_zero.mp hz0).resolve_left (div_ne_zero (Real.exp_pos _).ne' ha)

theorem card_roots_toFinset_le_step {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    p.roots.toFinset.card ≤ ((step a p).roots.toFinset \ p.roots.toFinset).card + 1 := by
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz, hz0⟩ := exists_step_root_between p ha hxy hx hy
  refine ⟨z, ?_, hz.1, hz.2⟩
  rw [Multiset.mem_toFinset, mem_roots (step_ne_zero hp a)]
  exact hz0

/-- **The weighted Rolle count**: `#real(p + a p′) ≥ #real(p) − 1` with multiplicity. -/
theorem card_roots_le_step {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (step a p).roots + 1 := by
  classical
  calc
    Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, (step a p).rootMultiplicity x) +
          (((step a p).roots.toFinset \ p.roots.toFinset).card + 1) :=
      add_le_add
        (Finset.sum_le_sum fun x _ => rootMultiplicity_sub_one_le_step hp a x)
        (card_roots_toFinset_le_step hp ha)
    _ ≤ (∑ x ∈ p.roots.toFinset, (step a p).roots.count x) +
          ((∑ x ∈ (step a p).roots.toFinset \ p.roots.toFinset,
            (step a p).roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (step a p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-! ## The step theorems -/

/-- **Hermite–Poulain**: `p ↦ p + a p′` never increases the non-real root count. -/
theorem nonreal_step_le (a : ℝ) (p : ℝ[X]) : nonreal (step a p) ≤ nonreal p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [step, nonreal]
  rcases eq_or_ne a 0 with rfl | ha
  · simp [step]
  have hdeg := natDegree_step a p
  have hcount := card_roots_le_step hp ha
  have hle := card_roots' p
  have h1 : nonreal (step a p) ≤ nonreal p + 1 := by
    unfold nonreal
    rw [hdeg]
    omega
  obtain ⟨k, hk⟩ := even_nonreal (step a p)
  obtain ⟨l, hl⟩ := even_nonreal p
  omega

/-- The heat step `p ↦ p − λ p″`. -/
noncomputable def heatStep (lam : ℝ) (p : ℝ[X]) : ℝ[X] := p - C lam * derivative^[2] p

theorem heatStep_eq {lam : ℝ} (hlam : 0 ≤ lam) (p : ℝ[X]) :
    heatStep lam p = step (-(Real.sqrt lam)) (step (Real.sqrt lam) p) := by
  unfold heatStep step
  rw [Function.iterate_succ_apply', Function.iterate_one, derivative_add, derivative_C_mul,
    C_neg]
  have hcs : C (Real.sqrt lam) * C (Real.sqrt lam) = C lam := by
    rw [← C_mul, Real.mul_self_sqrt hlam]
  linear_combination (derivative (derivative p)) * hcs

/-- **The heat step never creates a pair.** -/
theorem nonreal_heatStep_le {lam : ℝ} (hlam : 0 ≤ lam) (p : ℝ[X]) :
    nonreal (heatStep lam p) ≤ nonreal p := by
  rw [heatStep_eq hlam]
  exact (nonreal_step_le _ _).trans (nonreal_step_le _ _)

end Soma.Holonics.RH.PolyaStep
