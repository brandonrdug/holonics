import ElementaryHolonics.RH.RectangleArgumentPrinciple
import ElementaryHolonics.RH.PolyaStep
import ElementaryHolonics.Millennium.BirchSwinnertonDyerWinding
import ElementaryHolonics.RH.ExplicitFormulaLimit

/-!
# Hurwitz for polynomials: the non-real root count is lower semicontinuous

A polynomial is its own zero factorization, so the rectangle argument principle counts its
roots inside any rectangle whose boundary carries none.  Under coefficientwise convergence
`p_N → p` the rectangle integrals of `p_N′/p_N` converge to that of `p′/p`, the counts are
integers, so they are eventually equal: every non-real root of `p` of multiplicity `k` is the
limit of at least `k` non-real roots of `p_N`.  Hence `nonreal p ≤ nonreal p_N` for `N` large:
the non-real count can only drop in the limit.  This is the step that carries the
Hermite–Poulain monotonicity from the Euler steps to `e^{−tD²}` itself.
-/

open Polynomial Complex Metric Set Finset Filter Topology
open scoped Classical Interval
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleArgumentPrinciple
open Soma.Holonics.Millennium.BirchSwinnertonDyerWinding
open Soma.Holonics.RH.ExplicitFormulaLimit

namespace Soma.Holonics.RH.HurwitzPolynomial

/-! ## A polynomial is its own zero factorization -/

/-- The zero factorization of a nonzero polynomial on a disc containing its roots. -/
noncomputable def polyFactorization (p : ℂ[X]) (hp : p ≠ 0) (z₀ : ℂ) {r : ℝ}
    (hroots : ∀ ρ ∈ p.roots, ρ ∈ closedBall z₀ (r / 2)) :
    ZeroFactorization (fun w => p.eval w) z₀ r where
  zeros := p.roots.toFinset
  mult := fun ρ => rootMultiplicity ρ p
  unit := fun _ => p.leadingCoeff
  zeros_mem := fun ρ hρ => hroots ρ (Multiset.mem_toFinset.mp hρ)
  mult_pos := fun ρ hρ =>
    (rootMultiplicity_pos hp).mpr ((mem_roots hp).mp (Multiset.mem_toFinset.mp hρ))
  unit_diff := differentiableOn_const _
  unit_ne := fun _ _ => leadingCoeff_ne_zero.mpr hp
  factor := fun z _ => by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (splits_iff_card_roots.mp (IsAlgClosed.splits p))]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, mul_comm]
    congr 1
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro ρ _
    simp [count_roots]

/-- The count of roots of `p` in a set, with multiplicity, as a finset sum. -/
noncomputable def rootCount (p : ℂ[X]) (U : Set ℂ) : ℕ :=
  ∑ ρ ∈ p.roots.toFinset, if ρ ∈ U then rootMultiplicity ρ p else 0

theorem rootCount_eq_card_filter (p : ℂ[X]) (U : Set ℂ) :
    rootCount p U = Multiset.card (p.roots.filter fun ρ => ρ ∈ U) := by
  unfold rootCount
  rw [← Multiset.toFinset_sum_count_eq (p.roots.filter fun ρ => ρ ∈ U)]
  rw [← Finset.sum_subset
    (Multiset.toFinset_subset.mpr (Multiset.filter_subset (fun ρ => ρ ∈ U) p.roots))]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Multiset.mem_toFinset, Multiset.mem_filter] at hρ
    rw [if_pos hρ.2, Multiset.count_filter_of_pos hρ.2, count_roots]
  · intro ρ hρ hρ'
    rw [Multiset.mem_toFinset] at hρ
    rw [Multiset.mem_toFinset, Multiset.mem_filter] at hρ'
    rw [if_neg fun hU => hρ' ⟨hρ, hU⟩]

/-- **The rectangle counts the roots of a polynomial.** -/
theorem rectIntegral_logDeriv_poly (p : ℂ[X]) (hp : p ≠ 0) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im) (hbd : ∀ ρ ∈ p.roots, ρ ∉ boundaryRect z w) :
    rectIntegral (fun ζ => logDeriv (fun x => p.eval x) ζ) z w =
      2 * Real.pi * I * (rootCount p (openRect z w) : ℂ) := by
  -- a disc about 0 containing the roots and the rectangle
  set R : ℝ := (p.roots.map fun ρ => ‖ρ‖).sum + 2 * (‖z‖ + ‖w‖) + 1 with hR
  have hR0 : 0 ≤ (p.roots.map fun ρ => ‖ρ‖).sum :=
    Multiset.sum_nonneg fun x hx => by
      rw [Multiset.mem_map] at hx
      obtain ⟨ρ, _, rfl⟩ := hx
      exact norm_nonneg ρ
  have hr : 0 < 2 * R := by rw [hR]; positivity
  have hroots : ∀ ρ ∈ p.roots, ρ ∈ closedBall (0 : ℂ) (2 * R / 2) := by
    intro ρ hρ
    rw [mem_closedBall_zero_iff]
    have := Multiset.single_le_sum (fun x hx => by
        rw [Multiset.mem_map] at hx
        obtain ⟨ρ', _, rfl⟩ := hx
        exact norm_nonneg ρ') ‖ρ‖ (Multiset.mem_map_of_mem _ hρ)
    rw [hR]
    linarith [norm_nonneg z, norm_nonneg w]
  set Z := polyFactorization p hp 0 hroots with hZ
  have hrect : closedRect z w ⊆ ball (0 : ℂ) (2 * R / 2) := by
    intro ζ hζ
    have := closedRect_subset_ball_of_radius z w 0 hζ
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_zero, add_zero] at this
    rw [hR]
    linarith
  have hbd' : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w := fun ρ hρ =>
    hbd ρ (Multiset.mem_toFinset.mp hρ)
  have := rectIntegral_mul_logDeriv Z hr hzw hrect (h := fun _ => (1 : ℂ))
    (differentiableOn_const 1) hbd'
  simp only [one_mul, mul_one] at this
  rw [this]
  congr 1
  unfold rootCount
  push_cast
  rfl

/-! ## Coefficientwise convergence gives uniform convergence on bounded sets -/

theorem eventually_norm_eval_sub_lt {q : ℕ → ℂ[X]} {p : ℂ[X]} {n : ℕ}
    (hdeg : ∀ N, (q N).natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k)))
    {M : ℝ} (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ w : ℂ, ‖w‖ ≤ M → ‖(q N).eval w - p.eval w‖ < ε := by
  have hS : Tendsto (fun N => ∑ i ∈ range (n + 1), ‖(q N).coeff i - p.coeff i‖ * M ^ i) atTop
      (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ i ∈ range (n + 1), ‖p.coeff i - p.coeff i‖ * M ^ i := by simp
    rw [h0]
    apply tendsto_finsetSum
    intro i _
    exact (((hcoeff i).sub tendsto_const_nhds).norm).mul_const _
  filter_upwards [(tendsto_order.1 hS).2 ε hε] with N hN w hw
  calc ‖(q N).eval w - p.eval w‖
      = ‖∑ i ∈ range (n + 1), ((q N).coeff i - p.coeff i) * w ^ i‖ := by
        rw [eval_eq_sum_range' (by have := hdeg N; omega : (q N).natDegree < n + 1),
          eval_eq_sum_range' (by omega : p.natDegree < n + 1), ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ ∑ i ∈ range (n + 1), ‖(q N).coeff i - p.coeff i‖ * M ^ i := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_pow]
        gcongr
    _ < ε := hN

theorem tendsto_coeff_derivative {q : ℕ → ℂ[X]} {p : ℂ[X]}
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k))) (k : ℕ) :
    Tendsto (fun N => (derivative (q N)).coeff k) atTop (𝓝 ((derivative p).coeff k)) := by
  simp only [coeff_derivative]
  exact (hcoeff (k + 1)).mul_const _

theorem natDegree_derivative_le' {p : ℂ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (derivative p).natDegree ≤ n := (natDegree_derivative_le p).trans (by omega)

/-! ## The edge integrals converge -/

/-- Along an edge on which `p` does not vanish: eventually `q N` does not vanish either, and the
edge integrals of `q N′/q N` converge to that of `p′/p`. -/
theorem tendsto_edge_integral {q : ℕ → ℂ[X]} {p : ℂ[X]} {n : ℕ}
    (hdeg : ∀ N, (q N).natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k)))
    {e : ℝ → ℂ} (he : Continuous e) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ x ∈ Icc a b, p.eval (e x) ≠ 0) :
    (∀ᶠ N in atTop, ∀ x ∈ Icc a b, (q N).eval (e x) ≠ 0) ∧
    Tendsto (fun N => ∫ x in a..b, (derivative (q N)).eval (e x) / (q N).eval (e x)) atTop
      (𝓝 (∫ x in a..b, (derivative p).eval (e x) / p.eval (e x))) := by
  -- the edge is bounded
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (he.continuousOn (s := Icc a b))
  set M := max M₀ 0 with hM
  have hMe : ∀ x ∈ Icc a b, ‖e x‖ ≤ M := fun x hx => (hM₀ x hx).trans (le_max_left _ _)
  -- the minimum of ‖p‖ on the edge
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩
    ((p.continuous.comp he).norm.continuousOn (s := Icc a b))
  set δ := ‖p.eval (e x₀)‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.mpr (hne x₀ hx₀)
  have hδle : ∀ x ∈ Icc a b, δ ≤ ‖p.eval (e x)‖ := fun x hx => by
    have := hmin hx
    simpa [Function.comp] using this
  -- the maximum of ‖p′‖ on the edge
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((derivative p).continuous.comp he).continuousOn (s := Icc a b))
  have hev := eventually_norm_eval_sub_lt hdeg hp hcoeff (le_max_right M₀ 0) (half_pos hδ0)
  have hev' := eventually_norm_eval_sub_lt (fun N => natDegree_derivative_le' (hdeg N))
    (natDegree_derivative_le' hp) (tendsto_coeff_derivative hcoeff) (le_max_right M₀ 0)
    one_pos
  have hlow : ∀ᶠ N in atTop, ∀ x ∈ Icc a b, δ / 2 ≤ ‖(q N).eval (e x)‖ := by
    filter_upwards [hev] with N hN x hx
    have h1 := hN (e x) (hMe x hx)
    have h2 := hδle x hx
    have := norm_sub_norm_le (p.eval (e x)) ((q N).eval (e x))
    rw [norm_sub_rev] at h1
    linarith
  have hup : ∀ᶠ N in atTop, ∀ x ∈ Icc a b, ‖(derivative (q N)).eval (e x)‖ ≤ D + 1 := by
    filter_upwards [hev'] with N hN x hx
    have h1 := hN (e x) (hMe x hx)
    have h2 := hD x hx
    simp only [Function.comp] at h2
    have := norm_le_norm_add_norm_sub' ((derivative (q N)).eval (e x)) ((derivative p).eval (e x))
    linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hlow] with N hN x hx
    have := hN x hx
    intro h0
    rw [h0, norm_zero] at this
    linarith
  · have hIcc : ∀ x ∈ Ι a b, x ∈ Icc a b := fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      exact Ioc_subset_Icc_self hx
    have hnum : ∀ x ∈ Icc a b, Tendsto (fun N => (derivative (q N)).eval (e x)) atTop
        (𝓝 ((derivative p).eval (e x))) := by
      intro x hx
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [eventually_norm_eval_sub_lt (fun N => natDegree_derivative_le' (hdeg N))
        (natDegree_derivative_le' hp) (tendsto_coeff_derivative hcoeff) (le_max_right M₀ 0) hε]
        with N hN
      rw [dist_eq_norm]
      exact hN (e x) (hMe x hx)
    have hden : ∀ x ∈ Icc a b, Tendsto (fun N => (q N).eval (e x)) atTop (𝓝 (p.eval (e x))) := by
      intro x hx
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [eventually_norm_eval_sub_lt hdeg hp hcoeff (le_max_right M₀ 0) hε] with N hN
      rw [dist_eq_norm]
      exact hN (e x) (hMe x hx)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (D + 1) / (δ / 2))
    · filter_upwards with N
      exact (((derivative (q N)).continuous.comp he).measurable.div
        ((q N).continuous.comp he).measurable).aestronglyMeasurable
    · filter_upwards [hlow, hup] with N hN1 hN2
      refine Eventually.of_forall fun x hx => ?_
      have hx' := hIcc x hx
      rw [norm_div]
      have hD' := hD x hx'
      simp only [Function.comp] at hD'
      exact div_le_div₀ (by linarith [norm_nonneg ((derivative p).eval (e x))])
        (hN2 x hx') (half_pos hδ0) (hN1 x hx')
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x hx => ?_
      have hx' := hIcc x hx
      exact (hnum x hx').div (hden x hx') (hne x hx')

/-! ## The rectangle integrals converge and the counts are eventually equal -/

theorem eval_ne_zero_of_not_root {p : ℂ[X]} (hp : p ≠ 0) {ζ : ℂ} (h : ζ ∉ p.roots) :
    p.eval ζ ≠ 0 := fun h0 => h ((mem_roots hp).mpr h0)

theorem tendsto_rectIntegral_logDeriv {q : ℕ → ℂ[X]} {p : ℂ[X]} {n : ℕ}
    (hdeg : ∀ N, (q N).natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k))) (hp0 : p ≠ 0)
    {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im) (hbd : ∀ ρ ∈ p.roots, ρ ∉ boundaryRect z w) :
    (∀ᶠ N in atTop, ∀ ρ ∈ (q N).roots, ρ ∉ boundaryRect z w) ∧
    Tendsto (fun N => rectIntegral (fun ζ => logDeriv (fun x => (q N).eval x) ζ) z w) atTop
      (𝓝 (rectIntegral (fun ζ => logDeriv (fun x => p.eval x) ζ) z w)) := by
  have hne : ∀ ζ ∈ boundaryRect z w, p.eval ζ ≠ 0 := fun ζ hζ =>
    eval_ne_zero_of_not_root hp0 fun hρ => hbd ζ hρ hζ
  have hb := tendsto_edge_integral hdeg hp hcoeff (e := fun x : ℝ => (x : ℂ) + z.im * I)
    (by fun_prop) hzw.1.le (fun x hx => hne _ (bottom_mem (Set.uIcc_of_le hzw.1.le ▸ hx)))
  have ht := tendsto_edge_integral hdeg hp hcoeff (e := fun x : ℝ => (x : ℂ) + w.im * I)
    (by fun_prop) hzw.1.le (fun x hx => hne _ (top_mem (Set.uIcc_of_le hzw.1.le ▸ hx)))
  have hr := tendsto_edge_integral hdeg hp hcoeff (e := fun y : ℝ => (w.re : ℂ) + y * I)
    (by fun_prop) hzw.2.le (fun y hy => hne _ (right_mem (Set.uIcc_of_le hzw.2.le ▸ hy)))
  have hl := tendsto_edge_integral hdeg hp hcoeff (e := fun y : ℝ => (z.re : ℂ) + y * I)
    (by fun_prop) hzw.2.le (fun y hy => hne _ (left_mem (Set.uIcc_of_le hzw.2.le ▸ hy)))
  refine ⟨?_, ?_⟩
  · filter_upwards [hb.1, ht.1, hr.1, hl.1] with N h1 h2 h3 h4 ρ hρ hρb
    have hρeq : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := (Complex.re_add_im ρ).symm
    obtain ⟨⟨hre, him⟩, hcase⟩ := boundaryRect_cases hzw hρb
    have h0 : (q N).eval ρ = 0 := (mem_roots'.mp hρ).2
    rcases hcase with hc | hc | hc | hc
    · apply h4 ρ.im him
      rw [← hc, ← hρeq]
      exact h0
    · apply h3 ρ.im him
      rw [← hc, ← hρeq]
      exact h0
    · apply h1 ρ.re hre
      rw [← hc, ← hρeq]
      exact h0
    · apply h2 ρ.re hre
      rw [← hc, ← hρeq]
      exact h0
  · simp only [rectIntegral, logDeriv_apply, Polynomial.deriv]
    exact ((hb.2.sub ht.2).add (hr.2.const_smul I)).sub (hl.2.const_smul I)

theorem nat_eq_of_norm_sub_lt {a b : ℕ} (h : ‖(a : ℂ) - (b : ℂ)‖ < 1 / 2) : a = b := by
  by_contra hne
  have hz : ((a : ℤ) - (b : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have h1 : (1 : ℝ) ≤ |(((a : ℤ) - (b : ℤ) : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have h2 : ‖(a : ℂ) - (b : ℂ)‖ = |(((a : ℤ) - (b : ℤ) : ℤ) : ℝ)| := by
    rw [← Complex.norm_intCast]
    push_cast
    rfl
  linarith

/-- **Hurwitz for polynomials on a rectangle**: the root counts are eventually equal. -/
theorem eventually_rootCount_eq {q : ℕ → ℂ[X]} {p : ℂ[X]} {n : ℕ}
    (hdeg : ∀ N, (q N).natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k))) (hp0 : p ≠ 0)
    {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im) (hbd : ∀ ρ ∈ p.roots, ρ ∉ boundaryRect z w) :
    ∀ᶠ N in atTop, rootCount (q N) (openRect z w) = rootCount p (openRect z w) := by
  obtain ⟨hbdN, htend⟩ := tendsto_rectIntegral_logDeriv hdeg hp hcoeff hp0 hzw hbd
  have hq0 : ∀ᶠ N in atTop, q N ≠ 0 := by
    obtain ⟨k, hk⟩ : ∃ k, p.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hp0 (Polynomial.ext fun k => by rw [h k, coeff_zero])
    filter_upwards [(hcoeff k).eventually_ne hk] with N hN h0
    rw [h0, coeff_zero] at hN
    exact hN rfl
  have h2πi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have h2 : Tendsto (fun N => 2 * Real.pi * I * (rootCount (q N) (openRect z w) : ℂ)) atTop
      (𝓝 (2 * Real.pi * I * (rootCount p (openRect z w) : ℂ))) := by
    rw [← rectIntegral_logDeriv_poly p hp0 hzw hbd]
    refine htend.congr' ?_
    filter_upwards [hq0, hbdN] with N hN1 hN2
    exact rectIntegral_logDeriv_poly (q N) hN1 hzw hN2
  have h3 : Tendsto (fun N => (rootCount (q N) (openRect z w) : ℂ)) atTop
      (𝓝 (rootCount p (openRect z w) : ℂ)) := by
    have := h2.const_mul (2 * Real.pi * I : ℂ)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ h2πi] using this
  filter_upwards [Metric.tendsto_nhds.mp h3 (1 / 2) (by norm_num)] with N hN
  rw [dist_eq_norm] at hN
  exact nat_eq_of_norm_sub_lt hN

/-! ## The non-real count is lower semicontinuous -/

theorem rootCount_mono (p : ℂ[X]) {U V : Set ℂ} (h : U ⊆ V) : rootCount p U ≤ rootCount p V := by
  unfold rootCount
  apply Finset.sum_le_sum
  intro ρ _
  by_cases hU : ρ ∈ U
  · rw [if_pos hU, if_pos (h hU)]
  · rw [if_neg hU]
    exact Nat.zero_le _

theorem sum_rootCount_disjoint (p : ℂ[X]) {ι : Type*} (S : Finset ι) (U : ι → Set ℂ)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (U i) (U j)) :
    ∑ i ∈ S, rootCount p (U i) = rootCount p (⋃ i ∈ S, U i) := by
  unfold rootCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hmem : ∃ i ∈ S, ρ ∈ U i
  · obtain ⟨i, hi, hρi⟩ := hmem
    rw [Finset.sum_eq_single i]
    · rw [if_pos hρi, if_pos (Set.mem_iUnion₂.mpr ⟨i, hi, hρi⟩)]
    · intro j hj hji
      rw [if_neg]
      intro hρj
      exact Set.disjoint_left.mp (hdisj j hj i hi hji) hρj hρi
    · intro h
      exact absurd hi h
  · push Not at hmem
    rw [Finset.sum_eq_zero (fun i hi => if_neg (hmem i hi)), if_neg]
    intro h
    rw [Set.mem_iUnion₂] at h
    obtain ⟨i, hi, hρ⟩ := h
    exact hmem i hi hρ

/-- The square of half-side `η` about `z`: its corners. -/
theorem square_corner_re (z : ℂ) (η : ℝ) : (z - (η : ℂ) * (1 + I)).re = z.re - η := by simp
theorem square_corner_im (z : ℂ) (η : ℝ) : (z - (η : ℂ) * (1 + I)).im = z.im - η := by simp
theorem square_corner_re' (z : ℂ) (η : ℝ) : (z + (η : ℂ) * (1 + I)).re = z.re + η := by simp
theorem square_corner_im' (z : ℂ) (η : ℝ) : (z + (η : ℂ) * (1 + I)).im = z.im + η := by simp

theorem norm_sub_le_of_mem_closedRect_square {z ζ : ℂ} {η : ℝ} (hη : 0 < η)
    (hζ : ζ ∈ closedRect (z - (η : ℂ) * (1 + I)) (z + (η : ℂ) * (1 + I))) :
    ‖ζ - z‖ ≤ 2 * η := by
  rw [closedRect, Complex.mem_reProdIm, square_corner_re, square_corner_im, square_corner_re',
    square_corner_im', Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hζ
  calc ‖ζ - z‖ ≤ |(ζ - z).re| + |(ζ - z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ η + η := by
        gcongr
        · rw [sub_re, abs_le]; constructor <;> linarith [hζ.1.1, hζ.1.2]
        · rw [sub_im, abs_le]; constructor <;> linarith [hζ.2.1, hζ.2.2]
    _ = 2 * η := by ring

theorem mem_openRect_square {z : ℂ} {η : ℝ} (hη : 0 < η) :
    z ∈ openRect (z - (η : ℂ) * (1 + I)) (z + (η : ℂ) * (1 + I)) := by
  apply mem_openRect_of_bounds
  · rw [square_corner_re, square_corner_im, square_corner_re', square_corner_im']
    constructor <;> linarith
  · rw [square_corner_re, square_corner_im, square_corner_re', square_corner_im']
    constructor <;> constructor <;> linarith

/-- A square about each non-real root, avoiding the other roots and the real axis. -/
theorem exists_square_radius (P : ℂ[X]) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ η > 0, (∀ ρ ∈ P.roots, ρ ≠ z → 4 * η < ‖ρ - z‖) ∧ 2 * η ≤ |z.im| := by
  classical
  set T := P.roots.toFinset.erase z with hT
  have hzim : 0 < |z.im| := abs_pos.mpr hz
  by_cases hTe : T.Nonempty
  · set m := T.inf' hTe (fun ρ => ‖ρ - z‖) with hm
    have hm0 : 0 < m := by
      rw [hm, Finset.lt_inf'_iff]
      intro ρ hρ
      rw [hT, Finset.mem_erase] at hρ
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hρ.1)
    refine ⟨min (m / 8) (|z.im| / 2), by positivity, ?_, ?_⟩
    · intro ρ hρ hρz
      have hmem : ρ ∈ T := by
        rw [hT, Finset.mem_erase, Multiset.mem_toFinset]
        exact ⟨hρz, hρ⟩
      have := Finset.inf'_le (fun ρ => ‖ρ - z‖) hmem
      rw [← hm] at this
      have hmin := min_le_left (m / 8) (|z.im| / 2)
      linarith
    · have := min_le_right (m / 8) (|z.im| / 2)
      linarith
  · refine ⟨|z.im| / 2, by positivity, ?_, by linarith⟩
    intro ρ hρ hρz
    exfalso
    apply hTe
    refine ⟨ρ, ?_⟩
    rw [hT, Finset.mem_erase, Multiset.mem_toFinset]
    exact ⟨hρz, hρ⟩

theorem card_filter_im_eq (P : ℂ[X]) :
    Multiset.card (P.roots.filter fun z => ¬ z.im = 0) = rootCount P {ζ : ℂ | ¬ ζ.im = 0} := by
  rw [rootCount_eq_card_filter]
  congr 1
  simp only [Set.mem_ofPred_eq]

/-- **Hurwitz: the non-real root count is lower semicontinuous.**  Under coefficientwise
convergence `q N → p` of real polynomials of bounded degree with `p ≠ 0`, eventually
`nonreal p ≤ nonreal (q N)`. -/
theorem nonreal_le_of_tendsto {q : ℕ → ℝ[X]} {p : ℝ[X]} {n : ℕ}
    (hdeg : ∀ N, (q N).natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hcoeff : ∀ k, Tendsto (fun N => (q N).coeff k) atTop (𝓝 (p.coeff k))) (hp0 : p ≠ 0) :
    ∀ᶠ N in atTop,
      Soma.Holonics.RH.PolyaStep.nonreal p ≤ Soma.Holonics.RH.PolyaStep.nonreal (q N) := by
  classical
  set P : ℂ[X] := p.map ofRealHom with hP
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hp0
  have hdegP : ∀ N, ((q N).map ofRealHom).natDegree ≤ n := fun N => by
    rw [natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact hdeg N
  have hpP : P.natDegree ≤ n := by
    rw [hP, natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact hp
  have hcoeffP : ∀ k, Tendsto (fun N => ((q N).map ofRealHom).coeff k) atTop (𝓝 (P.coeff k)) := by
    intro k
    simp only [hP, coeff_map]
    exact (Complex.continuous_ofReal.tendsto _).comp (hcoeff k)
  set S := P.roots.toFinset.filter (fun z => ¬ z.im = 0) with hS
  have hsq : ∀ z, z ∈ S →
      ∃ η > 0, (∀ ρ ∈ P.roots, ρ ≠ z → 4 * η < ‖ρ - z‖) ∧ 2 * η ≤ |z.im| := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    exact exists_square_radius P hz.2
  choose! η hη using hsq
  set lo : ℂ → ℂ := fun z => z - (η z : ℂ) * (1 + I) with hlo
  set hi : ℂ → ℂ := fun z => z + (η z : ℂ) * (1 + I) with hhi
  have hzw : ∀ z ∈ S, (lo z).re < (hi z).re ∧ (lo z).im < (hi z).im := by
    intro z hz
    have := (hη z hz).1
    simp only [hlo, hhi, square_corner_re, square_corner_im, square_corner_re', square_corner_im']
    constructor <;> linarith
  have hbd : ∀ z ∈ S, ∀ ρ ∈ P.roots, ρ ∉ boundaryRect (lo z) (hi z) := by
    intro z hz ρ hρ hρb
    obtain ⟨hη0, hfar, -⟩ := hη z hz
    by_cases hρz : ρ = z
    · subst hρz
      exact hρb.2 (mem_openRect_square hη0)
    · have h1 := hfar ρ hρ hρz
      have h2 := norm_sub_le_of_mem_closedRect_square hη0
        (boundaryRect_subset_closedRect _ _ hρb)
      linarith
  have hev : ∀ᶠ N in atTop, ∀ z ∈ S,
      rootCount ((q N).map ofRealHom) (openRect (lo z) (hi z)) =
        rootCount P (openRect (lo z) (hi z)) := by
    rw [Filter.eventually_all_finset]
    intro z hz
    exact eventually_rootCount_eq hdegP hpP hcoeffP hP0 (hzw z hz) (hbd z hz)
  filter_upwards [hev] with N hN
  have hcount : ∀ z ∈ S, rootCount P (openRect (lo z) (hi z)) = rootMultiplicity z P := by
    intro z hz
    obtain ⟨hη0, hfar, -⟩ := hη z hz
    unfold rootCount
    rw [Finset.sum_eq_single z]
    · rw [if_pos (mem_openRect_square hη0)]
    · intro ρ hρ hρz
      rw [if_neg]
      intro hin
      have h1 := hfar ρ (Multiset.mem_toFinset.mp hρ) hρz
      have h2 := norm_sub_le_of_mem_closedRect_square hη0 (openRect_subset_closedRect _ _ hin)
      linarith
    · intro hz'
      exfalso
      apply hz'
      rw [hS, Finset.mem_filter] at hz
      exact hz.1
  have hdisj : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' →
      Disjoint (openRect (lo z) (hi z)) (openRect (lo z') (hi z')) := by
    intro z hz z' hz' hne
    rw [Set.disjoint_left]
    intro ζ h1 h2
    obtain ⟨hη0, hfar, -⟩ := hη z hz
    obtain ⟨hη0', hfar', -⟩ := hη z' hz'
    have hzr : z ∈ P.roots := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hz).1
    have hzr' : z' ∈ P.roots := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hz').1
    have a1 := hfar z' hzr' (Ne.symm hne)
    have a2 := hfar' z hzr hne
    have b1 := norm_sub_le_of_mem_closedRect_square hη0 (openRect_subset_closedRect _ _ h1)
    have b2 := norm_sub_le_of_mem_closedRect_square hη0' (openRect_subset_closedRect _ _ h2)
    have htri : ‖z - z'‖ ≤ ‖ζ - z‖ + ‖ζ - z'‖ := by
      calc ‖z - z'‖ = ‖(ζ - z') - (ζ - z)‖ := by ring_nf
        _ ≤ ‖ζ - z'‖ + ‖ζ - z‖ := norm_sub_le _ _
        _ = ‖ζ - z‖ + ‖ζ - z'‖ := add_comm _ _
    rw [norm_sub_rev z' z] at a1
    linarith
  have hunion : (⋃ z ∈ S, openRect (lo z) (hi z)) ⊆ {ζ : ℂ | ¬ ζ.im = 0} := by
    intro ζ hζ
    rw [Set.mem_iUnion₂] at hζ
    obtain ⟨z, hz, hζz⟩ := hζ
    obtain ⟨hη0, -, hhalf⟩ := hη z hz
    have := (openRect_bounds (hzw z hz) hζz).2
    simp only [hlo, hhi, square_corner_im, square_corner_im'] at this
    show ¬ ζ.im = 0
    intro h0
    rw [h0] at this
    rcases abs_cases z.im with ⟨habs, _⟩ | ⟨habs, _⟩ <;> linarith
  have hleft : Soma.Holonics.RH.PolyaStep.nonreal p = ∑ z ∈ S, rootMultiplicity z P := by
    rw [Soma.Holonics.RH.PolyaStep.nonreal_eq_card_filter, card_filter_im_eq]
    unfold rootCount
    rw [hS, Finset.sum_filter]
    simp only [hP, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  have hright : Soma.Holonics.RH.PolyaStep.nonreal (q N) =
      rootCount ((q N).map ofRealHom) {ζ : ℂ | ¬ ζ.im = 0} := by
    rw [Soma.Holonics.RH.PolyaStep.nonreal_eq_card_filter, card_filter_im_eq]
  rw [hleft, hright]
  calc ∑ z ∈ S, rootMultiplicity z P
      = ∑ z ∈ S, rootCount ((q N).map ofRealHom) (openRect (lo z) (hi z)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hN z hz, hcount z hz]
    _ = rootCount ((q N).map ofRealHom) (⋃ z ∈ S, openRect (lo z) (hi z)) :=
        sum_rootCount_disjoint _ S _ hdisj
    _ ≤ rootCount ((q N).map ofRealHom) {ζ : ℂ | ¬ ζ.im = 0} := rootCount_mono _ hunion

end Soma.Holonics.RH.HurwitzPolynomial
