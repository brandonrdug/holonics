import ElementaryHolonics.RH.HurwitzPolynomial
import ElementaryHolonics.RH.PairDescent

/-!
# Forward preservation: the backward heat flow never creates a pair

The Euler iterate `(1 − (t/N) D²)^N p` is a binomial sum of even derivatives whose coefficients
`C(N,k)(−t/N)^k` converge to `(−t)^k/k!`, the coefficients of `e^{−tD²}p`.  Each Euler step
never increases the non-real root count (Hermite–Poulain), the count is lower semicontinuous
in the limit (Hurwitz), so `nonreal (e^{−tD²} p) ≤ nonreal p` for `t ≥ 0`.  With the semigroup
law the count is non-increasing along the flow: forward in `t` the pair population only dies.
-/

open Polynomial Finset Filter Topology
open Soma.Holonics.RH.PolyaStep
open Soma.Holonics.RH.PairDescent
open Soma.Holonics.RH.HurwitzPolynomial

namespace Soma.Holonics.RH.ForwardPreservation

/-! ## The heat step as an endomorphism and its binomial iterate -/

/-- The derivative as an endomorphism of `ℝ[X]`. -/
noncomputable def D : Module.End ℝ ℝ[X] := Polynomial.derivative

theorem D_pow_apply (k : ℕ) (p : ℝ[X]) : (D ^ k) p = derivative^[k] p := by
  rw [Module.End.pow_apply]
  rfl

theorem heatStep_eq_end (lam : ℝ) (p : ℝ[X]) :
    heatStep lam p = ((-lam) • D ^ 2 + 1 : Module.End ℝ ℝ[X]) p := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, D_pow_apply]
  unfold heatStep
  rw [C_mul', neg_smul, sub_eq_add_neg, add_comm]

theorem heatStep_iterate_eq_end (lam : ℝ) (N : ℕ) (p : ℝ[X]) :
    (heatStep lam)^[N] p = (((-lam) • D ^ 2 + 1 : Module.End ℝ ℝ[X]) ^ N) p := by
  rw [Module.End.pow_apply]
  induction N generalizing p with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, heatStep_eq_end]

/-- **The binomial iterate**: `(1 − λD²)^N p = Σ_k C(N,k)(−λ)^k p^{(2k)}`. -/
theorem heatStep_iterate_eq_sum (lam : ℝ) (N : ℕ) (p : ℝ[X]) :
    (heatStep lam)^[N] p =
      ∑ k ∈ range (N + 1), ((N.choose k : ℝ) * (-lam) ^ k) • derivative^[2 * k] p := by
  rw [heatStep_iterate_eq_end, (Commute.one_right ((-lam) • D ^ 2)).add_pow N,
    LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_pow, mul_one, Module.End.mul_apply, Module.End.natCast_apply, _root_.smul_pow,
    ← pow_mul, LinearMap.smul_apply, D_pow_apply, ← Nat.cast_smul_eq_nsmul ℝ,
    iterate_derivative_smul, smul_smul, mul_comm]

/-! ## The Euler coefficients converge to the flow's -/

theorem tendsto_sub_div (i : ℕ) :
    Tendsto (fun N : ℕ => (((N - i : ℕ) : ℝ) / N)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (1 : ℝ) - (i : ℝ) / N) atTop (𝓝 1) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)
    simpa using tendsto_const_nhds.sub this
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max i 1)] with N hN
  have hi : i ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast (by omega : N ≠ 0)
  rw [Nat.cast_sub hi]
  field_simp

/-- **The scalar limit**: `C(N,k)(−t/N)^k → (−t)^k/k!`. -/
theorem tendsto_choose_mul_pow (t : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => (N.choose k : ℝ) * (-t / N) ^ k) atTop (𝓝 ((-t) ^ k / (k.factorial : ℝ))) := by
  have hprod : Tendsto (fun N : ℕ => ∏ i ∈ range k, (((N - i : ℕ) : ℝ) / N)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (range k) fun i _ => tendsto_sub_div i
    simpa using this
  have hlim : Tendsto (fun N : ℕ => (-t) ^ k / (k.factorial : ℝ) *
      ∏ i ∈ range k, (((N - i : ℕ) : ℝ) / N)) atTop (𝓝 ((-t) ^ k / (k.factorial : ℝ))) := by
    simpa using tendsto_const_nhds.mul hprod
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hchoose : (N.choose k : ℝ) = (N.descFactorial k : ℝ) / (k.factorial : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  have hdesc : (N.descFactorial k : ℝ) = ∏ i ∈ range k, ((N - i : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    rfl
  rw [hchoose, hdesc, div_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  field_simp

/-! ## The iterate converges to the flow coefficientwise -/

theorem coeff_heatStep_iterate (lam : ℝ) (N : ℕ) (p : ℝ[X]) (j : ℕ) :
    ((heatStep lam)^[N] p).coeff j =
      ∑ k ∈ range (N + 1), (N.choose k : ℝ) * (-lam) ^ k * (derivative^[2 * k] p).coeff j := by
  rw [heatStep_iterate_eq_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_smul, smul_eq_mul]

theorem coeff_heatR (t : ℝ) (p : ℝ[X]) (j : ℕ) :
    (heatR t p).coeff j = ∑ k ∈ range (p.natDegree + 1),
      (-t) ^ k / (k.factorial : ℝ) * (derivative^[2 * k] p).coeff j := by
  unfold heatR
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_C_mul]

theorem iterate_derivative_coeff_eq_zero {p : ℝ[X]} {k : ℕ} (hk : p.natDegree < k) (j : ℕ) :
    (derivative^[2 * k] p).coeff j = 0 := by
  rw [iterate_derivative_eq_zero (by omega : p.natDegree < 2 * k), coeff_zero]

theorem tendsto_coeff_iterate (t : ℝ) (p : ℝ[X]) (j : ℕ) :
    Tendsto (fun N : ℕ => ((heatStep (t / N))^[N] p).coeff j) atTop (𝓝 ((heatR t p).coeff j)) := by
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ range (p.natDegree + 1),
      (N.choose k : ℝ) * (-(t / N)) ^ k * (derivative^[2 * k] p).coeff j) atTop
      (𝓝 ((heatR t p).coeff j)) := by
    rw [coeff_heatR]
    apply tendsto_finsetSum
    intro k _
    have := (tendsto_choose_mul_pow t k).mul_const ((derivative^[2 * k] p).coeff j)
    simpa [neg_div] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop p.natDegree] with N hN
  rw [coeff_heatStep_iterate]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro k _ hk'
  have hk'' : p.natDegree + 1 ≤ k := by simpa [Finset.mem_range] using hk'
  rw [iterate_derivative_coeff_eq_zero (by omega), mul_zero]

theorem natDegree_heatStep_iterate_le (lam : ℝ) (N : ℕ) (p : ℝ[X]) :
    ((heatStep lam)^[N] p).natDegree ≤ p.natDegree := by
  rw [heatStep_iterate_eq_sum]
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_smul_le _ _).trans ((natDegree_iterate_derivative p _).trans (Nat.sub_le _ _))

theorem natDegree_heatR_le (t : ℝ) (p : ℝ[X]) : (heatR t p).natDegree ≤ p.natDegree := by
  unfold heatR
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative p _).trans (Nat.sub_le _ _))

/-! ## Forward preservation -/

theorem nonreal_heatStep_iterate_le {lam : ℝ} (hlam : 0 ≤ lam) (N : ℕ) (p : ℝ[X]) :
    nonreal ((heatStep lam)^[N] p) ≤ nonreal p := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact (nonreal_heatStep_le hlam _).trans ih

/-- **Forward preservation**: `e^{−tD²}` never increases the non-real root count. -/
theorem nonreal_heatR_le {t : ℝ} (ht : 0 ≤ t) (p : ℝ[X]) : nonreal (heatR t p) ≤ nonreal p := by
  rcases eq_or_ne (heatR t p) 0 with h0 | h0
  · rw [h0]
    simp [nonreal]
  have hev := nonreal_le_of_tendsto (q := fun N => (heatStep (t / N))^[N] p) (p := heatR t p)
    (n := p.natDegree) (fun N => natDegree_heatStep_iterate_le _ _ _) (natDegree_heatR_le _ _)
    (tendsto_coeff_iterate t p) h0
  obtain ⟨N, hN⟩ := hev.exists
  exact hN.trans (nonreal_heatStep_iterate_le (div_nonneg ht (Nat.cast_nonneg N)) N p)

end Soma.Holonics.RH.ForwardPreservation
