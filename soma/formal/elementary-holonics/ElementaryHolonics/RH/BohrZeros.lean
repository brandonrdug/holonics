import Mathlib
import ElementaryHolonics.RH.DescentApproximation

/-!
# RT5: the Dirichlet series `F_t` has zeros at every height in a fixed strip

`F_t` is entire with quadratic exponential growth; if it were zero-free, `log ‖F_t‖` would be the
real part of an entire function of quadratic growth, hence a quadratic polynomial by
Borel–Carathéodory and Cauchy's estimates, which the real axis refutes. Then Bohr's almost
periodicity carries the zero to every height.
-/

noncomputable section

namespace Soma.Holonics.RH.BohrZeros

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.DescentApproximation

/-! ## `F_t` is entire -/

theorem differentiable_Fterm (t : ℝ) (n : ℤ) : Differentiable ℂ (fun s => Fterm t s n) := by
  unfold Fterm
  split_ifs
  · exact differentiable_const _
  · fun_prop

/-- The one-sided bound: it uses only `−X ≤ Re s`. -/
theorem norm_Fterm_le' {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : -X ≤ s.re)
    (n : ℤ) :
    ‖Fterm t s n‖ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst hn
    simp [Fterm]
  have hL0 := log_abs_nonneg hn
  rw [norm_Fterm t s hn, ← Real.exp_add]
  have hx : -s.re ≤ X := by linarith
  calc Real.exp (-t * Real.log |(n : ℝ)| ^ 2 + -s.re * Real.log |(n : ℝ)|)
      ≤ Real.exp (X * Real.log |(n : ℝ)| - t * Real.log |(n : ℝ)| ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hx hL0]
    _ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        exp_neg_mul_log_sq_le ht hn hX0

theorem differentiable_Ft {t : ℝ} (ht : 0 < t) : Differentiable ℂ (Ft t) := by
  intro s
  set X : ℝ := |s.re| + 1 with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hU : IsOpen {z : ℂ | -X < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, Fterm t w n) {z : ℂ | -X < z.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_Z32.mul_left
      (Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t))))
      (fun n => (differentiable_Fterm t n).differentiableOn) hU
      (fun n w hw => norm_Fterm_le' ht hX0 (le_of_lt hw) n)
  have hmem : s ∈ {z : ℂ | -X < z.re} := by
    show -X < s.re
    linarith [neg_abs_le s.re]
  exact (hd.differentiableAt (hU.mem_nhds hmem))

/-! ## Growth -/

theorem Z32_pos : 0 < Z32 := by
  unfold Z32
  have h := le_hasSum summable_Z32.hasSum 1 (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  have : |((1 : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ)) = 1 := by simp
  linarith

theorem norm_Ft_le {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖Ft t s‖ ≤ Real.exp (s.re ^ 2 / (2 * t) + 9 / (8 * t)) * Z32 := by
  unfold Ft
  refine (norm_tsum_le_tsum_norm (summable_norm_Fterm ht s)).trans ?_
  have := tsum_norm_Fterm_le ht (X := |s.re|) (s := s) le_rfl
  rwa [sq_abs] at this

theorem log_norm_Ft_le {t : ℝ} (ht : 0 < t) (s : ℂ) (hF : Ft t s ≠ 0) :
    Real.log ‖Ft t s‖ ≤ s.re ^ 2 / (2 * t) + 9 / (8 * t) + Real.log Z32 := by
  have h := norm_Ft_le ht s
  have hpos : 0 < ‖Ft t s‖ := norm_pos_iff.mpr hF
  calc Real.log ‖Ft t s‖ ≤ Real.log (Real.exp (s.re ^ 2 / (2 * t) + 9 / (8 * t)) * Z32) :=
        Real.log_le_log hpos h
    _ = s.re ^ 2 / (2 * t) + 9 / (8 * t) + Real.log Z32 := by
        rw [Real.log_mul (Real.exp_pos _).ne' Z32_pos.ne', Real.log_exp]

/-! ## The real axis -/

/-- The real form of the main term at real `x`. -/
def Fr (t x : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-t * Real.log |(n : ℝ)| ^ 2) * Real.exp (-x * Real.log |(n : ℝ)|)

theorem Fr_nonneg (t x : ℝ) (n : ℤ) : 0 ≤ Fr t x n := by
  unfold Fr
  split_ifs <;> positivity

theorem Fterm_ofReal (t x : ℝ) (n : ℤ) : Fterm t (x : ℂ) n = ((Fr t x n : ℝ) : ℂ) := by
  unfold Fterm Fr
  split_ifs with hn
  · simp
  · push_cast
    first | rfl | ring_nf

theorem norm_Fterm_eq_Fr (t x : ℝ) (n : ℤ) : ‖Fterm t (x : ℂ) n‖ = Fr t x n := by
  rw [Fterm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Fr_nonneg t x n)]

theorem summable_Fr {t : ℝ} (ht : 0 < t) (x : ℝ) : Summable (Fr t x) := by
  have := summable_norm_Fterm ht (x : ℂ)
  simpa [norm_Fterm_eq_Fr] using this

theorem Ft_ofReal {t : ℝ} (ht : 0 < t) (x : ℝ) : Ft t (x : ℂ) = ((∑' n : ℤ, Fr t x n : ℝ) : ℂ) := by
  unfold Ft
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  exact Fterm_ofReal t x n

theorem norm_Ft_ofReal {t : ℝ} (ht : 0 < t) (x : ℝ) : ‖Ft t (x : ℂ)‖ = ∑' n : ℤ, Fr t x n := by
  rw [Ft_ofReal ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact tsum_nonneg (Fr_nonneg t x)

theorem Fr_one (t x : ℝ) : Fr t x 1 = 1 := by simp [Fr]
theorem Fr_neg_one (t x : ℝ) : Fr t x (-1) = 1 := by simp [Fr]
theorem Fr_two (t : ℝ) : Fr t 0 2 = Real.exp (-t * Real.log 2 ^ 2) := by
  simp [Fr]
theorem Fr_neg_two (t : ℝ) : Fr t 0 (-2) = Real.exp (-t * Real.log 2 ^ 2) := by
  simp [Fr]

/-- `‖F_t(0)‖ ≥ 2 + 2 e^{−t log² 2}`. -/
theorem norm_Ft_zero_ge {t : ℝ} (ht : 0 < t) :
    2 + 2 * Real.exp (-t * Real.log 2 ^ 2) ≤ ‖Ft t 0‖ := by
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  rw [← h0, norm_Ft_ofReal ht]
  have hs := summable_Fr ht 0
  have h := hs.sum_le_tsum ({1, -1, 2, -2} : Finset ℤ) (fun n _ => Fr_nonneg t 0 n)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fr_one, Fr_neg_one, Fr_two, Fr_neg_two] at h
  linarith

/-- `‖F_t(x)‖ ≥ 2` on the real axis. -/
theorem norm_Ft_ofReal_ge {t : ℝ} (ht : 0 < t) (x : ℝ) : 2 ≤ ‖Ft t (x : ℂ)‖ := by
  rw [norm_Ft_ofReal ht]
  have hs := summable_Fr ht x
  have h := hs.sum_le_tsum ({1, -1} : Finset ℤ) (fun n _ => Fr_nonneg t x n)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, Fr_one, Fr_neg_one] at h
  linarith

/-- `‖F_t(x)‖ ≤ 2 + 2^{−x} ‖F_t(0)‖` for `x ≥ 0`. -/
theorem norm_Ft_ofReal_le {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : 0 ≤ x) :
    ‖Ft t (x : ℂ)‖ ≤ 2 + (2 : ℝ) ^ (-x) * ‖Ft t 0‖ := by
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  rw [norm_Ft_ofReal ht, ← h0, norm_Ft_ofReal ht]
  -- pointwise: `Fr t x n ≤ g n + 2^{−x} Fr t 0 n` with `g` the indicator of `{1, −1}`
  set g : ℤ → ℝ := fun n => if n = 1 ∨ n = -1 then 1 else 0 with hg
  have hg_sum : ∑' n, g n = 2 := by
    rw [tsum_eq_sum (s := ({1, -1} : Finset ℤ)) (fun n hn => by
      simp only [hg]
      rw [if_neg]
      intro h
      rcases h with h | h <;> simp [h] at hn)]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [hg]
    norm_num
  have hpt : ∀ n, Fr t x n ≤ g n + (2 : ℝ) ^ (-x) * Fr t 0 n := by
    intro n
    by_cases h1 : n = 1 ∨ n = -1
    · have hFr : Fr t x n = 1 := by rcases h1 with h | h <;> simp [h, Fr]
      have : 0 ≤ (2 : ℝ) ^ (-x) * Fr t 0 n := by
        have := Fr_nonneg t 0 n
        positivity
      simp only [hg, if_pos h1]
      linarith
    · simp only [hg, if_neg h1, zero_add]
      by_cases hn : n = 0
      · subst hn; simp [Fr]
      · unfold Fr
        rw [if_neg hn, if_neg hn]
        have hn2 : (2 : ℝ) ≤ |(n : ℝ)| := by
          push_neg at h1
          have : (2 : ℤ) ≤ |n| := by
            rcases le_or_gt 0 n with h | h
            · rw [abs_of_nonneg h]; omega
            · rw [abs_of_neg h]; omega
          exact_mod_cast this
        have hL2 : Real.log 2 ≤ Real.log |(n : ℝ)| := Real.log_le_log (by norm_num) hn2
        have e1 : Real.exp (-x * Real.log |(n : ℝ)|) ≤ (2 : ℝ) ^ (-x) := by
          rw [Real.rpow_def_of_pos (by norm_num)]
          apply Real.exp_le_exp.mpr
          nlinarith
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
        have := Real.exp_pos (-t * Real.log |(n : ℝ)| ^ 2)
        nlinarith
  have hsg : Summable g := by
    apply summable_of_ne_finset_zero (s := ({1, -1} : Finset ℤ))
    intro n hn
    simp only [hg]
    rw [if_neg]
    intro h
    rcases h with h | h <;> simp [h] at hn
  have hs0 := (summable_Fr ht 0).mul_left ((2 : ℝ) ^ (-x))
  calc ∑' n, Fr t x n ≤ ∑' n, (g n + (2 : ℝ) ^ (-x) * Fr t 0 n) :=
        hasSum_le hpt (summable_Fr ht x).hasSum (hsg.add hs0).hasSum
    _ = 2 + (2 : ℝ) ^ (-x) * ∑' n, Fr t 0 n := by
        rw [hsg.tsum_add hs0, hg_sum, tsum_mul_left]

/-! ## A zero-free `F_t` would be the exponential of a quadratic -/

open InnerProductSpace in
theorem exists_analytic_re_eq_log {t : ℝ} (ht : 0 < t) (h0 : ∀ s, Ft t s ≠ 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ s, (H s).re = Real.log ‖Ft t s‖ := by
  have hharm : HarmonicOnNhd (fun s => Real.log ‖Ft t s‖) univ := by
    intro s _
    exact ((differentiable_Ft ht).analyticAt s).harmonicAt_log_norm (h0 s)
  obtain ⟨H, hH, hre⟩ := HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq hharm
  refine ⟨H, ?_, fun s => ?_⟩
  · exact differentiableOn_univ.mp hH.differentiableOn
  · exact congrFun hre s

/-- Borel–Carathéodory: a quadratic bound on `Re H` gives a quadratic bound on `‖H‖`. -/
theorem norm_H_le {H : ℂ → ℂ} (hH : Differentiable ℂ H) {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hre : ∀ s, (H s).re ≤ C₁ + C₂ * ‖s‖ ^ 2) {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖H z‖ ≤ ‖H 0‖ + 2 * (|C₁| + ‖H 0‖ + 4 * C₂ * R ^ 2 + 1) := by
  set M : ℝ := |C₁| + ‖H 0‖ + 4 * C₂ * R ^ 2 + 1 with hM
  have hMpos : 0 < M := by positivity
  set f : ℂ → ℂ := fun s => H s - H 0 with hf
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 (2 * R)) := (hH.sub_const _).differentiableOn
  have hf₁ : Set.MapsTo f (Metric.ball 0 (2 * R)) {z | z.re ≤ M} := by
    intro s hs
    simp only [Set.mem_setOf_eq, hf, Complex.sub_re]
    have h1 := hre s
    have hs' : ‖s‖ < 2 * R := by simpa using hs
    have h2 : C₂ * ‖s‖ ^ 2 ≤ C₂ * (2 * R) ^ 2 := by gcongr
    have h3 := Complex.abs_re_le_norm (H 0)
    have h4 := neg_abs_le (H 0).re
    nlinarith [le_abs_self C₁, abs_nonneg C₁]
  have hz' : z ∈ Metric.ball 0 (2 * R) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hbc := Complex.borelCaratheodory_zero hMpos hfd hf₁ (by positivity) hz' (by simp [hf])
  have h2 : 2 * M * ‖z‖ / (2 * R - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg z]
  calc ‖H z‖ = ‖f z + H 0‖ := by simp [hf]
    _ ≤ ‖f z‖ + ‖H 0‖ := norm_add_le _ _
    _ ≤ 2 * M + ‖H 0‖ := by linarith
    _ = ‖H 0‖ + 2 * M := by ring

/-- Cauchy's estimate: the third derivative of an entire function of quadratic growth vanishes. -/
theorem iteratedDeriv_three_eq_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H) {C₁ C₂ : ℝ}
    (hC₂ : 0 ≤ C₂) (hre : ∀ s, (H s).re ≤ C₁ + C₂ * ‖s‖ ^ 2) (c : ℂ) :
    iteratedDeriv 3 H c = 0 := by
  set A : ℝ := ‖H 0‖ + 2 * (|C₁| + ‖H 0‖ + 16 * C₂ + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  have hbound : ∀ R, 1 ≤ R → ‖c‖ ≤ R → ‖iteratedDeriv 3 H c‖ ≤ 6 * A / R := by
    intro R hR hcR
    have hR0 : 0 < R := by linarith
    have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 hR0
      hH.diffContOnCl (C := ‖H 0‖ + 2 * (|C₁| + ‖H 0‖ + 4 * C₂ * (‖c‖ + R) ^ 2 + 1)) (fun z hz => by
        have hz' : ‖z‖ ≤ ‖c‖ + R := by
          have hd : dist z c = R := hz
          calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
            _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
            _ = R + ‖c‖ := by rw [← dist_eq_norm, hd]
            _ = ‖c‖ + R := by ring
        exact norm_H_le hH hC₂ hre (by positivity : 0 < ‖c‖ + R) hz')
    refine hcau.trans ?_
    have hnum : ‖H 0‖ + 2 * (|C₁| + ‖H 0‖ + 4 * C₂ * (‖c‖ + R) ^ 2 + 1) ≤ A * R ^ 2 := by
      have e1 : (‖c‖ + R) ^ 2 ≤ 4 * R ^ 2 := by nlinarith [norm_nonneg c]
      have e2 : 1 ≤ R ^ 2 := by nlinarith
      have e3 : C₂ * (‖c‖ + R) ^ 2 ≤ C₂ * (4 * R ^ 2) := by gcongr
      rw [hA]
      nlinarith [norm_nonneg (H 0), abs_nonneg C₁]
    calc (Nat.factorial 3 : ℝ) * (‖H 0‖ + 2 * (|C₁| + ‖H 0‖ + 4 * C₂ * (‖c‖ + R) ^ 2 + 1)) / R ^ 3
        ≤ (Nat.factorial 3 : ℝ) * (A * R ^ 2) / R ^ 3 := by gcongr
      _ = 6 * A / R := by
          rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num]
          field_simp
          first | done | ring
  by_contra hne
  have hpos : 0 < ‖iteratedDeriv 3 H c‖ := norm_pos_iff.mpr hne
  set D := ‖iteratedDeriv 3 H c‖ with hD
  set R : ℝ := max (max 1 ‖c‖) (6 * A / D + 1) with hR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRc : ‖c‖ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRA : 6 * A / D + 1 ≤ R := le_max_right _ _
  have hb := hbound R hR1 hRc
  have hR0 : 0 < R := by linarith
  have : 6 * A / R < D := by
    rw [div_lt_iff₀ hR0]
    have : 6 * A / D * D = 6 * A := by field_simp
    nlinarith
  linarith

/-- An entire function with vanishing third derivative is a quadratic. -/
theorem eq_quadratic_of_iteratedDeriv_three {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h3 : ∀ c, iteratedDeriv 3 H c = 0) :
    ∀ s, H s = H 0 + deriv H 0 * s + iteratedDeriv 2 H 0 / 2 * s ^ 2 := by
  have hD1 : Differentiable ℂ (deriv H) := hH.deriv
  have hD2 : Differentiable ℂ (deriv (deriv H)) := hD1.deriv
  have h3' : ∀ c, deriv (deriv (deriv H)) c = 0 := by
    intro c
    have := h3 c
    rwa [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at this
  have hconst2 : ∀ s, deriv (deriv H) s = deriv (deriv H) 0 :=
    fun s => is_const_of_deriv_eq_zero hD2 h3' s 0
  set a := deriv (deriv H) 0 with ha
  have hD1eq : ∀ s, deriv H s = deriv H 0 + a * s := by
    intro s
    have hφ : Differentiable ℂ (fun s => deriv H s - a * s) := hD1.sub (differentiable_id.const_mul _)
    have hφ' : ∀ x, deriv (fun s => deriv H s - a * s) x = 0 := by
      intro x
      have hd : HasDerivAt (fun s => deriv H s - a * s) (deriv (deriv H) x - a * 1) x :=
        (hD1 x).hasDerivAt.sub ((hasDerivAt_id x).const_mul a)
      rw [hd.deriv, hconst2 x]
      ring
    have := is_const_of_deriv_eq_zero hφ hφ' s 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this
  intro s
  have hψ : Differentiable ℂ (fun s => H s - (H 0 + deriv H 0 * s + a / 2 * s ^ 2)) := by
    fun_prop
  have hψ' : ∀ x, deriv (fun s => H s - (H 0 + deriv H 0 * s + a / 2 * s ^ 2)) x = 0 := by
    intro x
    have hd : HasDerivAt (fun s => H s - (H 0 + deriv H 0 * s + a / 2 * s ^ 2))
        (deriv H x - (0 + deriv H 0 * 1 + a / 2 * (2 * x))) x := by
      apply HasDerivAt.sub (hH x).hasDerivAt
      apply HasDerivAt.add (HasDerivAt.add (hasDerivAt_const _ _) ((hasDerivAt_id x).const_mul _))
      have := (hasDerivAt_pow 2 x).const_mul (a / 2)
      simpa using this
    rw [hd.deriv, hD1eq x]
    ring
  have := is_const_of_deriv_eq_zero hψ hψ' s 0
  simp only [mul_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_self] at this
  have h2 : iteratedDeriv 2 H 0 = a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  linear_combination this

/-- A real quadratic bounded on `[0, ∞)` has no linear or quadratic term. -/
theorem quad_bounded {α β γ B : ℝ} (h : ∀ x : ℝ, 0 ≤ x → |α * x ^ 2 + β * x + γ| ≤ B) :
    α = 0 ∧ β = 0 := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (h 0 le_rfl)
  have hα : α = 0 := by
    by_contra hα
    have hα' : 0 < |α| := abs_pos.mpr hα
    set x : ℝ := (|β| + B + |γ| + 1) / |α| + 1 with hx
    clear_value x
    have hx1 : 1 ≤ x := by
      have : 0 ≤ (|β| + B + |γ| + 1) / |α| := by positivity
      linarith
    have hx0 : 0 ≤ x := by linarith
    have hxα : |α| * x ≥ |β| + B + |γ| + 1 := by
      have : |α| * x = (|β| + B + |γ| + 1) + |α| := by
        rw [hx]
        field_simp
        first | done | ring
      linarith
    have hq := h x hx0
    have hlow : |α * x ^ 2 + β * x + γ| ≥ |α| * x ^ 2 - |β| * x - |γ| := by
      have h1 : |α * x ^ 2 + β * x + γ| ≥ |α * x ^ 2| - |β * x + γ| := by
        have := abs_sub_abs_le_abs_sub (α * x ^ 2) (-(β * x + γ))
        rw [abs_neg, sub_neg_eq_add, ← add_assoc] at this
        linarith
      have h2 : |β * x + γ| ≤ |β| * x + |γ| := by
        calc |β * x + γ| ≤ |β * x| + |γ| := abs_add_le _ _
          _ = |β| * x + |γ| := by rw [abs_mul, abs_of_nonneg hx0]
      rw [abs_mul, abs_pow, abs_of_nonneg hx0] at h1
      linarith
    have e1 : (|β| + B + |γ| + 1) * x ≤ |α| * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hxα hx0
      nlinarith
    have e2 : |β| * x + (B + |γ| + 1) ≤ (|β| + B + |γ| + 1) * x := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ B + |γ| + 1) (sub_nonneg.mpr hx1)]
    linarith [abs_nonneg γ]
  refine ⟨hα, ?_⟩
  subst hα
  by_contra hβ
  have hβ' : 0 < |β| := abs_pos.mpr hβ
  set x : ℝ := (B + |γ| + 1) / |β| with hx
  clear_value x
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxβ : |β| * x = B + |γ| + 1 := by rw [hx]; field_simp
  have hq := h x hx0
  have hlow : |0 * x ^ 2 + β * x + γ| ≥ |β| * x - |γ| := by
    have := abs_sub_abs_le_abs_sub (β * x) (-γ)
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_nonneg hx0] at this
    simp only [zero_mul, zero_add]
    linarith
  linarith

/-- **`F_t` has a zero.** -/
theorem exists_zero_Ft {t : ℝ} (ht : 0 < t) : ∃ s, Ft t s = 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨H, hH, hre⟩ := exists_analytic_re_eq_log ht hno
  have hgrow : ∀ s, (H s).re ≤ (9 / (8 * t) + Real.log Z32) + (1 / (2 * t)) * ‖s‖ ^ 2 := by
    intro s
    rw [hre]
    have h1 := log_norm_Ft_le ht s (hno s)
    have h2 : s.re ^ 2 ≤ ‖s‖ ^ 2 := by
      have := Complex.abs_re_le_norm s
      nlinarith [abs_nonneg s.re, sq_abs s.re]
    have h3 : s.re ^ 2 / (2 * t) ≤ (1 / (2 * t)) * ‖s‖ ^ 2 := by
      rw [div_eq_mul_one_div, mul_comm]
      gcongr
    linarith
  have h3 := iteratedDeriv_three_eq_zero hH (by positivity) hgrow
  have hq := eq_quadratic_of_iteratedDeriv_three hH h3
  set b := deriv H 0 with hb
  set c := iteratedDeriv 2 H 0 / 2 with hc
  have hq' : ∀ x : ℝ, Real.log ‖Ft t (x : ℂ)‖ = c.re * x ^ 2 + b.re * x + (H 0).re := by
    intro x
    rw [← hre, hq (x : ℂ), ← Complex.ofReal_pow]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have hK : 0 ≤ ‖Ft t 0‖ := norm_nonneg _
  -- bounded on `[0, ∞)`
  have hbdd : ∀ x : ℝ, 0 ≤ x →
      |c.re * x ^ 2 + b.re * x + (H 0).re| ≤ |Real.log (2 + ‖Ft t 0‖)| + |Real.log 2| := by
    intro x hx
    rw [← hq' x]
    have hlo := norm_Ft_ofReal_ge ht x
    have hhi := norm_Ft_ofReal_le ht hx
    have h2x : (2 : ℝ) ^ (-x) ≤ 1 := by
      rw [Real.rpow_neg (by norm_num)]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hx)
    have hlog1 : Real.log 2 ≤ Real.log ‖Ft t (x : ℂ)‖ := Real.log_le_log (by norm_num) hlo
    have hlog2 : Real.log ‖Ft t (x : ℂ)‖ ≤ Real.log (2 + ‖Ft t 0‖) := by
      apply Real.log_le_log (by linarith)
      have : (2 : ℝ) ^ (-x) * ‖Ft t 0‖ ≤ 1 * ‖Ft t 0‖ := by gcongr
      linarith
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log 2)
      have := abs_nonneg (Real.log (2 + ‖Ft t 0‖))
      linarith
    · have := le_abs_self (Real.log (2 + ‖Ft t 0‖))
      have := abs_nonneg (Real.log 2)
      linarith
  obtain ⟨hcre, hbre⟩ := quad_bounded hbdd
  -- so `log ‖F_t(x)‖ = log ‖F_t(0)‖` for all `x ≥ 0`
  have hconst : ∀ x : ℝ, 0 ≤ x → Real.log ‖Ft t (x : ℂ)‖ = Real.log ‖Ft t 0‖ := by
    intro x hx
    have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
    rw [hq' x, hcre, hbre, ← h0, hq' 0]
    simp
  -- but `‖F_t(x)‖ ≤ 2 + 2^{−x}‖F_t(0)‖ < 2 + 2e^{−t log² 2} ≤ ‖F_t(0)‖` for `x` large
  have hε : 0 < 2 * Real.exp (-t * Real.log 2 ^ 2) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 2 * Real.exp (-t * Real.log 2 ^ 2) / (‖Ft t 0‖ + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hx : (2 : ℝ) ^ (-(N : ℝ)) * ‖Ft t 0‖ < 2 * Real.exp (-t * Real.log 2 ^ 2) := by
    have e1 : (2 : ℝ) ^ (-(N : ℝ)) = (1 / 2) ^ N := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    rw [e1]
    have hK1 : ‖Ft t 0‖ < ‖Ft t 0‖ + 1 := by linarith
    calc (1 / 2 : ℝ) ^ N * ‖Ft t 0‖ ≤ (1 / 2 : ℝ) ^ N * (‖Ft t 0‖ + 1) := by gcongr
      _ < 2 * Real.exp (-t * Real.log 2 ^ 2) / (‖Ft t 0‖ + 1) * (‖Ft t 0‖ + 1) := by
          gcongr
      _ = 2 * Real.exp (-t * Real.log 2 ^ 2) := by
          field_simp
          first | done | ring
  have hlo := norm_Ft_zero_ge ht
  have hhi := norm_Ft_ofReal_le ht (x := (N : ℝ)) (by positivity)
  have hlt : ‖Ft t ((N : ℝ) : ℂ)‖ < ‖Ft t 0‖ := by linarith
  have hlog := Real.log_lt_log (by linarith [norm_Ft_ofReal_ge ht (N : ℝ)]) hlt
  have := hconst (N : ℝ) (by positivity)
  linarith

/-! ## Bohr: almost periods by simultaneous Diophantine approximation -/

/-- Two reals whose scaled fractional parts share a floor are within `1/Q`. -/
theorem abs_fract_sub_lt_of_floor_eq {Q : ℕ} (hQ : 0 < Q) {a b : ℝ}
    (h : ⌊(Q : ℝ) * Int.fract a⌋₊ = ⌊(Q : ℝ) * Int.fract b⌋₊) :
    |Int.fract b - Int.fract a| < 1 / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha0 : 0 ≤ (Q : ℝ) * Int.fract a := by positivity
  have hb0 : 0 ≤ (Q : ℝ) * Int.fract b := by positivity
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract a)
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract b)
  rw [h] at h1 h2
  rw [abs_sub_lt_iff]
  constructor
  · rw [lt_div_iff₀ hQ']
    nlinarith
  · rw [lt_div_iff₀ hQ']
    nlinarith

/-- **Simultaneous Dirichlet approximation** by pigeonhole: for finitely many reals `θ n`,
`n ∈ s`, and any `Q, q₀`, some integer `q ≥ q₀` has `‖q θ n‖ ≤ 1/Q` for all `n ∈ s`. -/
theorem exists_simultaneous_approx (s : Finset ℤ) (θ : ℤ → ℝ) {Q : ℕ} (hQ : 0 < Q) (q₀ : ℕ) :
    ∃ q : ℕ, q₀ ≤ q ∧ 0 < q ∧ ∀ n ∈ s, ∃ m : ℤ, |(q : ℝ) * θ n - m| ≤ 1 / Q := by
  classical
  set J : ℕ := Q ^ s.card + 1 with hJ
  set box : ℕ → (s → ℕ) := fun j n => ⌊(Q : ℝ) * Int.fract (((j * (q₀ + 1) : ℕ) : ℝ) * θ n)⌋₊
    with hbox
  have hmaps : ∀ j ∈ Finset.range J, box j ∈ Fintype.piFinset (fun _ : s => Finset.range Q) := by
    intro j _
    rw [Fintype.mem_piFinset]
    intro n
    rw [Finset.mem_range]
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have : (Q : ℝ) * Int.fract (((j * (q₀ + 1) : ℕ) : ℝ) * θ n) < Q := by
      have := Int.fract_lt_one (((j * (q₀ + 1) : ℕ) : ℝ) * θ n)
      nlinarith
    exact Nat.floor_lt (by positivity) |>.mpr this
  have hcard : (Fintype.piFinset (fun _ : s => Finset.range Q)).card < (Finset.range J).card := by
    rw [Fintype.card_piFinset, Finset.card_range]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    omega
  obtain ⟨j, hj, j', hj', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- order the pair
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(j' - j) * (q₀ + 1), ?_, ?_, ?_⟩
    · have : 1 ≤ j' - j := by omega
      nlinarith
    · have : 1 ≤ j' - j := by omega
      positivity
    · intro n hn
      have hb := congrFun heq ⟨n, hn⟩
      simp only [hbox] at hb
      set a : ℝ := ((j * (q₀ + 1) : ℕ) : ℝ) * θ n with ha
      set b : ℝ := ((j' * (q₀ + 1) : ℕ) : ℝ) * θ n with hb'
      have hfr := abs_fract_sub_lt_of_floor_eq hQ hb
      refine ⟨⌊b⌋ - ⌊a⌋, ?_⟩
      have e3 : (((j' - j) * (q₀ + 1) : ℕ) : ℝ) * θ n = b - a := by
        rw [hb', ha, Nat.cast_mul, Nat.cast_sub hlt.le]
        push_cast
        ring
      rw [e3]
      push_cast
      have : b - a - ((⌊b⌋ : ℝ) - ⌊a⌋) = Int.fract b - Int.fract a := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        ring
      rw [this]
      exact hfr.le
  · refine ⟨(j - j') * (q₀ + 1), ?_, ?_, ?_⟩
    · have : 1 ≤ j - j' := by omega
      nlinarith
    · have : 1 ≤ j - j' := by omega
      positivity
    · intro n hn
      have hb := congrFun heq ⟨n, hn⟩
      simp only [hbox] at hb
      set a : ℝ := ((j' * (q₀ + 1) : ℕ) : ℝ) * θ n with ha
      set b : ℝ := ((j * (q₀ + 1) : ℕ) : ℝ) * θ n with hb'
      have hfr := abs_fract_sub_lt_of_floor_eq hQ hb.symm
      refine ⟨⌊b⌋ - ⌊a⌋, ?_⟩
      have e3 : (((j - j') * (q₀ + 1) : ℕ) : ℝ) * θ n = b - a := by
        rw [hb', ha, Nat.cast_mul, Nat.cast_sub hlt.le]
        push_cast
        ring
      rw [e3]
      push_cast
      have : b - a - ((⌊b⌋ : ℝ) - ⌊a⌋) = Int.fract b - Int.fract a := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]
        ring
      rw [this]
      exact hfr.le

/-- The translate of a main term. -/
theorem Fterm_add_I_mul (t : ℝ) (s : ℂ) (τ : ℝ) (n : ℤ) :
    Fterm t (s + Complex.I * τ) n =
      Fterm t s n * Complex.exp (-(Complex.I * τ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) := by
  unfold Fterm
  split_ifs with hn
  · simp
  · rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring

/-- `‖e^{−iτ L} − 1‖ ≤ |τ L − 2π m|` for every integer `m`. -/
theorem norm_exp_neg_I_sub_one_le (τ L : ℝ) (m : ℤ) :
    ‖Complex.exp (-(Complex.I * τ) * (L : ℂ)) - 1‖ ≤ |τ * L - 2 * π * m| := by
  have h1 : Complex.exp (-(Complex.I * τ) * (L : ℂ)) =
      Complex.exp (Complex.I * ((-(τ * L) + 2 * π * m : ℝ) : ℂ)) := by
    rw [show Complex.I * ((-(τ * L) + 2 * π * m : ℝ) : ℂ) =
      -(Complex.I * τ) * (L : ℂ) + (m : ℂ) * (2 * π * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1]
  have := norm_exp_I_mul_ofReal_sub_one_le (x := -(τ * L) + 2 * π * m)
  rw [Real.norm_eq_abs] at this
  calc ‖Complex.exp (Complex.I * ((-(τ * L) + 2 * π * m : ℝ) : ℂ)) - 1‖
      ≤ |-(τ * L) + 2 * π * m| := this
    _ = |τ * L - 2 * π * m| := by rw [← abs_neg]; congr 1; ring

/-- **Bohr's almost periods.** For every `ε > 0` and `T₀`, some `τ ≥ T₀` has
`‖F_t(s + iτ) − F_t(s)‖ ≤ ε` for every `s` in the strip `|Re s| ≤ X`. -/
theorem exists_almost_period {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {ε : ℝ} (hε : 0 < ε)
    (T₀ : ℝ) :
    ∃ τ : ℝ, T₀ ≤ τ ∧ ∀ s : ℂ, |s.re| ≤ X → ‖Ft t (s + Complex.I * τ) - Ft t s‖ ≤ ε := by
  classical
  set K : ℝ := Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) with hK
  have hK0 : 0 < K := Real.exp_pos _
  -- the tail
  have hsum : Summable (fun n : ℤ => K * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) := summable_Z32.mul_left K
  have htail := tendsto_tsum_compl_atTop_zero (fun n : ℤ => K * |(n : ℝ)| ^ (-(3 / 2 : ℝ)))
  have hev : ∀ᶠ s₀ : Finset ℤ in atTop,
      ∑' n : {n : ℤ // n ∉ s₀}, K * |((n : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ)) < ε / 4 :=
    (tendsto_order.1 htail).2 _ (by positivity)
  obtain ⟨s₀, hs₀⟩ := hev.exists
  -- the modulus of approximation
  obtain ⟨Q, hQ⟩ := exists_nat_gt (4 * π * K * Z32 / ε)
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < 4 * π * K * Z32 / ε := by
      have := Z32_pos
      positivity
    exact_mod_cast this.trans hQ
  -- the almost period
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt T₀
  obtain ⟨q, hqq₀, hq0, hq⟩ := exists_simultaneous_approx s₀
    (fun n => Real.log |(n : ℝ)| / (2 * π)) hQ0 q₀
  set τ : ℝ := (q : ℝ) with hτ
  refine ⟨τ, ?_, ?_⟩
  · have : (q₀ : ℝ) ≤ q := by exact_mod_cast hqq₀
    rw [hτ]
    linarith
  intro s hX
  -- the termwise bound
  have hpt : ∀ n : ℤ, ‖Fterm t (s + Complex.I * τ) n - Fterm t s n‖ ≤
      (if n ∈ s₀ then 2 * π / Q else 2) * ‖Fterm t s n‖ := by
    intro n
    rw [Fterm_add_I_mul, ← mul_sub_one, norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    split_ifs with hn
    · obtain ⟨m, hm⟩ := hq n hn
      refine (norm_exp_neg_I_sub_one_le _ _ m).trans ?_
      have : τ * Real.log |(n : ℝ)| - 2 * π * m =
          2 * π * (q * (Real.log |(n : ℝ)| / (2 * π)) - m) := by
        rw [hτ]
        field_simp
        first | done | ring
      rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      calc 2 * π * |q * (Real.log |(n : ℝ)| / (2 * π)) - m| ≤ 2 * π * (1 / Q) := by gcongr
        _ = 2 * π / Q := by ring
    · calc ‖Complex.exp (-(Complex.I * τ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) - 1‖
          ≤ ‖Complex.exp (-(Complex.I * τ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ))‖ +
            ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · rw [Complex.norm_exp, Real.exp_le_one_iff]
              simp [Complex.mul_re, Complex.mul_im]
            · simp
        _ = 2 := by norm_num
  -- summability
  have hsF := summable_norm_Fterm ht s
  have hsF' := summable_Fterm ht s
  have hsF2 := summable_Fterm ht (s + Complex.I * τ)
  have hg : Summable (fun n : ℤ => (if n ∈ s₀ then 2 * π / Q else 2) * ‖Fterm t s n‖) := by
    refine (hsF.mul_left (2 * π / Q + 2)).of_nonneg_of_le (fun n => by positivity)
      (fun n => ?_)
    have hQpos : (0 : ℝ) ≤ 2 * π / Q := by positivity
    split_ifs
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith
  -- the sum
  have hdiff : Ft t (s + Complex.I * τ) - Ft t s =
      ∑' n : ℤ, (Fterm t (s + Complex.I * τ) n - Fterm t s n) := by
    unfold Ft
    rw [hsF2.tsum_sub hsF']
  rw [hdiff]
  have hsd : Summable (fun n : ℤ => ‖Fterm t (s + Complex.I * τ) n - Fterm t s n‖) :=
    hg.of_nonneg_of_le (fun n => norm_nonneg _) hpt
  refine (norm_tsum_le_tsum_norm hsd).trans ?_
  refine (hasSum_le hpt hsd.hasSum hg.hasSum).trans ?_
  -- split the majorant over `s₀` and its complement
  rw [← hg.sum_add_tsum_compl (s := s₀)]
  have hA : ∑ n ∈ s₀, (if n ∈ s₀ then 2 * π / Q else 2) * ‖Fterm t s n‖ ≤ ε / 2 := by
    have h1 : ∑ n ∈ s₀, (if n ∈ s₀ then 2 * π / Q else 2) * ‖Fterm t s n‖ =
        2 * π / Q * ∑ n ∈ s₀, ‖Fterm t s n‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos hn]
    rw [h1]
    have h2 : ∑ n ∈ s₀, ‖Fterm t s n‖ ≤ K * Z32 := by
      calc ∑ n ∈ s₀, ‖Fterm t s n‖ ≤ ∑' n, ‖Fterm t s n‖ :=
            hsF.sum_le_tsum s₀ (fun n _ => norm_nonneg _)
        _ ≤ K * Z32 := tsum_norm_Fterm_le ht hX
    have h3 : 2 * π / Q * (K * Z32) ≤ ε / 2 := by
      have hQ' : 4 * π * K * Z32 < Q * ε := by
        have := hQ
        rwa [div_lt_iff₀ hε] at this
      have e1 : 2 * π / Q * (K * Z32) = (4 * π * K * Z32) / (2 * Q) := by
        field_simp
        first | done | ring
      rw [e1, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)]
      nlinarith
    calc 2 * π / Q * ∑ n ∈ s₀, ‖Fterm t s n‖ ≤ 2 * π / Q * (K * Z32) := by gcongr
      _ ≤ ε / 2 := h3
  have hB : ∑' n : {n : ℤ // n ∉ s₀}, (if (n : ℤ) ∈ s₀ then 2 * π / Q else 2) *
      ‖Fterm t s n‖ ≤ ε / 2 := by
    have h1 : ∀ n : {n : ℤ // n ∉ s₀},
        (if (n : ℤ) ∈ s₀ then 2 * π / Q else 2) * ‖Fterm t s n‖ ≤
          2 * (K * |((n : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ))) := by
      intro n
      rw [if_neg n.2]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact norm_Fterm_le ht hX n
    have h2 := hasSum_le h1 (hg.subtype _).hasSum ((hsum.mul_left 2).subtype _).hasSum
    simp only [Function.comp_apply] at h2
    rw [tsum_mul_left] at h2
    linarith
  refine le_trans (add_le_add hA hB) ?_
  linarith

end Soma.Holonics.RH.BohrZeros
