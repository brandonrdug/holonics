import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Iterated derivatives of entire functions of order below two, and the heat series

For an entire `f` with `‖f w‖ ≤ A exp (B ‖w‖^ρ)`, Cauchy's estimate on the circle of radius `R`
about `z` gives `‖f^{(n)}(z)‖ ≤ n! A exp (B (‖z‖+R)^ρ) / R^n`.  Choosing `R = k^{1/ρ}` for the
`2k`-th derivative and using `(2k)! ≤ (2k)^{2k}`, `k^k / k! ≤ e^k`, the `k`-th term
`(−t)^k/k! · f^{(2k)}(z)` of the derivative-series heat flow is bounded by
`M (C k^{−(2/ρ − 1)})^k`, which is eventually below `M/2^k` when `ρ < 2`.  So the heat series
`Σ_k (−t)^k/k! f^{(2k)}(z)` converges absolutely for every real `t` and every `z`: this is the
passage from the polynomial face of the de Bruijn–Newman flow to entire functions of order below
two, of which `Ξ` is one.
-/

open Complex Metric Filter Topology Finset

namespace Soma.Holonics.RH.EntireDerivativeGrowth

/-- `f` has growth of order `ρ` with constants `A`, `B`. -/
def HasGrowth (f : ℂ → ℂ) (A B ρ : ℝ) : Prop := ∀ w : ℂ, ‖f w‖ ≤ A * Real.exp (B * ‖w‖ ^ ρ)

variable {f : ℂ → ℂ} {A B ρ : ℝ}

theorem norm_le_of_mem_sphere (hg : HasGrowth f A B ρ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    {z w : ℂ} {R : ℝ} (hw : w ∈ sphere z R) :
    ‖f w‖ ≤ A * Real.exp (B * (‖z‖ + R) ^ ρ) := by
  refine (hg w).trans ?_
  rw [mem_sphere_iff_norm] at hw
  have hwz : ‖w‖ ≤ ‖z‖ + R := by
    calc ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ = ‖z‖ + R := by rw [hw]
  have h1 : ‖w‖ ^ ρ ≤ (‖z‖ + R) ^ ρ := Real.rpow_le_rpow (norm_nonneg _) hwz hρ
  have h2 : B * ‖w‖ ^ ρ ≤ B * (‖z‖ + R) ^ ρ := mul_le_mul_of_nonneg_left h1 hB
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hA

/-- Cauchy's estimate under a growth bound. -/
theorem norm_iteratedDeriv_le (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (n : ℕ) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv n f z‖ ≤ n.factorial * (A * Real.exp (B * (‖z‖ + R) ^ ρ)) / R ^ n :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf.diffContOnCl
    (fun _ hw => norm_le_of_mem_sphere hg hA hB hρ hw)

theorem add_rpow_le {ρ a b : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ ρ ≤ 2 ^ ρ * (a ^ ρ + b ^ ρ) := by
  have h2 : (0 : ℝ) ≤ 2 ^ ρ := Real.rpow_nonneg (by norm_num) ρ
  have haρ := Real.rpow_nonneg ha ρ
  have hbρ := Real.rpow_nonneg hb ρ
  rcases le_total a b with h | h
  · calc (a + b) ^ ρ ≤ (2 * b) ^ ρ := Real.rpow_le_rpow (by positivity) (by linarith) hρ
      _ = 2 ^ ρ * b ^ ρ := Real.mul_rpow (by norm_num) hb
      _ ≤ 2 ^ ρ * (a ^ ρ + b ^ ρ) := by nlinarith
  · calc (a + b) ^ ρ ≤ (2 * a) ^ ρ := Real.rpow_le_rpow (by positivity) (by linarith) hρ
      _ = 2 ^ ρ * a ^ ρ := Real.mul_rpow (by norm_num) ha
      _ ≤ 2 ^ ρ * (a ^ ρ + b ^ ρ) := by nlinarith

/-- The `k`-th term of the derivative-series heat flow `e^{−tD²} f` at `z`. -/
noncomputable def heatTerm (t : ℝ) (f : ℂ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * iteratedDeriv (2 * k) f z

theorem norm_heatTerm (t : ℝ) (f : ℂ → ℂ) (z : ℂ) (k : ℕ) :
    ‖heatTerm t f z k‖ = |t| ^ k / (k.factorial : ℝ) * ‖iteratedDeriv (2 * k) f z‖ := by
  unfold heatTerm
  rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast]

/-- `1 / k! ≤ e^k / k^k`. -/
theorem inv_factorial_le {k : ℕ} (hk : 0 < k) :
    (1 : ℝ) / (k.factorial : ℝ) ≤ Real.exp 1 ^ k / (k : ℝ) ^ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) hk'.le k
  rw [Real.exp_one_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- The term bound `‖heatTerm t f z k‖ ≤ M (C k^{−(2/ρ−1)})^k` with `R = k^{1/ρ}`. -/
theorem norm_heatTerm_le (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (t : ℝ) (z : ℂ) {k : ℕ} (hk : 0 < k) :
    ‖heatTerm t f z k‖ ≤ (A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ)) *
      ((4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) * (k : ℝ) ^ (-(2 / ρ - 1))) ^ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set R : ℝ := (k : ℝ) ^ (1 / ρ) with hRdef
  have hR : 0 < R := Real.rpow_pos_of_pos hk' _
  have hRρ : R ^ ρ = k := by
    rw [hRdef, ← Real.rpow_mul hk'.le, one_div_mul_cancel hρ0.ne', Real.rpow_one]
  have hR2k : R ^ (2 * k) = (k : ℝ) ^ (2 * (k : ℝ) / ρ) := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hk'.le]
    congr 1
    push_cast
    ring
  have h2ρ : (0 : ℝ) ≤ 2 ^ ρ := Real.rpow_nonneg (by norm_num) ρ
  -- Cauchy with the exponent bound
  have hexp : Real.exp (B * (‖z‖ + R) ^ ρ) ≤
      Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ) * Real.exp (B * 2 ^ ρ) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := add_rpow_le hρ0.le (norm_nonneg z) hR.le
    rw [hRρ] at this
    nlinarith [mul_le_mul_of_nonneg_left this hB]
  have hC := norm_iteratedDeriv_le hf hg hA hB hρ0.le (2 * k) z hR
  -- factorial bounds
  have hfac : ((2 * k).factorial : ℝ) ≤ (4 : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
    have := Nat.factorial_le_pow (2 * k)
    calc ((2 * k).factorial : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ (2 * k) := by exact_mod_cast this
      _ = (4 : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by push_cast; rw [mul_pow, pow_mul]; norm_num
  have hinv := inv_factorial_le hk
  -- the rpow bookkeeping: k^{2k} / (k^k k^{2k/ρ}) = (k^{-(2/ρ-1)})^k
  have hpow : (k : ℝ) ^ (2 * k) / ((k : ℝ) ^ k * (k : ℝ) ^ (2 * (k : ℝ) / ρ)) =
      ((k : ℝ) ^ (-(2 / ρ - 1))) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast ((k : ℝ) ^ (-(2 / ρ - 1))) k,
      ← Real.rpow_natCast (k : ℝ) k, ← Real.rpow_mul hk'.le, ← Real.rpow_add hk',
      ← Real.rpow_sub hk']
    congr 1
    push_cast
    field_simp
    ring
  rw [norm_heatTerm]
  have hM : 0 ≤ A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ) := by positivity
  calc |t| ^ k / (k.factorial : ℝ) * ‖iteratedDeriv (2 * k) f z‖
      ≤ |t| ^ k / (k.factorial : ℝ) *
          ((2 * k).factorial * (A * Real.exp (B * (‖z‖ + R) ^ ρ)) / R ^ (2 * k)) := by
        gcongr
    _ ≤ |t| ^ k * (Real.exp 1 ^ k / (k : ℝ) ^ k) *
          (((4 : ℝ) ^ k * (k : ℝ) ^ (2 * k)) *
            (A * (Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ) * Real.exp (B * 2 ^ ρ) ^ k)) /
              (k : ℝ) ^ (2 * (k : ℝ) / ρ)) := by
        rw [hR2k, div_eq_mul_one_div (|t| ^ k)]
        gcongr
    _ = (A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ)) *
          ((4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) ^ k *
            ((k : ℝ) ^ (2 * k) / ((k : ℝ) ^ k * (k : ℝ) ^ (2 * (k : ℝ) / ρ)))) := by
        have h1 : (k : ℝ) ^ k ≠ 0 := by positivity
        have h2 : (k : ℝ) ^ (2 * (k : ℝ) / ρ) ≠ 0 := (Real.rpow_pos_of_pos hk' _).ne'
        field_simp
        ring
    _ = _ := by rw [hpow, ← mul_pow]

/-- Absolute convergence of the heat series for entire functions of order below two. -/
theorem summable_heatTerm (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (t : ℝ) (z : ℂ) :
    Summable (fun k => ‖heatTerm t f z k‖) := by
  set C : ℝ := 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ) with hC
  set M : ℝ := A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ) with hM
  have hC0 : 0 ≤ C := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hlim : Tendsto (fun k : ℕ => C * (k : ℝ) ^ (-(2 / ρ - 1))) atTop (𝓝 (C * 0)) :=
    ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at hlim
  have hev : ∀ᶠ k : ℕ in atTop, ‖heatTerm t f z k‖ ≤ M * (1 / 2 : ℝ) ^ k := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_gt_atTop 0] with k hk hk0
    calc ‖heatTerm t f z k‖ ≤ M * (C * (k : ℝ) ^ (-(2 / ρ - 1))) ^ k :=
          norm_heatTerm_le hf hg hA hB hρ0 t z hk0
      _ ≤ M * (1 / 2 : ℝ) ^ k := by
          have h0 : 0 ≤ C * (k : ℝ) ^ (-(2 / ρ - 1)) :=
            mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg k) _)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hk.le k) hM0
  have hgeom : Summable (fun k : ℕ => M * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M
  exact (Summable.of_norm_bounded_eventually_nat hgeom
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hev))

end Soma.Holonics.RH.EntireDerivativeGrowth
