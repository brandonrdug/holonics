import Mathlib
import Holonics.Aeon.Production.Zeta

/-!
# The growth rate of a nonnegative return map is the logarithm of its Perron value

[definition] Source: aeon record A8 and `Aeon/Production/Zeta`, whose closing paragraph held as
owed (issue #410) the equality `h = log ρ(M) = lim (1/k) log N_k` for a nonnegative return map
`M`, the radius of convergence of its word series and the place of the first pole of
`ζ(T) = 1/det(1 − T·M)`. Here `N_k = 1ᵀ Mᵏ 1` is `Zeta.wordCount M k`, the count of the words of
`k` epochs.

[proved-derived; formal-checked] What is proved. Throughout `M` is a real square matrix with
nonnegative entries; items 1 to 5 also take a strictly positive vector `v` with `M v = λ v` (a
Perron vector, as a hypothesis).

1. **The two-sided growth law.** With `a ≤ v_i ≤ b`: every row sum of `Mᵏ` lies between
   `(a/b)·λᵏ` and `(b/a)·λᵏ` (`row_sum_lower`, `row_sum_upper`, written without division), so
   `d·a·λᵏ ≤ b·N_k` and `a·N_k ≤ d·b·λᵏ` with `d` the number of states (`wordCount_lower`,
   `wordCount_upper`). `λ ≥ 0` follows (`eigenvalue_nonneg`).
2. **The rate.** For `λ > 0`: `(1/k)·log N_k → log λ` (`tendsto_log_wordCount`) and
   `N_k^(1/k) → λ` (`tendsto_wordCount_rpow`). The limit exists; no upper limit is needed.
3. **The radius of the word series.** For `z ≥ 0`, `Σ_k N_k zᵏ` is summable if and only if
   `z·λ < 1` (`summable_wordCount_iff`); it is summable for every real `z` with `|z|·λ < 1`
   (`summable_wordCount_of_abs_lt`) and is not summable at `z = 1/λ`
   (`not_summable_wordCount_at_inv`).
4. **The first pole of the zeta.** `det(1 − λ⁻¹·M) = 0` (`transferDet_zero_at_inv`), and
   `det(1 − z·M) ≠ 0` for every complex `z` with `|z|·λ < 1` (`transferDet_ne_zero_of_lt`): the
   transfer determinant has no zero inside the disc of radius `1/λ` and has one at `1/λ`.
   The step behind it: every complex eigenvalue `μ` of `M` has `|μ| ≤ λ`
   (`eigenvalue_norm_le`).
5. **The Perron value is the spectral radius** (`spectralRadius_eq_perron`): for `λ > 0`,
   Mathlib's `spectralRadius ℂ M` is `λ`.
6. **Gelfand's form, with no eigenvector.** For every nonnegative `M` on a nonempty set of
   states, `N_k^(1/k)` tends to the spectral radius of `M` read over `ℂ`
   (`tendsto_wordCount_rpow_spectralRadius`), and `(1/k)·log N_k` tends to its logarithm when it
   is positive (`tendsto_log_wordCount_spectralRadius`). The entry sum is within the factor `d`
   of the row-sum norm (`linfty_norm_le_wordCount`, `wordCount_le_card_mul_linfty_norm`).
7. **Ruler, the golden-mean shift.** `!![1, 1; 1, 0]ᵏ` has the Fibonacci entries
   (`goldenShift_pow`), `N_k = F_(k+3)` (`wordCount_goldenShift`), its Perron vector is `(φ, 1)`
   at `λ = φ` (`goldenShift_eigen`), so `(1/k)·log F_(k+3) → log φ` (`fib_growth`) and its
   spectral radius is `φ` (`goldenShift_spectralRadius`).

Limits. The existence of a strictly positive eigenvector (Perron–Frobenius, for an irreducible
nonnegative matrix) is a hypothesis of items 1 to 5 and is not proved; item 6 needs none. The
cycle counts `tr Mᵏ` have the upper bound `d·λᵏ` (`Zeta.cycle_count_le_perron`) and no lower
bound at every `k` (a cyclic shift has `tr Mᵏ = 0` off its period), so their rate is an upper
limit and is not stated here. That the zero at `1/λ` is a simple pole of the continued word series
is not stated; items 3 and 4 give its place.

Computational object: the helical pair interaction, read through its return map over one epoch.
Of the winding guide's six objects it touches the tube (the return map composes along the clocked
span, and `N_k` counts its words of `k` epochs) and cell holonomy (the cycle counts `tr Mᵏ` and
the transfer determinant); helix, pair, faces and placement and the tower thread stay attached.

Consumers: `Aeon/Production/Zeta` (growth of cycle and word counts, the zeta's first pole),
`Foundation/FractalString` (the scale chart `T = r^s`, where `1/λ` is the abscissa).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.GrowthRate

open Matrix Finset Filter Topology
open Holonics.Aeon.Production.Zeta (wordCount)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. The two-sided growth law under a Perron vector -/

section Perron

variable {M : Matrix n n ℝ} {v : n → ℝ} {lam : ℝ}

/-- [proved-derived; formal-checked] The powers of a matrix of nonnegative entries have
nonnegative entries. -/
theorem pow_nonneg_entries (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) (i j : n) : 0 ≤ (M ^ k) i j := by
  induction k generalizing i j with
  | zero => rw [pow_zero, one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (ih i l) (hM l j)

/-- [proved-derived; formal-checked] The word count of a nonnegative return map is nonnegative. -/
theorem wordCount_nonneg (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) : 0 ≤ wordCount M k :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => pow_nonneg_entries hM k i j

/-- [proved-derived; formal-checked] An eigenvector of `M` is an eigenvector of every power. -/
theorem pow_mulVec_eigen (heig : M *ᵥ v = lam • v) (k : ℕ) : (M ^ k) *ᵥ v = lam ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, heig, smul_smul, pow_succ]

/-- [proved-derived; formal-checked] Row `i` of `Mᵏ` weighted by the eigenvector reads
`λᵏ·v_i`. -/
theorem row_weighted_sum (heig : M *ᵥ v = lam • v) (k : ℕ) (i : n) :
    ∑ j, (M ^ k) i j * v j = lam ^ k * v i := by
  have h := congrFun (pow_mulVec_eigen heig k) i
  simpa [mulVec, dotProduct] using h

/-- [proved-derived; formal-checked] A nonnegative matrix with a strictly positive eigenvector on
at least one state has a nonnegative eigenvalue. -/
theorem eigenvalue_nonneg (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (i : n) : 0 ≤ lam := by
  have h := row_weighted_sum heig 1 i
  rw [pow_one, pow_one] at h
  have h0 : 0 ≤ ∑ j, M i j * v j := sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j).le
  rw [h] at h0
  exact (mul_nonneg_iff_of_pos_right (hv i)).mp h0

/-- [proved-derived; formal-checked] **A row sum of `Mᵏ` is at most `(b/a)·λᵏ`**, with
`a ≤ v ≤ b`, written without division. -/
theorem row_sum_upper (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (heig : M *ᵥ v = lam • v)
    {a b : ℝ} (ha : ∀ i, a ≤ v i) (hb : ∀ i, v i ≤ b) (k : ℕ) (i : n) :
    a * ∑ j, (M ^ k) i j ≤ b * lam ^ k := by
  have hlam : 0 ≤ lam ^ k := pow_nonneg (eigenvalue_nonneg hM hv heig i) k
  calc a * ∑ j, (M ^ k) i j = ∑ j, (M ^ k) i j * a := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ ∑ j, (M ^ k) i j * v j :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ha j) (pow_nonneg_entries hM k i j)
    _ = lam ^ k * v i := row_weighted_sum heig k i
    _ ≤ lam ^ k * b := mul_le_mul_of_nonneg_left (hb i) hlam
    _ = b * lam ^ k := mul_comm _ _

/-- [proved-derived; formal-checked] **A row sum of `Mᵏ` is at least `(a/b)·λᵏ`**, with
`a ≤ v ≤ b`, written without division. -/
theorem row_sum_lower (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (heig : M *ᵥ v = lam • v)
    {a b : ℝ} (ha : ∀ i, a ≤ v i) (hb : ∀ i, v i ≤ b) (k : ℕ) (i : n) :
    a * lam ^ k ≤ b * ∑ j, (M ^ k) i j := by
  have hlam : 0 ≤ lam ^ k := pow_nonneg (eigenvalue_nonneg hM hv heig i) k
  calc a * lam ^ k ≤ v i * lam ^ k := mul_le_mul_of_nonneg_right (ha i) hlam
    _ = ∑ j, (M ^ k) i j * v j := by rw [row_weighted_sum heig k i, mul_comm]
    _ ≤ ∑ j, (M ^ k) i j * b :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (pow_nonneg_entries hM k i j)
    _ = b * ∑ j, (M ^ k) i j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => mul_comm _ _

/-- [proved-derived; formal-checked] **The word count is at most `d·(b/a)·λᵏ`.** -/
theorem wordCount_upper (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (heig : M *ᵥ v = lam • v)
    {a b : ℝ} (ha : ∀ i, a ≤ v i) (hb : ∀ i, v i ≤ b) (k : ℕ) :
    a * wordCount M k ≤ Fintype.card n * (b * lam ^ k) := by
  calc a * wordCount M k = ∑ i, a * ∑ j, (M ^ k) i j := by rw [wordCount, mul_sum]
    _ ≤ ∑ _i : n, b * lam ^ k := sum_le_sum fun i _ => row_sum_upper hM hv heig ha hb k i
    _ = Fintype.card n * (b * lam ^ k) := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- [proved-derived; formal-checked] **The word count is at least `d·(a/b)·λᵏ`.** -/
theorem wordCount_lower (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (heig : M *ᵥ v = lam • v)
    {a b : ℝ} (ha : ∀ i, a ≤ v i) (hb : ∀ i, v i ≤ b) (k : ℕ) :
    Fintype.card n * (a * lam ^ k) ≤ b * wordCount M k := by
  calc (Fintype.card n : ℝ) * (a * lam ^ k) = ∑ _i : n, a * lam ^ k := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ ∑ i, b * ∑ j, (M ^ k) i j := sum_le_sum fun i _ => row_sum_lower hM hv heig ha hb k i
    _ = b * wordCount M k := by rw [wordCount, mul_sum]

/-- [proved-derived; formal-checked] **The two-sided growth law in ratio form.** On a nonempty
set of states there are constants `0 < c` and `C` with `c·λᵏ ≤ N_k ≤ C·λᵏ` at every `k`. -/
theorem wordCount_two_sided [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) :
    ∃ c C : ℝ, 0 < c ∧ (∀ k, c * lam ^ k ≤ wordCount M k) ∧ ∀ k, wordCount M k ≤ C * lam ^ k := by
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image univ v univ_nonempty
  obtain ⟨i₁, -, hmax⟩ := Finset.exists_max_image univ v univ_nonempty
  have ha : ∀ i, v i₀ ≤ v i := fun i => hmin i (mem_univ i)
  have hb : ∀ i, v i ≤ v i₁ := fun i => hmax i (mem_univ i)
  have ha0 : 0 < v i₀ := hv i₀
  have hb0 : 0 < v i₁ := hv i₁
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card n * v i₀ / v i₁, Fintype.card n * v i₁ / v i₀,
    div_pos (mul_pos hd ha0) hb0, fun k => ?_, fun k => ?_⟩
  · have h := wordCount_lower hM hv heig ha hb k
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    linarith
  · have h := wordCount_upper hM hv heig ha hb k
    rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
    linarith

end Perron

/-! ## 2. The rate, for any sequence with a two-sided geometric bound -/

section Rate

variable {N : ℕ → ℝ} {lam c C : ℝ}

/-- [proved-derived; formal-checked] **A sequence between two multiples of `λᵏ` has rate
`log λ`**: `(1/k)·log N_k → log λ`. -/
theorem tendsto_log_div_of_two_sided (hlam : 0 < lam) (hc : 0 < c)
    (hlow : ∀ k, c * lam ^ k ≤ N k) (hup : ∀ k, N k ≤ C * lam ^ k) :
    Tendsto (fun k : ℕ => Real.log (N k) / k) atTop (𝓝 (Real.log lam)) := by
  have hC : 0 < C := by
    have h0 := (hlow 0).trans (hup 0)
    simp only [pow_zero, mul_one] at h0
    linarith
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le (mul_pos hc (pow_pos hlam k)) (hlow k)
  have hlo : Tendsto (fun k : ℕ => Real.log c / k + Real.log lam) atTop (𝓝 (Real.log lam)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add_const (Real.log lam)
  have hhi : Tendsto (fun k : ℕ => Real.log C / k + Real.log lam) atTop (𝓝 (Real.log lam)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add_const (Real.log lam)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : Real.log (c * lam ^ k) ≤ Real.log (N k) :=
      Real.log_le_log (mul_pos hc (pow_pos hlam k)) (hlow k)
    rw [Real.log_mul hc.ne' (pow_pos hlam k).ne', Real.log_pow] at h1
    rw [le_div_iff₀ hk0]
    have h2 : (Real.log c / k + Real.log lam) * k = Real.log c + k * Real.log lam := by
      field_simp
    linarith
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : Real.log (N k) ≤ Real.log (C * lam ^ k) := Real.log_le_log (hNpos k) (hup k)
    rw [Real.log_mul hC.ne' (pow_pos hlam k).ne', Real.log_pow] at h1
    rw [div_le_iff₀ hk0]
    have h2 : (Real.log C / k + Real.log lam) * k = Real.log C + k * Real.log lam := by
      field_simp
    linarith

/-- [proved-derived; formal-checked] The root form of a rate: if `(1/k)·log N_k → log λ` for a
positive sequence then `N_k^(1/k) → λ`. -/
theorem tendsto_rpow_of_tendsto_log (hlam : 0 < lam) (hN : ∀ k, 0 < N k)
    (h : Tendsto (fun k : ℕ => Real.log (N k) / k) atTop (𝓝 (Real.log lam))) :
    Tendsto (fun k : ℕ => N k ^ (1 / (k : ℝ))) atTop (𝓝 lam) := by
  have h2 := (Real.continuous_exp.tendsto (Real.log lam)).comp h
  rw [Real.exp_log hlam] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (hN k)]
  congr 1
  ring

/-- [proved-derived; formal-checked] **The radius of a series with a two-sided geometric bound.**
For `z ≥ 0`, `Σ N_k zᵏ` is summable if and only if `z·λ < 1`. -/
theorem summable_iff_of_two_sided (hlam : 0 < lam) (hc : 0 < c)
    (hlow : ∀ k, c * lam ^ k ≤ N k) (hup : ∀ k, N k ≤ C * lam ^ k) {z : ℝ} (hz : 0 ≤ z) :
    Summable (fun k => N k * z ^ k) ↔ z * lam < 1 := by
  constructor
  · intro hs
    by_contra hge
    have hge' : 1 ≤ z * lam := not_lt.mp hge
    have hev := (tendsto_order.1 hs.tendsto_atTop_zero).2 c hc
    obtain ⟨k, hk⟩ := hev.exists
    have hck : c ≤ N k * z ^ k := by
      calc c ≤ c * (z * lam) ^ k := le_mul_of_one_le_right hc.le (one_le_pow₀ hge')
        _ = c * lam ^ k * z ^ k := by rw [mul_pow]; ring
        _ ≤ N k * z ^ k := mul_le_mul_of_nonneg_right (hlow k) (pow_nonneg hz k)
    linarith
  · intro hlt
    have hgeo : Summable (fun k : ℕ => C * (z * lam) ^ k) :=
      (summable_geometric_of_lt_one (mul_nonneg hz hlam.le) hlt).mul_left C
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hgeo
    · exact mul_nonneg (le_trans (mul_nonneg hc.le (pow_nonneg hlam.le k)) (hlow k))
        (pow_nonneg hz k)
    · calc N k * z ^ k ≤ C * lam ^ k * z ^ k :=
            mul_le_mul_of_nonneg_right (hup k) (pow_nonneg hz k)
        _ = C * (z * lam) ^ k := by rw [mul_pow]; ring

end Rate

/-! ## 3. The rate, the radius and the first pole of a return map with a Perron vector -/

section PerronRate

variable {M : Matrix n n ℝ} {v : n → ℝ} {lam : ℝ}

/-- [proved-derived; formal-checked] **`h = log λ`: the word count's rate is the logarithm of the
Perron value**, `(1/k)·log N_k → log λ`. -/
theorem tendsto_log_wordCount [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) :
    Tendsto (fun k : ℕ => Real.log (wordCount M k) / k) atTop (𝓝 (Real.log lam)) := by
  obtain ⟨c, C, hc, hlow, hup⟩ := wordCount_two_sided hM hv heig
  exact tendsto_log_div_of_two_sided hlam hc hlow hup

/-- [proved-derived; formal-checked] The word count of a return map with a Perron vector at a
positive value is positive. -/
theorem wordCount_pos [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) (k : ℕ) : 0 < wordCount M k := by
  obtain ⟨c, C, hc, hlow, -⟩ := wordCount_two_sided hM hv heig
  exact lt_of_lt_of_le (mul_pos hc (pow_pos hlam k)) (hlow k)

/-- [proved-derived; formal-checked] **The root form**, `N_k^(1/k) → λ`. -/
theorem tendsto_wordCount_rpow [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) :
    Tendsto (fun k : ℕ => wordCount M k ^ (1 / (k : ℝ))) atTop (𝓝 lam) :=
  tendsto_rpow_of_tendsto_log hlam (wordCount_pos hM hv heig hlam)
    (tendsto_log_wordCount hM hv heig hlam)

/-- [proved-derived; formal-checked] **The word series has radius `1/λ`.** For `z ≥ 0`,
`Σ_k N_k zᵏ` is summable if and only if `z·λ < 1`. -/
theorem summable_wordCount_iff [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) {z : ℝ} (hz : 0 ≤ z) :
    Summable (fun k => wordCount M k * z ^ k) ↔ z * lam < 1 := by
  obtain ⟨c, C, hc, hlow, hup⟩ := wordCount_two_sided hM hv heig
  exact summable_iff_of_two_sided hlam hc hlow hup hz

/-- [proved-derived; formal-checked] The word series is summable at every real `z` inside the
radius, `|z|·λ < 1`. -/
theorem summable_wordCount_of_abs_lt [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) {z : ℝ} (hz : |z| * lam < 1) :
    Summable (fun k => wordCount M k * z ^ k) := by
  have h := (summable_wordCount_iff hM hv heig hlam (abs_nonneg z)).mpr hz
  refine Summable.of_norm ?_
  refine h.congr fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (wordCount_nonneg hM k)]

/-- [proved-derived; formal-checked] **The word series is not summable at `z = 1/λ`**: the
radius is reached there. -/
theorem not_summable_wordCount_at_inv [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) :
    ¬ Summable (fun k => wordCount M k * lam⁻¹ ^ k) := by
  rw [summable_wordCount_iff hM hv heig hlam (inv_nonneg.mpr hlam.le),
    inv_mul_cancel₀ hlam.ne']
  exact lt_irrefl 1

/-- [proved-derived; formal-checked] **The transfer determinant vanishes at `T = 1/λ`**:
`det(1 − λ⁻¹·M) = 0` for any eigenvector `v ≠ 0` at `λ ≠ 0`. This is where
`ζ(T) = 1/det(1 − T·M)` has its pole. -/
theorem transferDet_zero_at_inv (hv0 : v ≠ 0) (heig : M *ᵥ v = lam • v) (hlam : lam ≠ 0) :
    (1 - lam⁻¹ • M).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, heig, smul_smul,
    inv_mul_cancel₀ hlam, one_smul, sub_self]

/-- [proved-derived; formal-checked] **Every complex eigenvalue of a nonnegative matrix with a
Perron vector has modulus at most the Perron value.** The proof weighs the eigenvector by `v` and
reads the row where `|w_i|/v_i` is largest. -/
theorem eigenvalue_norm_le (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) {w : n → ℂ} (hw : w ≠ 0) {μ : ℂ}
    (h : (M.map (algebraMap ℝ ℂ)) *ᵥ w = μ • w) : ‖μ‖ ≤ lam := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image univ (fun i => ‖w i‖ / v i) ⟨j, mem_univ j⟩
  have hjpos : 0 < ‖w j‖ / v j := div_pos (norm_pos_iff.mpr (by simpa using hj)) (hv j)
  have htpos : 0 < ‖w i‖ / v i := lt_of_lt_of_le hjpos (hi j (mem_univ j))
  have hwi : 0 < ‖w i‖ := by
    rcases (div_pos_iff.mp htpos) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd (hv i) (not_lt.mpr h2.le)
  have hle : ∀ l, ‖w l‖ ≤ ‖w i‖ / v i * v l := fun l =>
    (div_le_iff₀ (hv l)).mp (hi l (mem_univ l))
  have hrow : ∑ l, ((M i l : ℝ) : ℂ) * w l = μ * w i := by
    have h' := congrFun h i
    simpa [mulVec, dotProduct] using h'
  have hbound : ‖μ‖ * ‖w i‖ ≤ lam * ‖w i‖ := by
    calc ‖μ‖ * ‖w i‖ = ‖∑ l, ((M i l : ℝ) : ℂ) * w l‖ := by rw [hrow, norm_mul]
      _ ≤ ∑ l, ‖((M i l : ℝ) : ℂ) * w l‖ := norm_sum_le _ _
      _ = ∑ l, M i l * ‖w l‖ := by
          refine sum_congr rfl fun l _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM i l)]
      _ ≤ ∑ l, M i l * (‖w i‖ / v i * v l) :=
          sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (hM i l)
      _ = ‖w i‖ / v i * ∑ l, M i l * v l := by
          rw [mul_sum]; exact sum_congr rfl fun l _ => by ring
      _ = ‖w i‖ / v i * (lam * v i) := by
          have h1 := row_weighted_sum heig 1 i
          rw [pow_one, pow_one] at h1
          rw [h1]
      _ = lam * ‖w i‖ := by
          have hvi : v i ≠ 0 := (hv i).ne'
          field_simp
  exact le_of_mul_le_mul_right hbound hwi

/-- [proved-derived; formal-checked] **The transfer determinant has no zero inside the disc of
radius `1/λ`**: `det(1 − z·M) ≠ 0` for every complex `z` with `|z|·λ < 1`. With
`transferDet_zero_at_inv`, the first pole of the zeta is at `T = 1/λ`. -/
theorem transferDet_ne_zero_of_lt (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i)
    (heig : M *ᵥ v = lam • v) {z : ℂ} (hz : ‖z‖ * lam < 1) :
    (1 - z • M.map (algebraMap ℝ ℂ)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hw0
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hw
    simpa using hw0
  have h : (M.map (algebraMap ℝ ℂ)) *ᵥ w = z⁻¹ • w := by
    conv_rhs => rw [hw0]
    rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
  have hle := eigenvalue_norm_le hM hv heig hw h
  rw [norm_inv] at hle
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h1 : 1 ≤ ‖z‖ * lam := by
    have h2 := mul_le_mul_of_nonneg_left hle hzpos.le
    rwa [mul_inv_cancel₀ hzpos.ne'] at h2
  linarith

end PerronRate

/-! ## 4. Gelfand's form: the rate is the spectral radius, with no eigenvector -/

section Gelfand

open scoped Matrix.Norms.Operator NNReal ENNReal

variable {M : Matrix n n ℝ}

/-- [proved-derived; formal-checked] The row-sum norm of the `k`-th power of a nonnegative
matrix, read over `ℂ`, is at most its word count. -/
theorem linfty_norm_le_wordCount (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) :
    ‖(M.map (algebraMap ℝ ℂ)) ^ k‖ ≤ wordCount M k := by
  rw [← Matrix.map_pow, Matrix.linfty_opNorm_def]
  have hT : wordCount M k = ((∑ i, ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊ : ℝ≥0) : ℝ) := by
    rw [wordCount]
    push_cast
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg_entries hM k i j)]
  rw [hT, NNReal.coe_le_coe]
  exact Finset.sup_le fun i _ =>
    Finset.single_le_sum (f := fun i => ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊)
      (fun _ _ => by positivity) (mem_univ i)

/-- [proved-derived; formal-checked] The word count of a nonnegative matrix is at most the
number of states times the row-sum norm of its `k`-th power. -/
theorem wordCount_le_card_mul_linfty_norm (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) :
    wordCount M k ≤ Fintype.card n * ‖(M.map (algebraMap ℝ ℂ)) ^ k‖ := by
  rw [← Matrix.map_pow, Matrix.linfty_opNorm_def]
  have hT : wordCount M k = ((∑ i, ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊ : ℝ≥0) : ℝ) := by
    rw [wordCount]
    push_cast
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg_entries hM k i j)]
  rw [hT]
  have h := Finset.sum_le_card_nsmul (univ : Finset n)
    (fun i => ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊)
    (univ.sup fun i => ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊)
    (fun i hi => Finset.le_sup (f := fun i => ∑ j, ‖((M ^ k).map (algebraMap ℝ ℂ)) i j‖₊) hi)
  rw [card_univ, nsmul_eq_mul] at h
  exact_mod_cast h

/-- [proved-derived; formal-checked] Gelfand's formula for a complex matrix in real form:
`‖Aᵏ‖^(1/k)` tends to the spectral radius, for the row-sum norm. -/
theorem tendsto_norm_pow_rpow (A : Matrix n n ℂ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (spectralRadius ℂ A).toReal) := by
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A
  have hne : spectralRadius ℂ A ≠ ⊤ := by
    refine (lt_of_le_of_lt (spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ A 0) ?_).ne
    refine ENNReal.mul_lt_top ?_ ?_ <;>
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  have h := (ENNReal.tendsto_toReal hne).comp hG
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm]

/-- [proved-derived; formal-checked] **Gelfand's form of the rate.** For a nonnegative return map
on a nonempty set of states, `N_k^(1/k)` tends to the spectral radius of `M` read over `ℂ`. No
eigenvector is assumed. -/
theorem tendsto_wordCount_rpow_spectralRadius [Nonempty n] (hM : ∀ i j, 0 ≤ M i j) :
    Tendsto (fun k : ℕ => wordCount M k ^ (1 / (k : ℝ))) atTop
      (𝓝 (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal) := by
  have hG := tendsto_norm_pow_rpow (M.map (algebraMap ℝ ℂ))
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hd1 : Tendsto (fun k : ℕ => (Fintype.card n : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 := (Real.continuousAt_const_rpow (a := (Fintype.card n : ℝ)) (b := 0)
      hd.ne').tendsto.comp h0
    rw [Real.rpow_zero] at h1
    exact h1
  have hup := hd1.mul hG
  rw [one_mul] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hG hup ?_ ?_
  · refine Eventually.of_forall fun k => ?_
    exact Real.rpow_le_rpow (norm_nonneg _) (linfty_norm_le_wordCount hM k)
      (by positivity)
  · refine Eventually.of_forall fun k => ?_
    rw [← Real.mul_rpow hd.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (wordCount_nonneg hM k) (wordCount_le_card_mul_linfty_norm hM k)
      (by positivity)

/-- [proved-derived; formal-checked] **`h = log ρ(M)` in Gelfand's form.** Where the spectral
radius is positive, `(1/k)·log N_k` tends to its logarithm. -/
theorem tendsto_log_wordCount_spectralRadius [Nonempty n] (hM : ∀ i j, 0 ≤ M i j)
    (hρ : 0 < (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal) :
    Tendsto (fun k : ℕ => Real.log (wordCount M k) / k) atTop
      (𝓝 (Real.log (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal)) := by
  have h := (Real.continuousAt_log hρ.ne').tendsto.comp (tendsto_wordCount_rpow_spectralRadius hM)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Function.comp_apply]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  rcases (wordCount_nonneg hM k).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (one_div_ne_zero hk0), Real.log_zero, zero_div]
  · rw [Real.log_rpow hpos]
    ring

/-- [proved-derived; formal-checked] **The Perron value is the spectral radius.** A nonnegative
matrix with a strictly positive eigenvector at `λ > 0` has spectral radius `λ` over `ℂ`. -/
theorem spectralRadius_eq_perron [Nonempty n] {v : n → ℝ} {lam : ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, 0 < v i) (heig : M *ᵥ v = lam • v) (hlam : 0 < lam) :
    (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal = lam :=
  tendsto_nhds_unique (tendsto_wordCount_rpow_spectralRadius hM)
    (tendsto_wordCount_rpow hM hv heig hlam)

end Gelfand

/-! ## 5. Ruler: the golden-mean shift -/

section GoldenMean

/-- [definition] The golden-mean shift: two states, the second never followed by itself. -/
def goldenShift : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- [proved-derived; formal-checked] The powers of the golden-mean shift carry the Fibonacci
numbers. -/
theorem goldenShift_pow (k : ℕ) :
    goldenShift ^ k
      = !![(Nat.fib (k + 1) : ℝ), Nat.fib k; Nat.fib k, (Nat.fib (k + 1) : ℝ) - Nat.fib k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, ih, goldenShift]
    have hfib : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, hfib]
    ring

/-- [proved-derived; formal-checked] The golden-mean shift has `F_(k+3)` words of `k` epochs. -/
theorem wordCount_goldenShift (k : ℕ) : wordCount goldenShift k = Nat.fib (k + 3) := by
  have h3 : (Nat.fib (k + 3) : ℝ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    exact_mod_cast Nat.fib_add_two (n := k + 1)
  have h2 : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
    exact_mod_cast Nat.fib_add_two
  rw [wordCount, goldenShift_pow, h3, h2]
  simp [Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] The golden-mean shift has nonnegative entries. -/
theorem goldenShift_nonneg (i j : Fin 2) : 0 ≤ goldenShift i j := by
  fin_cases i <;> fin_cases j <;> simp [goldenShift]

/-- [proved-derived; formal-checked] The Perron vector of the golden-mean shift is `(φ, 1)` at
the value `φ`, by `φ² = φ + 1`. -/
theorem goldenShift_eigen :
    goldenShift *ᵥ ![Real.goldenRatio, 1] = Real.goldenRatio • ![Real.goldenRatio, 1] := by
  have hsq := Real.goldenRatio_sq
  ext i
  fin_cases i
  · simp [goldenShift, mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [hsq]
  · simp [goldenShift, mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The Perron vector `(φ, 1)` is strictly positive. -/
theorem goldenShift_vector_pos (i : Fin 2) : 0 < ![Real.goldenRatio, 1] i := by
  fin_cases i
  · simpa using Real.goldenRatio_pos
  · simp

/-- [proved-derived; formal-checked] **Ruler.** The Fibonacci numbers grow at the rate `log φ`:
`(1/k)·log F_(k+3) → log φ`, read from the growth law of the golden-mean shift. -/
theorem fib_growth :
    Tendsto (fun k : ℕ => Real.log (Nat.fib (k + 3) : ℝ) / k) atTop
      (𝓝 (Real.log Real.goldenRatio)) := by
  have h := tendsto_log_wordCount goldenShift_nonneg goldenShift_vector_pos goldenShift_eigen
    Real.goldenRatio_pos
  simpa [wordCount_goldenShift] using h

/-- [proved-derived; formal-checked] **Ruler.** The spectral radius of the golden-mean shift is
the golden ratio. -/
theorem goldenShift_spectralRadius :
    (spectralRadius ℂ (goldenShift.map (algebraMap ℝ ℂ))).toReal = Real.goldenRatio :=
  spectralRadius_eq_perron goldenShift_nonneg goldenShift_vector_pos goldenShift_eigen
    Real.goldenRatio_pos

end GoldenMean

end Holonics.Aeon.Production.GrowthRate
