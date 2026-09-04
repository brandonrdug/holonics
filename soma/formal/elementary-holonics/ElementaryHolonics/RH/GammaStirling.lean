import Mathlib

/-!
# RT2: Stirling with a remainder

On the sector `Sector = {w ≠ 0 : 0 ≤ Re w ∨ |Re w| ≤ |Im w|}` the Gamma function is
`Γ(w) = √(2π) · exp((w − ½) Log w − w − μ(w))` with the Binet--Euler--Maclaurin remainder
`μ(w) = ∫_0^∞ P₂(x)/(w + x)² dx`, `P₂(x) = ({x}² − {x})/2`, and `‖μ(w)‖ ≤ π/(4‖w‖)`.

The route is Euler's limit `Γ(w) = lim n^w n!/∏_{j ≤ n}(w + j)` (Mathlib's `GammaSeq`), the
trapezoid identity on each unit interval,
`½(Log(w+k) + Log(w+k+1)) − ∫_k^{k+1} Log(w+x) dx = ∫_k^{k+1} g₂(x−k)/(w+x)² dx`, `g₂(u) = (u²−u)/2`,
summed to `Σ_{j≤n} Log(w+j) = ∫_0^n Log(w+x) dx + ½Log w + ½Log(w+n) + μ_n(w)`, and real
Stirling for `n!` (Mathlib's `Stirling.tendsto_stirlingSeq_sqrt_pi`). No logarithm of `Γ` is
taken: every identity is exponentiated before the limit.

**Returned.** `sector_shift`, `norm_μ_le`, `tendsto_μN`, `trapezoid`, `euler_maclaurin`,
`gammaSeq_eq_exp`, `tendsto_E`, **`gamma_eq`** (`Γ(w) = exp((w−½)Log w − w − μ(w) + ½ log 2π)`),
**`gamma_eq_sqrt`** (the `√(2π)` form), and **`gamma_eq_mul`** (the multiplicative form
`Γ(w) = √(2π) exp((w−½)Log w − w)(1 + ρ(w))`, `‖ρ(w)‖ ≤ π/(2‖w‖)` for `‖w‖ ≥ 1`). Every theorem
is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.GammaStirling

open Real Set Filter Topology MeasureTheory intervalIntegral

/-! ## The sector -/

/-- The sector on which the remainder is bounded: `w ≠ 0` and `0 ≤ Re w` or `|Re w| ≤ |Im w|`. -/
def Sector : Set ℂ := {w | w ≠ 0 ∧ (0 ≤ w.re ∨ |w.re| ≤ |w.im|)}

theorem ne_zero_of_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) : z ≠ 0 := by
  rintro rfl
  simp [Complex.mem_slitPlane_iff] at hz

/-- Every point `w + x`, `x ≥ 0`, of a sector point is off the slit, and
`‖w + x‖² ≥ (x² + ‖w‖²)/4`. -/
theorem sector_shift {w : ℂ} (hw : w ∈ Sector) {x : ℝ} (hx : 0 ≤ x) :
    (w + x) ∈ Complex.slitPlane ∧ (x ^ 2 + ‖w‖ ^ 2) / 4 ≤ ‖w + x‖ ^ 2 := by
  obtain ⟨hw0, hcase⟩ := hw
  have hre : (w + x).re = w.re + x := by simp
  have him : (w + x).im = w.im := by simp
  have hn : ‖w + x‖ ^ 2 = (w.re + x) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hnw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rcases hcase with h | h
  · refine ⟨?_, ?_⟩
    · rw [Complex.mem_slitPlane_iff, hre, him]
      rcases lt_or_eq_of_le (add_nonneg h hx) with hpos | hzero
      · exact Or.inl hpos
      · right
        intro him0
        apply hw0
        apply Complex.ext
        · simp
          linarith
        · simpa using him0
    · rw [hn, hnw]
      nlinarith [sq_nonneg w.re, mul_nonneg h hx]
  · have him0 : w.im ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have : w.re = 0 := abs_nonpos_iff.mp h
      exact hw0 (Complex.ext this h0)
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_slitPlane_iff, him]
      exact Or.inr him0
    · rw [hn, hnw]
      have h1 : w.re ^ 2 ≤ w.im ^ 2 := by
        rw [← sq_abs w.re, ← sq_abs w.im]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      nlinarith [sq_nonneg (3 * x + 4 * w.re)]

theorem sector_shift_nat {w : ℂ} (hw : w ∈ Sector) (j : ℕ) : w + (j : ℂ) ≠ 0 := by
  have := (sector_shift hw (Nat.cast_nonneg j)).1
  rw [Complex.ofReal_natCast] at this
  exact ne_zero_of_slit this

/-! ## The trapezoid weight -/

/-- `g₂(u) = (u² − u)/2`. -/
def g₂ (u : ℝ) : ℝ := (u ^ 2 - u) / 2

theorem abs_g₂_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |g₂ u| ≤ 1 / 8 := by
  unfold g₂
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (u - 1 / 2)]

theorem g₂_zero : g₂ 0 = 0 := by
  unfold g₂
  ring

theorem g₂_one : g₂ 1 = 0 := by
  unfold g₂
  ring

/-- The periodic weight `P₂(x) = g₂({x})`. -/
def P₂ (x : ℝ) : ℝ := g₂ (Int.fract x)

theorem abs_P₂_le (x : ℝ) : |P₂ x| ≤ 1 / 8 :=
  abs_g₂_le (Int.fract_nonneg x) (Int.fract_lt_one x).le

theorem P₂_eq {k : ℕ} {x : ℝ} (hx : x ∈ Icc (k : ℝ) (k + 1)) : P₂ x = g₂ (x - k) := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h]
    unfold P₂
    have : Int.fract ((k : ℝ) + 1) = 0 := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Int.fract_natCast]
    rw [this, add_sub_cancel_left, g₂_zero, g₂_one]
  · unfold P₂
    have hf : ⌊x⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      exact ⟨hx.1, h⟩
    rw [Int.fract, hf]
    push_cast
    rfl

theorem hasDerivAt_g₂ (u : ℝ) : HasDerivAt g₂ (u - 1 / 2) u := by
  have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  have h2 := (h1.sub (hasDerivAt_id' u)).div_const 2
  refine h2.congr_deriv ?_
  ring

theorem continuous_g₂ : Continuous g₂ := by
  unfold g₂
  fun_prop

theorem measurable_P₂ : Measurable P₂ :=
  continuous_g₂.measurable.comp measurable_fract

/-! ## The remainder -/

/-- The Binet--Euler--Maclaurin remainder `μ(w) = ∫_0^∞ P₂(x)/(w + x)² dx`. -/
def μ (w : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2

/-- Its truncation `μ_n(w) = ∫_0^n P₂(x)/(w + x)² dx`. -/
def μN (w : ℂ) (n : ℕ) : ℂ := ∫ x in (0 : ℝ)..n, ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2

theorem integrable_inv_sq_add {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => (x ^ 2 + c ^ 2)⁻¹) := by
  have h := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc.ne')
  have h2 := h.const_mul (c ^ 2)⁻¹
  refine h2.congr (Eventually.of_forall fun x => ?_)
  show (c ^ 2)⁻¹ * (1 + (c⁻¹ * x) ^ 2)⁻¹ = (x ^ 2 + c ^ 2)⁻¹
  field_simp
  ring

theorem integral_Ioi_inv_sq_add {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), (x ^ 2 + c ^ 2)⁻¹ = π / (2 * c) := by
  have h1 : ∀ x : ℝ, (x ^ 2 + c ^ 2)⁻¹ = (c ^ 2)⁻¹ * (1 + (c⁻¹ * x) ^ 2)⁻¹ := by
    intro x
    field_simp
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul, integral_comp_mul_left_Ioi (fun y : ℝ => (1 + y ^ 2)⁻¹) 0 (inv_pos.mpr hc)]
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, arctan_zero, sub_zero, inv_inv, smul_eq_mul]
  field_simp

theorem norm_term_le {w : ℂ} (hw : w ∈ Sector) {x : ℝ} (hx : 0 ≤ x) :
    ‖((P₂ x : ℝ) : ℂ) / (w + x) ^ 2‖ ≤ (1 / 2) * (x ^ 2 + ‖w‖ ^ 2)⁻¹ := by
  obtain ⟨_, hn⟩ := sector_shift hw hx
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw.1
  have hpos : 0 < x ^ 2 + ‖w‖ ^ 2 := by positivity
  have hden : 0 < ‖w + x‖ ^ 2 := lt_of_lt_of_le (by positivity) hn
  rw [div_le_iff₀ hden]
  calc |P₂ x| ≤ 1 / 8 := abs_P₂_le x
    _ = (1 / 2) * (x ^ 2 + ‖w‖ ^ 2)⁻¹ * ((x ^ 2 + ‖w‖ ^ 2) / 4) := by
        field_simp
        norm_num
    _ ≤ (1 / 2) * (x ^ 2 + ‖w‖ ^ 2)⁻¹ * ‖w + x‖ ^ 2 := by gcongr

theorem measurable_term (w : ℂ) : Measurable (fun x : ℝ => ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2) :=
  (Complex.measurable_ofReal.comp measurable_P₂).div
    ((by fun_prop : Continuous fun x : ℝ => (w + (x : ℂ)) ^ 2).measurable)

theorem integrableOn_term {w : ℂ} (hw : w ∈ Sector) :
    IntegrableOn (fun x : ℝ => ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2) (Ioi 0) := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw.1
  refine (((integrable_inv_sq_add hw0).const_mul (1 / 2)).integrableOn).mono'
    (measurable_term w).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact norm_term_le hw (le_of_lt hx)

/-- **The remainder bound**: `‖μ(w)‖ ≤ π/(4‖w‖)` on the sector. -/
theorem norm_μ_le {w : ℂ} (hw : w ∈ Sector) : ‖μ w‖ ≤ π / (4 * ‖w‖) := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw.1
  calc ‖μ w‖ ≤ ∫ x in Ioi (0 : ℝ), (1 / 2) * (x ^ 2 + ‖w‖ ^ 2)⁻¹ := by
        apply MeasureTheory.norm_integral_le_of_norm_le ((integrable_inv_sq_add hw0).const_mul (1 / 2)).integrableOn
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        exact norm_term_le hw hx.le
    _ = (1 / 2) * (π / (2 * ‖w‖)) := by rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_sq_add hw0]
    _ = π / (4 * ‖w‖) := by ring

theorem tendsto_μN {w : ℂ} (hw : w ∈ Sector) : Tendsto (μN w) atTop (𝓝 (μ w)) := by
  have hU : (⋃ n : ℕ, Ioc (0 : ℝ) n) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨n, h, _⟩
      exact h
    · intro h
      exact ⟨⌈x⌉₊, h, Nat.le_ceil x⟩
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) n) := by
    intro m n hmn
    exact Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have h := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun x : ℝ => ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2) (fun n : ℕ => measurableSet_Ioc) hmono
    (by rw [hU]; exact integrableOn_term hw)
  rw [hU] at h
  refine h.congr fun n => ?_
  unfold μN
  rw [integral_of_le (Nat.cast_nonneg n)]

/-! ## The trapezoid identity and Euler--Maclaurin -/

theorem hasDerivAt_add_ofReal (w : ℂ) (x : ℝ) : HasDerivAt (fun y : ℝ => w + (y : ℂ)) 1 x := by
  simpa using ((hasDerivAt_id x).ofReal_comp).const_add w

theorem hasDerivAt_log_add {w : ℂ} (hw : w ∈ Sector) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log (w + y)) (1 / (w + x)) x := by
  have hslit := (sector_shift hw hx).1
  have h2 := ((Complex.hasDerivAt_log hslit).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_add w))
  have h3 := h2.comp_ofReal
  simpa [one_div] using h3

theorem continuousAt_log_add {w : ℂ} (hw : w ∈ Sector) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousAt (fun y : ℝ => Complex.log (w + y)) x :=
  (hasDerivAt_log_add hw hx).continuousAt

/-- **The trapezoid identity on a unit interval.** -/
theorem trapezoid {w : ℂ} (hw : w ∈ Sector) (k : ℕ) :
    (1 / 2 : ℂ) * (Complex.log (w + k) + Complex.log (w + (k + 1))) -
        ∫ x in (k : ℝ)..(k + 1), Complex.log (w + x) =
      ∫ x in (k : ℝ)..(k + 1), ((g₂ (x - k) : ℝ) : ℂ) / (w + x) ^ 2 := by
  have hk1 : (k : ℝ) ≤ k + 1 := by linarith
  have hnonneg : ∀ x ∈ uIcc (k : ℝ) (k + 1), 0 ≤ x := by
    intro x hx
    rw [uIcc_of_le hk1] at hx
    exact le_trans (Nat.cast_nonneg k) hx.1
  set A : ℝ → ℂ := fun x => ((x - k - 1 / 2 : ℝ) : ℂ) * Complex.log (w + x) -
    ((g₂ (x - k) : ℝ) : ℂ) / (w + x) with hA
  have hderiv : ∀ x ∈ uIcc (k : ℝ) (k + 1),
      HasDerivAt A (Complex.log (w + x) + ((g₂ (x - k) : ℝ) : ℂ) / (w + x) ^ 2) x := by
    intro x hx
    have hx0 := hnonneg x hx
    have hne : w + x ≠ 0 := ne_zero_of_slit (sector_shift hw hx0).1
    have hlog := hasDerivAt_log_add hw hx0
    have hlin : HasDerivAt (fun y : ℝ => ((y - k - 1 / 2 : ℝ) : ℂ)) 1 x := by
      have : HasDerivAt (fun y : ℝ => y - k - 1 / 2) 1 x :=
        ((hasDerivAt_id x).sub_const _).sub_const _
      simpa using this.ofReal_comp
    have hg : HasDerivAt (fun y : ℝ => ((g₂ (y - k) : ℝ) : ℂ)) ((x - k - 1 / 2 : ℝ) : ℂ) x := by
      have h1 : HasDerivAt (fun y : ℝ => g₂ (y - k)) (x - k - 1 / 2) x := by
        have h := (hasDerivAt_g₂ (x - k)).comp x ((hasDerivAt_id x).sub_const (k : ℝ))
        exact h.congr_deriv (by simp)
      exact h1.ofReal_comp
    have hquot := hg.div (hasDerivAt_add_ofReal w x) hne
    have := (hlin.mul hlog).sub hquot
    refine this.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn
      (fun x : ℝ => Complex.log (w + x) + ((g₂ (x - k) : ℝ) : ℂ) / (w + x) ^ 2)
      (uIcc (k : ℝ) (k + 1)) := by
    intro x hx
    have hx0 := hnonneg x hx
    have hne : (w + (x : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ (ne_zero_of_slit (sector_shift hw hx0).1)
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_log_add hw hx0).add
    exact ((Complex.continuous_ofReal.comp (continuous_g₂.comp
      (continuous_id.sub continuous_const))).continuousAt).div
      ((by fun_prop : Continuous fun y : ℝ => (w + (y : ℂ)) ^ 2).continuousAt) hne
  have hint : IntervalIntegrable
      (fun x : ℝ => Complex.log (w + x) + ((g₂ (x - k) : ℝ) : ℂ) / (w + x) ^ 2) volume
      (k : ℝ) (k + 1) := hcont.intervalIntegrable
  have hfund := integral_eq_sub_of_hasDerivAt hderiv hint
  have hint1 : IntervalIntegrable (fun x : ℝ => Complex.log (w + x)) volume (k : ℝ) (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_log_add hw (hnonneg x hx)).continuousWithinAt
  have hint2 : IntervalIntegrable (fun x : ℝ => ((g₂ (x - k) : ℝ) : ℂ) / (w + x) ^ 2) volume
      (k : ℝ) (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hne : (w + (x : ℂ)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (ne_zero_of_slit (sector_shift hw (hnonneg x hx)).1)
    apply ContinuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.comp (continuous_g₂.comp
      (continuous_id.sub continuous_const))).continuousAt).div
      ((by fun_prop : Continuous fun y : ℝ => (w + (y : ℂ)) ^ 2).continuousAt) hne
  rw [integral_add hint1 hint2] at hfund
  have hAk : A k = -(1 / 2 : ℂ) * Complex.log (w + k) := by
    rw [hA]
    simp only [sub_self, zero_sub, g₂_zero]
    push_cast
    ring
  have hAk1 : A (k + 1) = (1 / 2 : ℂ) * Complex.log (w + (k + 1)) := by
    rw [hA]
    simp only [add_sub_cancel_left, g₂_one]
    push_cast
    ring
  rw [hAk, hAk1] at hfund
  push_cast at hfund ⊢
  simp only [← add_assoc] at hfund ⊢
  linear_combination (-1 : ℂ) * hfund

/-- **Euler--Maclaurin for the logarithms**:
`Σ_{j ≤ n} Log(w + j) = ∫_0^n Log(w + x) dx + ½ Log w + ½ Log(w + n) + μ_n(w)`. -/
theorem euler_maclaurin {w : ℂ} (hw : w ∈ Sector) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Complex.log (w + j) =
      (∫ x in (0 : ℝ)..n, Complex.log (w + x)) + (1 / 2 : ℂ) * Complex.log w +
        (1 / 2 : ℂ) * Complex.log (w + n) + μN w n := by
  induction n with
  | zero =>
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero,
      integral_same, zero_add]
    unfold μN
    simp only [Nat.cast_zero, integral_same, add_zero]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hk1 : (n : ℝ) ≤ n + 1 := by linarith
    have htrap := trapezoid hw n
    have hP : ∫ x in (n : ℝ)..(n + 1), ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2 =
        ∫ x in (n : ℝ)..(n + 1), ((g₂ (x - n) : ℝ) : ℂ) / (w + x) ^ 2 := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hk1] at hx
      simp only [P₂_eq hx]
    have hintLog : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        IntervalIntegrable (fun x : ℝ => Complex.log (w + x)) volume a b := by
      intro a b ha hb
      apply ContinuousOn.intervalIntegrable
      intro x hx
      have : 0 ≤ x := by
        rcases le_total a b with h | h
        · rw [uIcc_of_le h] at hx; exact le_trans ha hx.1
        · rw [uIcc_of_ge h] at hx; exact le_trans hb hx.1
      exact (continuousAt_log_add hw this).continuousWithinAt
    have hintP : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        IntervalIntegrable (fun x : ℝ => ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2) volume a b := by
      intro a b ha hb
      rw [intervalIntegrable_iff]
      apply (integrableOn_term hw).mono_set
      intro x hx
      rcases le_total a b with h | h
      · rw [uIoc_of_le h] at hx; exact lt_of_le_of_lt ha hx.1
      · rw [uIoc_of_ge h] at hx; exact lt_of_le_of_lt hb hx.1
    have hsplitLog : ∫ x in (0 : ℝ)..((n + 1 : ℕ) : ℝ), Complex.log (w + x) =
        (∫ x in (0 : ℝ)..n, Complex.log (w + x)) +
          ∫ x in (n : ℝ)..(n + 1), Complex.log (w + x) := by
      push_cast
      rw [integral_add_adjacent_intervals (hintLog 0 n le_rfl (Nat.cast_nonneg n))
        (hintLog n (n + 1) (Nat.cast_nonneg n) (by linarith))]
    have hsplitP : μN w (n + 1) = μN w n + ∫ x in (n : ℝ)..(n + 1), ((P₂ x : ℝ) : ℂ) / (w + x) ^ 2 := by
      unfold μN
      push_cast
      rw [integral_add_adjacent_intervals (hintP 0 n le_rfl (Nat.cast_nonneg n))
        (hintP n (n + 1) (Nat.cast_nonneg n) (by linarith))]
    rw [hsplitLog, hsplitP, hP]
    push_cast at htrap ⊢
    linear_combination htrap

/-! ## The integral of the logarithm -/

theorem integral_log_add {w : ℂ} (hw : w ∈ Sector) (n : ℕ) :
    ∫ x in (0 : ℝ)..n, Complex.log (w + x) =
      (w + n) * Complex.log (w + n) - (w + n) - (w * Complex.log w - w) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) n,
      HasDerivAt (fun y : ℝ => (w + y) * Complex.log (w + y) - (w + y)) (Complex.log (w + x)) x := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le (Nat.cast_nonneg n)] at hx
      exact hx.1
    have hne : w + x ≠ 0 := ne_zero_of_slit (sector_shift hw hx0).1
    have h1 := (hasDerivAt_add_ofReal w x).mul (hasDerivAt_log_add hw hx0)
    have h2 := h1.sub (hasDerivAt_add_ofReal w x)
    refine h2.congr_deriv ?_
    rw [mul_one_div_cancel hne]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => Complex.log (w + x)) volume 0 n := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (Nat.cast_nonneg n)] at hx
    exact (continuousAt_log_add hw hx.1).continuousWithinAt
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp

/-! ## Euler's limit as an exponential -/

/-- `E_n(w) = w log n + log n! − Σ_{j ≤ n} Log(w + j)`. -/
def E (w : ℂ) (n : ℕ) : ℂ :=
  w * (Real.log n : ℂ) + (Real.log (n.factorial : ℝ) : ℂ) -
    ∑ j ∈ Finset.range (n + 1), Complex.log (w + j)

theorem gammaSeq_eq_exp {w : ℂ} (hw : w ∈ Sector) {n : ℕ} (hn : 1 ≤ n) :
    Complex.GammaSeq w n = Complex.exp (E w n) := by
  unfold Complex.GammaSeq E
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℂ) ^ w = Complex.exp (w * (Real.log n : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hn0.le, mul_comm]
  have h2 : ((n.factorial : ℕ) : ℂ) = Complex.exp (Real.log (n.factorial : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast Nat.factorial_pos n)]
    push_cast
    rfl
  have h3 : ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) =
      Complex.exp (∑ j ∈ Finset.range (n + 1), Complex.log (w + j)) := by
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [Complex.exp_log (sector_shift_nat hw j)]
  rw [h1, h2, h3, ← Complex.exp_add, ← Complex.exp_sub]

/-- The real Stirling defect `δ_n = log n! − ((n + ½) log n − n + ½ log 2π)`. -/
def δ (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - (((n : ℝ) + 1 / 2) * Real.log n - n + 1 / 2 * Real.log (2 * π))

theorem δ_eq {n : ℕ} (hn : 1 ≤ n) : δ n = Real.log (Stirling.stirlingSeq n) - Real.log π / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfact : (n.factorial : ℝ) = Stirling.stirlingSeq n * (√(2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
    unfold Stirling.stirlingSeq
    have : √(2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
    field_simp
  have hS : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  unfold δ
  rw [hfact, Real.log_mul hS.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hn0.ne' (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_mul (by norm_num) hn0.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
  ring

theorem tendsto_δ : Tendsto δ atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log π / 2) atTop
      (𝓝 (Real.log (√π) - Real.log π / 2)) :=
    ((Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const _
  rw [Real.log_sqrt Real.pi_pos.le, sub_self] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (δ_eq hn).symm

theorem E_eq {w : ℂ} (hw : w ∈ Sector) {n : ℕ} (hn : 1 ≤ n) :
    E w n = -(w + n + 1 / 2) * Complex.log (1 + w / n) +
      ((w - 1 / 2) * Complex.log w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ) - μN w n) + (δ n : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : 1 + w / n ≠ 0 := by
    have := sector_shift_nat hw n
    intro h
    apply this
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    calc w + n = n * (1 + w / n) := by
          field_simp
          ring
      _ = 0 := by rw [h, mul_zero]
  have hlog : Complex.log (w + n) = (Real.log n : ℂ) + Complex.log (1 + w / n) := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [← Complex.log_ofReal_mul hn0 hne]
    congr 1
    push_cast
    field_simp
    ring
  unfold E
  rw [euler_maclaurin hw n, integral_log_add hw n, hlog]
  unfold δ
  push_cast
  ring

theorem tendsto_log_one_add_div {w : ℂ} :
    Tendsto (fun n : ℕ => (w + n + 1 / 2) * Complex.log (1 + w / n)) atTop (𝓝 w) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C : ℝ := ‖w + 1 / 2‖ * ‖w‖ + (‖w‖ + 1 / 2) * ‖w‖ ^ 2 + ‖w‖ ^ 2 with hC
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop (⌈2 * ‖w‖⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by
    have : (⌈2 * ‖w‖⌉₊ + 1 : ℕ) ≤ n := hn
    exact_mod_cast (le_trans (Nat.le_add_left 1 _) this)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnw : 2 * ‖w‖ ≤ n := by
    have h1 : (⌈2 * ‖w‖⌉₊ : ℝ) ≤ n := by
      have : (⌈2 * ‖w‖⌉₊ : ℕ) ≤ n := le_trans (Nat.le_add_right _ 1) hn
      exact_mod_cast this
    exact (Nat.le_ceil _).trans h1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = w / n := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = Complex.log (1 + a) - a := ⟨_, rfl⟩
  have hanorm : ‖a‖ = ‖w‖ / n := by
    rw [ha, norm_div, Complex.norm_natCast]
  have ha_le : ‖a‖ ≤ 1 / 2 := by
    rw [hanorm, div_le_iff₀ hn0]
    linarith
  have ha_lt : ‖a‖ < 1 := by linarith
  have hr_le : ‖r‖ ≤ ‖a‖ ^ 2 := by
    have := Complex.norm_log_one_add_sub_self_le ha_lt
    rw [← hr] at this
    have h2 : (1 - ‖a‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖r‖ ≤ ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2 := this
      _ ≤ ‖a‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖a‖ ^ 2 := by ring
  have hna : (n : ℂ) * a = w := by
    rw [ha]
    field_simp
  have hident : (w + n + 1 / 2) * Complex.log (1 + w / n) - w =
      (w + 1 / 2) * a + (w + n + 1 / 2) * r := by
    rw [hr, ← ha]
    linear_combination hna
  rw [hident]
  have hnormn : ‖(n : ℂ)‖ = (n : ℝ) := Complex.norm_natCast n
  calc ‖(w + 1 / 2) * a + (w + n + 1 / 2) * r‖
      ≤ ‖w + 1 / 2‖ * ‖a‖ + (‖w‖ + n + 1 / 2) * ‖r‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        gcongr
        calc ‖w + n + 1 / 2‖ ≤ ‖w‖ + ‖(n : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
              refine (norm_add_le _ _).trans ?_
              gcongr
              exact norm_add_le _ _
          _ = ‖w‖ + n + 1 / 2 := by
              rw [hnormn]
              norm_num
    _ ≤ ‖w + 1 / 2‖ * (‖w‖ / n) + (‖w‖ + n + 1 / 2) * (‖w‖ / n) ^ 2 := by
        rw [← hanorm]
        gcongr
    _ ≤ C / n := by
        rw [hC]
        have hnn : (1 : ℝ) / n ^ 2 ≤ 1 / n := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          nlinarith
        have e1 : ‖w + 1 / 2‖ * (‖w‖ / n) = ‖w + 1 / 2‖ * ‖w‖ * (1 / n) := by ring
        have e2 : (‖w‖ + n + 1 / 2) * (‖w‖ / n) ^ 2 =
            (‖w‖ + 1 / 2) * ‖w‖ ^ 2 * (1 / n ^ 2) + ‖w‖ ^ 2 * (1 / n) := by
          field_simp
          ring
        rw [e1, e2]
        calc ‖w + 1 / 2‖ * ‖w‖ * (1 / n) + ((‖w‖ + 1 / 2) * ‖w‖ ^ 2 * (1 / n ^ 2) + ‖w‖ ^ 2 * (1 / n))
            ≤ ‖w + 1 / 2‖ * ‖w‖ * (1 / n) + ((‖w‖ + 1 / 2) * ‖w‖ ^ 2 * (1 / n) + ‖w‖ ^ 2 * (1 / n)) := by
              gcongr
          _ = C / n := by
              rw [hC]
              ring

/-- **The limit of `E_n(w)`.** -/
theorem tendsto_E {w : ℂ} (hw : w ∈ Sector) :
    Tendsto (E w) atTop
      (𝓝 (-w + ((w - 1 / 2) * Complex.log w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ) - μ w))) := by
  have h1 : Tendsto (fun n : ℕ => -(w + n + 1 / 2) * Complex.log (1 + w / n)) atTop (𝓝 (-w)) := by
    have := tendsto_log_one_add_div (w := w) |>.neg
    refine this.congr fun n => ?_
    ring
  have h2 : Tendsto (fun n : ℕ => (w - 1 / 2) * Complex.log w +
      (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ) - μN w n) atTop
      (𝓝 ((w - 1 / 2) * Complex.log w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ) - μ w)) :=
    tendsto_const_nhds.sub (tendsto_μN hw)
  have h3 : Tendsto (fun n : ℕ => ((δ n : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_δ
    rw [Complex.ofReal_zero] at this
    exact this
  have h := (h1.add h2).add h3
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (E_eq hw hn).symm

/-! ## Stirling -/

/-- **Stirling with a remainder**: on the sector,
`Γ(w) = exp((w − ½) Log w − w − μ(w) + ½ log 2π)`. -/
theorem gamma_eq {w : ℂ} (hw : w ∈ Sector) :
    Complex.Gamma w =
      Complex.exp ((w - 1 / 2) * Complex.log w - w - μ w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)) := by
  have hG := Complex.GammaSeq_tendsto_Gamma w
  have hE := (Complex.continuous_exp.tendsto _).comp (tendsto_E hw)
  have hEq : Tendsto (Complex.GammaSeq w) atTop
      (𝓝 (Complex.exp (-w + ((w - 1 / 2) * Complex.log w +
        (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ) - μ w)))) := by
    refine hE.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (gammaSeq_eq_exp hw hn).symm
  rw [tendsto_nhds_unique hG hEq]
  congr 1
  ring

theorem exp_half_log_two_pi : Real.exp (1 / 2 * Real.log (2 * π)) = √(2 * π) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
  ring_nf

/-- **Stirling, the `√(2π)` form**: `Γ(w) = √(2π) exp((w − ½) Log w − w − μ(w))`. -/
theorem gamma_eq_sqrt {w : ℂ} (hw : w ∈ Sector) :
    Complex.Gamma w = (√(2 * π) : ℝ) * Complex.exp ((w - 1 / 2) * Complex.log w - w - μ w) := by
  rw [gamma_eq hw, Complex.exp_add, mul_comm]
  congr 1
  rw [← exp_half_log_two_pi, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The multiplicative remainder `ρ(w) = e^{−μ(w)} − 1`. -/
def ρ (w : ℂ) : ℂ := Complex.exp (-μ w) - 1

/-- **Stirling, the multiplicative form**:
`Γ(w) = √(2π) exp((w − ½) Log w − w) (1 + ρ(w))`. -/
theorem gamma_eq_mul {w : ℂ} (hw : w ∈ Sector) :
    Complex.Gamma w =
      (√(2 * π) : ℝ) * Complex.exp ((w - 1 / 2) * Complex.log w - w) * (1 + ρ w) := by
  rw [gamma_eq_sqrt hw]
  unfold ρ
  rw [add_sub_cancel, mul_assoc, ← Complex.exp_add]
  congr 2

/-- `‖ρ(w)‖ ≤ π/(2‖w‖)` for `‖w‖ ≥ 1` on the sector. -/
theorem norm_ρ_le {w : ℂ} (hw : w ∈ Sector) (h1 : 1 ≤ ‖w‖) : ‖ρ w‖ ≤ π / (2 * ‖w‖) := by
  have hμ := norm_μ_le hw
  have hμ1 : ‖-μ w‖ ≤ 1 := by
    rw [norm_neg]
    refine hμ.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_lt_four]
  unfold ρ
  calc ‖Complex.exp (-μ w) - 1‖ ≤ 2 * ‖-μ w‖ := Complex.norm_exp_sub_one_le hμ1
    _ ≤ 2 * (π / (4 * ‖w‖)) := by
        rw [norm_neg]
        gcongr
    _ = π / (2 * ‖w‖) := by
        field_simp
        ring

end Soma.Holonics.RH.GammaStirling
