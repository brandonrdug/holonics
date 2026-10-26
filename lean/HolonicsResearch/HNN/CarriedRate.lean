import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# The critically tuned carried rate contracts by `q` a pass

The record `research/records/2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md`
(§0 statement 5 and §4; atlas `contact.pass-reach-gap`) reads relaxation of a quadratic with
constitution `H`, spectrum in `[λ_min, λ_max]`, `κ = λ_max/λ_min`: the plain step
`x ← x − α(Hx − b)` contracts by `(κ − 1)/(κ + 1)` a pass, the carried-rate step
`x ← x − α(Hx − b) + β(x − x_prev)` with `α = 4/(√λ_max + √λ_min)²`, `β = q²`,
`q = (√κ − 1)/(√κ + 1)` by `q`. #410 owes the carried rate's contraction; this file proves it on
every eigendirection. Write `a = √λ_min` and `b = √λ_max`, so `α = 4/(a + b)²` (`rate`) and
`q = (b − a)/(b + a)` (`contraction`).

[proved-standard; formal-checked] What is proved.

1. **The error recurrence** (`carried_step_error`): on an eigendirection `λ`, the error of the
   carried step obeys `e_(k+1) = (1 + β − αλ) e_k − β e_(k−1)`, with characteristic polynomial
   `z² − (1 + β − αλ) z + β`.
2. **The tuned rate places every eigendirection in the band** (`tuned_band`):
   `αλ ∈ [(1 − q)², (1 + q)²]` for `λ ∈ [a², b²]`, the ends at the ends of the spectrum.
3. **The band is where the roots leave the real axis** (`disc_nonpos`): in the band
   `(1 + q² − αλ)² ≤ 4q²`.
4. **Then every root has modulus exactly `q`** (`root_normSq`, `root_norm`,
   `carried_rate_contraction`): a complex pair in the interior, a double root at the two ends.
5. **The error falls like `q^t` up to the double root's factor `t`** (`roots_exist`,
   `homSum_recurrence`, `recurrence_closed_form`, `norm_homSum_le`, `carried_error_bound`): every
   solution of the recurrence reads `e_(t+1) = s_(t+1) e_1 − β s_t e_0` with
   `s_t = Σ_(j<t) z₁^j z₂^(t−1−j)`, and `‖e_(t+1)‖ ≤ (t + 1) q^t (‖e_1‖ + q ‖e_0‖)`.
6. **The plain step contracts by `(κ − 1)/(κ + 1)`** (`plain_step`): with `α = 2/(λ_min + λ_max)`,
   `|1 − αλ| ≤ (λ_max − λ_min)/(λ_max + λ_min)` on the spectrum.

The receipt's pass counts (plain 28, 77, 246, 908 against carried 12, 20, 37, 73 at `κ ≤ m²`,
`m = 3, 5, 9, 17`) are measurements on the path of 33 vertices and stay in the record.

The computational object is the helical pair interaction: the carried rate is the pair's turn, the
two roots a turning pair of modulus `q` (`K + K⁻¹ + 2 = tr²/det` of the swing guide), so the
error turns while it contracts. Of the winding guide's six general objects this touches the helix
(the carried turn) and the tube (the passes as a clocked span); the pair, faces and placement, the
cell holonomy and the tower thread stay attached.

Consumers: the atlas row `contact.pass-reach-gap`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.CarriedRate

/-! ## 1. The recurrence and the band -/

/-- [definition] The tuned rate `α = 4/(√λ_max + √λ_min)²`, with `a = √λ_min`, `b = √λ_max`. -/
def rate (a b : ℝ) : ℝ := 4 / (a + b) ^ 2

/-- [definition] The carried contraction `q = (√κ − 1)/(√κ + 1) = (b − a)/(b + a)`. -/
def contraction (a b : ℝ) : ℝ := (b - a) / (b + a)

/-- [proved-standard; formal-checked] **The error recurrence of the carried step** on an
eigendirection `λ` with fixed point `x*`. -/
theorem carried_step_error (α β l xs xk xp : ℝ) :
    (xk - α * (l * xk - l * xs) + β * (xk - xp)) - xs =
      (1 + β - α * l) * (xk - xs) - β * (xp - xs) := by
  ring

/-- [proved-standard; formal-checked] **The tuned rate places every eigendirection in the band:**
`(1 − q)² ≤ αλ ≤ (1 + q)²` for `λ ∈ [a², b²]`. -/
theorem tuned_band {a b l : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl1 : a ^ 2 ≤ l) (hl2 : l ≤ b ^ 2) :
    (1 - contraction a b) ^ 2 ≤ rate a b * l ∧ rate a b * l ≤ (1 + contraction a b) ^ 2 := by
  have hs : a + b ≠ 0 := (by linarith : 0 < a + b).ne'
  have hs' : b + a ≠ 0 := (by linarith : 0 < b + a).ne'
  have e1 : (1 - contraction a b) ^ 2 = rate a b * a ^ 2 := by
    unfold contraction rate
    field_simp
    ring
  have e2 : (1 + contraction a b) ^ 2 = rate a b * b ^ 2 := by
    unfold contraction rate
    field_simp
    ring
  have hα : 0 ≤ rate a b := by unfold rate; positivity
  rw [e1, e2]
  exact ⟨mul_le_mul_of_nonneg_left hl1 hα, mul_le_mul_of_nonneg_left hl2 hα⟩

/-- [proved-standard; formal-checked] **In the band the discriminant is not positive:**
`(1 + q² − x)² ≤ 4q²` when `(1 − q)² ≤ x ≤ (1 + q)²`. -/
theorem disc_nonpos {q x : ℝ} (h1 : (1 - q) ^ 2 ≤ x) (h2 : x ≤ (1 + q) ^ 2) :
    (1 + q ^ 2 - x) ^ 2 ≤ 4 * q ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-! ## 2. Every root has modulus exactly `q` -/

/-- [proved-standard; formal-checked] **A real quadratic of nonpositive discriminant has its roots
on the circle of radius `√β`:** `z² − tz + β = 0` and `t² ≤ 4β` give `|z|² = β`. -/
theorem root_normSq {t β : ℝ} (hdisc : t ^ 2 ≤ 4 * β) {z : ℂ}
    (hz : z * z - (t : ℂ) * z + (β : ℂ) = 0) : Complex.normSq z = β := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  rw [Complex.normSq_apply]
  have hfac : z.im * (2 * z.re - t) = 0 := by linear_combination him
  rcases mul_eq_zero.mp hfac with h | h
  · have hq : z.re * z.re - t * z.re + β = 0 := by linear_combination hre + z.im * h
    have hsq : (2 * z.re - t) ^ 2 = t ^ 2 - 4 * β := by linear_combination 4 * hq
    have h0 : 2 * z.re - t = 0 := by
      have h00 : (2 * z.re - t) ^ 2 = 0 := le_antisymm (by rw [hsq]; linarith) (sq_nonneg _)
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h00
    linear_combination z.re * h0 + z.im * h - hq
  · linear_combination -hre + z.re * h

/-- [proved-standard; formal-checked] The roots have modulus exactly `q`. -/
theorem root_norm {q t : ℝ} (hq : 0 ≤ q) (hdisc : t ^ 2 ≤ 4 * q ^ 2) {z : ℂ}
    (hz : z * z - (t : ℂ) * z + ((q ^ 2 : ℝ) : ℂ) = 0) : ‖z‖ = q := by
  have h := root_normSq hdisc hz
  rw [Complex.normSq_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg z) hq).mp h

/-- [proved-standard; formal-checked] **The critically tuned carried rate contracts by `q`:** on
every eigendirection `λ ∈ [λ_min, λ_max]` every root of `z² − (1 + q² − αλ)z + q²` has modulus
exactly `q`. -/
theorem carried_rate_contraction {a b l : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl1 : a ^ 2 ≤ l)
    (hl2 : l ≤ b ^ 2) {z : ℂ}
    (hz : z * z - ((1 + contraction a b ^ 2 - rate a b * l : ℝ) : ℂ) * z +
      ((contraction a b ^ 2 : ℝ) : ℂ) = 0) :
    ‖z‖ = contraction a b := by
  have hq : 0 ≤ contraction a b := div_nonneg (by linarith) (by linarith)
  obtain ⟨h1, h2⟩ := tuned_band ha hab hl1 hl2
  exact root_norm hq (disc_nonpos h1 h2) hz

/-! ## 3. The error falls like `q^t` up to the factor `t` -/

/-- [proved-standard; formal-checked] The characteristic polynomial factors over `ℂ`:
`z² − tz + β = (z − z₁)(z − z₂)`, that is `z₁ + z₂ = t` and `z₁ z₂ = β`. -/
theorem roots_exist (t β : ℂ) : ∃ z₁ z₂ : ℂ, z₁ + z₂ = t ∧ z₁ * z₂ = β := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (t * t - 4 * β)
  refine ⟨(t + s) / 2, (t - s) / 2, by ring, ?_⟩
  linear_combination (1 / 4 : ℂ) * hs

/-- [proved-standard; formal-checked] Each factor's root is a root of `z² − (z₁ + z₂)z + z₁z₂`. -/
theorem root_of_factors (z₁ z₂ : ℂ) : z₁ * z₁ - (z₁ + z₂) * z₁ + z₁ * z₂ = 0 := by
  ring

/-- [definition] The complete homogeneous sum `s_t = Σ_(j<t) z₁^j z₂^(t−1−j)`, by
`s_0 = 0`, `s_(t+1) = z₁ s_t + z₂^t`. -/
def homSum (z₁ z₂ : ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => z₁ * homSum z₁ z₂ k + z₂ ^ k

/-- [proved-standard; formal-checked] The complete homogeneous sum obeys the recurrence
`s_(t+2) = (z₁ + z₂) s_(t+1) − z₁ z₂ s_t`. -/
theorem homSum_recurrence (z₁ z₂ : ℂ) (k : ℕ) :
    homSum z₁ z₂ (k + 2) = (z₁ + z₂) * homSum z₁ z₂ (k + 1) - z₁ * z₂ * homSum z₁ z₂ k := by
  simp only [homSum]
  ring

/-- [proved-standard; formal-checked] **Every solution of the recurrence is read from its first two
terms:** `e_(t+1) = s_(t+1) e_1 − z₁ z₂ s_t e_0`. -/
theorem recurrence_closed_form (z₁ z₂ : ℂ) (e : ℕ → ℂ)
    (he : ∀ k, e (k + 2) = (z₁ + z₂) * e (k + 1) - z₁ * z₂ * e k) (k : ℕ) :
    e (k + 1) = homSum z₁ z₂ (k + 1) * e 1 - z₁ * z₂ * homSum z₁ z₂ k * e 0 := by
  have s1 : homSum z₁ z₂ 1 = 1 := by simp [homSum]
  have s2 : homSum z₁ z₂ 2 = z₁ + z₂ := by simp [homSum]
  have key : ∀ k, (e (k + 1) = homSum z₁ z₂ (k + 1) * e 1 - z₁ * z₂ * homSum z₁ z₂ k * e 0) ∧
      e (k + 2) = homSum z₁ z₂ (k + 2) * e 1 - z₁ * z₂ * homSum z₁ z₂ (k + 1) * e 0 := by
    intro k
    induction k with
    | zero =>
      constructor
      · show e 1 = homSum z₁ z₂ 1 * e 1 - z₁ * z₂ * homSum z₁ z₂ 0 * e 0
        rw [s1]
        simp [homSum]
      · show e 2 = homSum z₁ z₂ 2 * e 1 - z₁ * z₂ * homSum z₁ z₂ 1 * e 0
        have h2 : e 2 = (z₁ + z₂) * e 1 - z₁ * z₂ * e 0 := he 0
        rw [h2, s1, s2]
        ring
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih2, ?_⟩
      show e (k + 3) = homSum z₁ z₂ (k + 3) * e 1 - z₁ * z₂ * homSum z₁ z₂ (k + 2) * e 0
      have h3 : e (k + 3) = (z₁ + z₂) * e (k + 2) - z₁ * z₂ * e (k + 1) := he (k + 1)
      have hr : homSum z₁ z₂ (k + 3) =
          (z₁ + z₂) * homSum z₁ z₂ (k + 2) - z₁ * z₂ * homSum z₁ z₂ (k + 1) :=
        homSum_recurrence z₁ z₂ (k + 1)
      rw [h3, hr, ih2, ih1]
      linear_combination (z₁ * z₂ * e 0) * homSum_recurrence z₁ z₂ k
  exact (key k).1

/-- [proved-standard; formal-checked] **The double root's factor:** if both roots have modulus at
most `q`, then `‖s_(t+1)‖ ≤ (t + 1) q^t`. -/
theorem norm_homSum_le {z₁ z₂ : ℂ} {q : ℝ} (hq : 0 ≤ q) (h₁ : ‖z₁‖ ≤ q) (h₂ : ‖z₂‖ ≤ q)
    (k : ℕ) : ‖homSum z₁ z₂ (k + 1)‖ ≤ (k + 1) * q ^ k := by
  induction k with
  | zero => simp [homSum]
  | succ k ih =>
    rw [homSum]
    calc ‖z₁ * homSum z₁ z₂ (k + 1) + z₂ ^ (k + 1)‖
        ≤ ‖z₁ * homSum z₁ z₂ (k + 1)‖ + ‖z₂ ^ (k + 1)‖ := norm_add_le _ _
      _ = ‖z₁‖ * ‖homSum z₁ z₂ (k + 1)‖ + ‖z₂‖ ^ (k + 1) := by rw [norm_mul, norm_pow]
      _ ≤ q * ((k + 1) * q ^ k) + q ^ (k + 1) :=
          add_le_add (mul_le_mul h₁ ih (norm_nonneg _) hq)
            (pow_le_pow_left₀ (norm_nonneg _) h₂ _)
      _ = (((k + 1 : ℕ) : ℝ) + 1) * q ^ (k + 1) := by
          push_cast
          ring

/-- [proved-standard; formal-checked] **The error of `t + 1` carried passes is at most
`(t + 1) q^t (‖e_1‖ + q ‖e_0‖)`** when both roots of the characteristic polynomial have modulus at
most `q`: it falls like `q^t` up to the double root's factor `t`. -/
theorem carried_error_bound {z₁ z₂ : ℂ} {q : ℝ} (hq : 0 ≤ q) (h₁ : ‖z₁‖ ≤ q) (h₂ : ‖z₂‖ ≤ q)
    (e : ℕ → ℂ) (he : ∀ k, e (k + 2) = (z₁ + z₂) * e (k + 1) - z₁ * z₂ * e k) (k : ℕ) :
    ‖e (k + 1)‖ ≤ (k + 1) * q ^ k * (‖e 1‖ + q * ‖e 0‖) := by
  rw [recurrence_closed_form z₁ z₂ e he k]
  have hs1 := norm_homSum_le hq h₁ h₂ k
  have hs0 : ‖homSum z₁ z₂ k‖ * q ≤ (k + 1) * q ^ k := by
    cases k with
    | zero => simp [homSum]
    | succ k =>
      have h := norm_homSum_le hq h₁ h₂ k
      have hqk : 0 ≤ q ^ (k + 1) := pow_nonneg hq _
      calc ‖homSum z₁ z₂ (k + 1)‖ * q ≤ ((k + 1) * q ^ k) * q :=
            mul_le_mul_of_nonneg_right h hq
        _ = (k + 1) * q ^ (k + 1) := by ring
        _ ≤ (((k + 1 : ℕ) : ℝ) + 1) * q ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (by push_cast; linarith) hqk
  have hz : ‖z₁ * z₂‖ ≤ q * q := by
    rw [norm_mul]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) hq
  calc ‖homSum z₁ z₂ (k + 1) * e 1 - z₁ * z₂ * homSum z₁ z₂ k * e 0‖
      ≤ ‖homSum z₁ z₂ (k + 1) * e 1‖ + ‖z₁ * z₂ * homSum z₁ z₂ k * e 0‖ := norm_sub_le _ _
    _ = ‖homSum z₁ z₂ (k + 1)‖ * ‖e 1‖ + ‖z₁ * z₂‖ * ‖homSum z₁ z₂ k‖ * ‖e 0‖ := by
        simp only [norm_mul]
    _ ≤ (k + 1) * q ^ k * ‖e 1‖ + (q * q) * ‖homSum z₁ z₂ k‖ * ‖e 0‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hs1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
            (norm_nonneg _))
    _ = (k + 1) * q ^ k * ‖e 1‖ + q * (‖homSum z₁ z₂ k‖ * q) * ‖e 0‖ := by ring
    _ ≤ (k + 1) * q ^ k * ‖e 1‖ + q * ((k + 1) * q ^ k) * ‖e 0‖ :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs0 hq) (norm_nonneg _))
    _ = (k + 1) * q ^ k * (‖e 1‖ + q * ‖e 0‖) := by ring

/-! ## 4. The plain step -/

/-- [proved-standard; formal-checked] **The plain step contracts by `(κ − 1)/(κ + 1)`:** with
`α = 2/(λ_min + λ_max)`, `|1 − αλ| ≤ (λ_max − λ_min)/(λ_max + λ_min)` for `λ ∈ [λ_min, λ_max]`. -/
theorem plain_step {m M l : ℝ} (hm : 0 < m) (hl1 : m ≤ l) (hl2 : l ≤ M) :
    |1 - 2 / (m + M) * l| ≤ (M - m) / (M + m) := by
  have hs : 0 < m + M := by linarith
  have e : 1 - 2 / (m + M) * l = (m + M - 2 * l) / (m + M) := by
    rw [sub_div, div_self hs.ne', div_mul_eq_mul_div]
  rw [e, add_comm M m, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hs.le

end Holonics.HNN.CarriedRate
