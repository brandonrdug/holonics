import Mathlib
import ElementaryHolonics.RH.EventSaddle

/-!
# RT3 (iii-c): the event on the window, exactly

With `Λ(s) = Log(s/2) − log π`, `J_t(s) = s + tΛ(s)` (Dobner's `J_t` for `ζ`), and `h = 2t log n`,
the `n`-th event at `J_t(s)` is `e^{−tL²} e^{−J L} Γ_t(J + h)`. On the window through the saddle
`z = s + h + iv` the integrand is exactly

`f(z) = g(s) e^{P} e^{−A v² + i q v} (1 + D(v))`,

`P = tΛ²/4 + hℓ(s) + h²ℓ'(s)/2`, `A = 1/(4t) + ℓ'(s)/2`, `q = ε₁(s) + hℓ'(s)`,
`ε₁(s) = ℓ(s) − Λ(s)/2 = 1/(2s) + 1/(s−1)`, and the pointwise defect `D(v)` is bounded through the
segment expansion of `g` and Stirling's remainder: `‖D(v)‖ ≤ (ρ + m) e^{ρ + m}` with
`ρ = 402 (h + |v|)³/‖s‖²` and `m = 2π/(3‖s‖)`.

**Returned.** `ℓ_sub_half_Λ`, `f_window` (the pointwise identity with the defect isolated),
`norm_D_le`, and **`event_decomp`**: the exact decomposition of the event.
-/

noncomputable section

namespace Soma.Holonics.RH.EventMain

open Real Set Filter Topology MeasureTheory intervalIntegral
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle

/-! ## The coordinates -/

/-- `Λ(s) = Log(s/2) − log π`, so that `Λ(s) = Log(s/(2π))` off the slit. -/
def Λ (s : ℂ) : ℂ := Complex.log (s / 2) - (Real.log π : ℂ)

/-- Dobner's `J_t(s) = s + tΛ(s)` (repository time `t`, standard `|t|_D = 4t`). -/
def J (t : ℝ) (s : ℂ) : ℂ := s + t * Λ s

/-- Dobner's `γ_t(s) = g(s) e^{tΛ(s)²/4}`. -/
def γt' (t : ℝ) (s : ℂ) : ℂ := g s * Complex.exp (t * (Λ s) ^ 2 / 4)

/-- `ε₁(s) = 1/(2s) + 1/(s − 1)`, the exact difference `ℓ(s) − Λ(s)/2`. -/
def ε₁ (s : ℂ) : ℂ := (2 * s)⁻¹ + (s - 1)⁻¹

theorem ℓ_sub_half_Λ (s : ℂ) : ℓ s - Λ s / 2 = ε₁ s := by
  unfold ℓ Λ ε₁
  ring

/-- The quadratic coefficient `A = 1/(4t) + ℓ'(s)/2`. -/
def A (t : ℝ) (s : ℂ) : ℂ := 1 / (4 * t) + ℓ' s / 2

/-- The residual phase `q = ε₁(s) + h ℓ'(s)`. -/
def q (s : ℂ) (h : ℝ) : ℂ := ε₁ s + h * ℓ' s

/-- The `v`-free exponent `P = tΛ²/4 + hℓ(s) + h²ℓ'(s)/2`. -/
def P (t : ℝ) (s : ℂ) (h : ℝ) : ℂ := t * (Λ s) ^ 2 / 4 + h * ℓ s + h ^ 2 * ℓ' s / 2

/-- The main Gaussian `e^{−A v² + i q v}`. -/
def gauss (t : ℝ) (s : ℂ) (h : ℝ) (v : ℝ) : ℂ :=
  Complex.exp (-(A t s) * (v : ℂ) ^ 2 + Complex.I * q s h * v)

/-- The pointwise defect `D(v)`. -/
def D (t : ℝ) (s : ℂ) (h : ℝ) (v : ℝ) : ℂ :=
  f t (J t s + h) (s + h + Complex.I * v) / (g s * Complex.exp (P t s h) * gauss t s h v) - 1

theorem g_ne_zero {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) : g s ≠ 0 := by
  unfold g
  have : (√(2 * π) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero hs0 hs1'))
    (Complex.exp_ne_zero _)) (by exact_mod_cast this)) (Complex.exp_ne_zero _)

/-! ## The pointwise expansion on the window -/

/-- **The integrand on the window**: for a good segment from `s` in the direction `h + iv`,
`f(s + h + iv) = g(s) e^{P} e^{−Av² + iqv} e^{E}` with `‖E‖ ≤ 402 ‖h + iv‖³/‖s‖² + 2π/(3‖s‖)`. -/
theorem f_window {t : ℝ} (ht : 0 < t) {s : ℂ} {h v : ℝ}
    (hgood : GoodSeg s (h + Complex.I * v)) (hs2 : 2 ≤ ‖s‖)
    (hζ : ‖(h : ℂ) + Complex.I * v‖ ≤ ‖s‖ / 8) :
    ∃ E : ℂ, f t (J t s + h) (s + h + Complex.I * v) =
      g s * Complex.exp (P t s h) * gauss t s h v * Complex.exp E ∧
      ‖E‖ ≤ 402 * ‖(h : ℂ) + Complex.I * v‖ ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) := by
  obtain ⟨R, hR, hRb⟩ := g_expansion hgood hs2 hζ
  obtain ⟨hslit, -, hn, -, hsec⟩ := hgood 1 (by norm_num)
  simp only [Complex.ofReal_one, one_mul] at hslit hn hsec
  have hz0 : s + ((h : ℂ) + Complex.I * v) ≠ 0 := ne_zero_of_slit hslit
  have hzeq : s + (h : ℂ) + Complex.I * v = s + ((h : ℂ) + Complex.I * v) := by ring
  refine ⟨R - μ ((s + ((h : ℂ) + Complex.I * v)) / 2), ?_, ?_⟩
  · rw [f_apply, hzeq, γ₁_eq_γ hz0, γ_eq_g hsec, hR]
    unfold gauss P A q
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hJ : s + ((h : ℂ) + Complex.I * v) - (J t s + h) = Complex.I * v - t * Λ s := by
      unfold J
      ring
    rw [hJ]
    have hε : ℓ s = Λ s / 2 + ε₁ s := by
      have := ℓ_sub_half_Λ s
      linear_combination this
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
    have key : Complex.exp ((Complex.I * v - t * Λ s) ^ 2 / (4 * t)) *
        Complex.exp (((h : ℂ) + Complex.I * v) * ℓ s + ((h : ℂ) + Complex.I * v) ^ 2 * ℓ' s / 2) =
        Complex.exp (t * Λ s ^ 2 / 4) * Complex.exp (h * ℓ s) * Complex.exp (h ^ 2 * ℓ' s / 2) *
          Complex.exp (-(1 / (4 * t) + ℓ' s / 2) * (v : ℂ) ^ 2 +
            Complex.I * (ε₁ s + h * ℓ' s) * v) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hε]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    calc Complex.exp ((Complex.I * v - t * Λ s) ^ 2 / (4 * t)) *
          (g s * (Complex.exp (((h : ℂ) + Complex.I * v) * ℓ s) *
            Complex.exp (((h : ℂ) + Complex.I * v) ^ 2 * ℓ' s / 2) * Complex.exp R) *
            Complex.exp (-μ ((s + ((h : ℂ) + Complex.I * v)) / 2)))
        = g s * (Complex.exp ((Complex.I * v - t * Λ s) ^ 2 / (4 * t)) *
            Complex.exp (((h : ℂ) + Complex.I * v) * ℓ s + ((h : ℂ) + Complex.I * v) ^ 2 * ℓ' s / 2)) *
            (Complex.exp R * Complex.exp (-μ ((s + ((h : ℂ) + Complex.I * v)) / 2))) := by
          rw [Complex.exp_add]
          ring
      _ = _ := by
          rw [key, show Complex.exp (R - μ ((s + ((h : ℂ) + Complex.I * v)) / 2)) =
            Complex.exp R * Complex.exp (-μ ((s + ((h : ℂ) + Complex.I * v)) / 2)) by
              rw [← Complex.exp_add]; congr 1 <;> ring]
          ring
  · have hμ : ‖μ ((s + ((h : ℂ) + Complex.I * v)) / 2)‖ ≤ 2 * π / (3 * ‖s‖) := by
      have h1 := norm_μ_le hsec
      have h2 : ‖(s + ((h : ℂ) + Complex.I * v)) / 2‖ = ‖s + ((h : ℂ) + Complex.I * v)‖ / 2 := by
        rw [norm_div, Complex.norm_ofNat]
      rw [h2] at h1
      refine h1.trans ?_
      have hs0 : 0 < ‖s‖ := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    calc ‖R - μ ((s + ((h : ℂ) + Complex.I * v)) / 2)‖
        ≤ ‖R‖ + ‖μ ((s + ((h : ℂ) + Complex.I * v)) / 2)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hRb hμ

/-- **The pointwise defect is small**: `‖D(v)‖ ≤ 2(ρ + m)` when `ρ + m ≤ 1`, with
`ρ = 402 ‖h + iv‖³/‖s‖²`, `m = 2π/(3‖s‖)`. -/
theorem norm_D_le {t : ℝ} (ht : 0 < t) {s : ℂ} {h v : ℝ}
    (hgood : GoodSeg s (h + Complex.I * v)) (hs2 : 2 ≤ ‖s‖)
    (hζ : ‖(h : ℂ) + Complex.I * v‖ ≤ ‖s‖ / 8)
    (hsmall : 402 * ‖(h : ℂ) + Complex.I * v‖ ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1) :
    ‖D t s h v‖ ≤ 2 * (402 * ‖(h : ℂ) + Complex.I * v‖ ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) := by
  obtain ⟨E, hE, hEb⟩ := f_window ht hgood hs2 hζ
  obtain ⟨hslit, hne1, -, -, -⟩ := hgood 0 (by simp)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hslit hne1
  have hg : g s ≠ 0 := g_ne_zero (ne_zero_of_slit hslit) hne1
  have hden : g s * Complex.exp (P t s h) * gauss t s h v ≠ 0 :=
    mul_ne_zero (mul_ne_zero hg (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  have hD : D t s h v = Complex.exp E - 1 := by
    unfold D
    rw [hE, mul_div_cancel_left₀ _ hden]
  rw [hD]
  have h1 := Complex.norm_exp_sub_one_le (hEb.trans hsmall)
  refine h1.trans ?_
  gcongr

/-! ## The exact decomposition of the event -/

/-- The window integral in terms of the Gaussian and the defect. -/
theorem window_eq {t : ℝ} {s : ℂ} (hg : g s ≠ 0) (h Y : ℝ) :
    (∫ v in (-Y)..Y, f t (J t s + h) (((s.re + h : ℝ) : ℂ) + Complex.I * ((s.im + v : ℝ) : ℂ))) =
      g s * Complex.exp (P t s h) * ∫ v in (-Y)..Y, gauss t s h v * (1 + D t s h v) := by
  rw [← intervalIntegral.integral_const_mul]
  apply integral_congr
  intro v _
  simp only
  have hz : ((s.re + h : ℝ) : ℂ) + Complex.I * ((s.im + v : ℝ) : ℂ) = s + h + Complex.I * v := by
    push_cast
    rw [show s = s.re + s.im * Complex.I from (Complex.re_add_im s).symm]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.mul_im]
    ring
  rw [hz]
  have hP : Complex.exp (P t s h) ≠ 0 := Complex.exp_ne_zero _
  have hgauss : gauss t s h v ≠ 0 := Complex.exp_ne_zero _
  unfold D
  field_simp
  ring

/-- **The exact decomposition of the `n`-th event at `J_t(s)`**: with `L = log n`, `h = 2tL`,
and the window `|v| ≤ Y` at the saddle `Re z = Re s + h`,
`∫ flowedTerm t (J s) n = e^{−tL²} e^{−J L} (4πt)^{−1/2}
   (g(s) e^{P} ∫_{−Y}^{Y} gauss (1 + D) − i(H₊ − H₋) + T)`. -/
theorem event_decomp {t : ℝ} (ht : 0 < t) {s : ℂ} (hg : g s ≠ 0) {n : ℤ} (hn : n ≠ 0) {Y : ℝ}
    (hY : 0 < Y) (hy : Y < s.im) :
    ∫ u : ℝ, flowedTerm t (J t s) n u =
      Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
        Complex.exp (-(J t s) * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) *
        (((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
          ((g s * Complex.exp (P t s (2 * t * Real.log |(n : ℝ)|)) *
              ∫ v in (-Y)..Y, gauss t s (2 * t * Real.log |(n : ℝ)|) v *
                (1 + D t s (2 * t * Real.log |(n : ℝ)|) v))
            - Complex.I *
              ((∫ x in (s.re + 2 * t * Real.log |(n : ℝ)|)..(2 : ℝ),
                  f t (J t s + 2 * t * Real.log |(n : ℝ)|) ((x : ℂ) + ((s.im + Y : ℝ) : ℂ) * Complex.I))
                - ∫ x in (s.re + 2 * t * Real.log |(n : ℝ)|)..(2 : ℝ),
                  f t (J t s + 2 * t * Real.log |(n : ℝ)|) ((x : ℂ) + ((s.im - Y : ℝ) : ℂ) * Complex.I))
            + ((∫ y : ℝ, f t (J t s + 2 * t * Real.log |(n : ℝ)|) (2 + Complex.I * y))
                - ∫ y in (s.im - Y)..(s.im + Y),
                  f t (J t s + 2 * t * Real.log |(n : ℝ)|) (2 + Complex.I * y)))) := by
  rw [integral_flowedTerm_eq_shift t (J t s) hn]
  set L : ℝ := Real.log |(n : ℝ)| with hL
  have hw : J t s + 2 * t * (L : ℂ) = J t s + ((2 * t * L : ℝ) : ℂ) := by push_cast; ring
  rw [hw, Γt_window ht (J t s + ((2 * t * L : ℝ) : ℂ)) (s.re + 2 * t * L) s.im Y hY hy]
  rw [window_eq hg]

end Soma.Holonics.RH.EventMain
