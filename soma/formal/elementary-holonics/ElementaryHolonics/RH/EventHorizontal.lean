import Mathlib
import ElementaryHolonics.RH.EventDefect

/-!
# RT3 (iii-k): the horizontal pieces and the tails, over the main term

With `ξ = X + h + 2`, `ξ₁ = 2X + 2h + 2 + t(log‖s‖ + 6)`, `Z = ξ + y + Y`, and
`M_H = e^{(ξ₁² − (Y − tπ)²)/(4t)} e^{π/4} (√(2π)/2) Z² Z^{(ξ+1)/2} (πe)^{ξ/2}`:
`‖H‖ ≤ 2 M_H ξ`, `‖T‖ ≤ β_T`, and the piece `R'` of the defect is at most
`(2 M_H ξ + β_T) (4πt)^{−1/2} / γ_low`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventHorizontal

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventTail
open Soma.Holonics.RH.EventAssembly

/-! ## The real and imaginary parts of `z − w` -/

theorem J_re (t : ℝ) (s : ℂ) : (J t s).re = s.re + t * (Λs s).re := by
  unfold J
  simp [Complex.mul_re]

theorem J_im (t : ℝ) (s : ℂ) : (J t s).im = s.im + t * (Λs s).im := by
  unfold J
  simp [Complex.mul_im]

theorem abs_Λ_im_le (s : ℂ) : |(Λs s).im| ≤ π := by
  unfold Λs
  rw [Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero]
  exact Complex.abs_arg_le_pi _

theorem abs_Λ_re_le {s : ℂ} (hs : 2 ≤ ‖s‖) : |(Λs s).re| ≤ Real.log ‖s‖ + 6 :=
  (Complex.abs_re_le_norm _).trans (norm_Λ_le hs)

theorem abs_mem_uIcc_le {a b x : ℝ} (hx : x ∈ uIcc a b) : |x| ≤ |a| + |b| := by
  rw [uIcc, mem_Icc] at hx
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h] at hx
    rw [abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  · rw [min_eq_right h, max_eq_left h] at hx
    rw [abs_le]
    constructor <;> linarith [neg_abs_le b, le_abs_self a, abs_nonneg a, abs_nonneg b]

/-! ## The supremum on a horizontal piece -/

/-- The supremum `M_H`. -/
def MH (t X h Y y ξ₁ : ℝ) : ℝ :=
  Real.exp ((ξ₁ ^ 2 - (Y - t * π) ^ 2) / (4 * t)) *
    (Real.exp (π / 4) * (√(2 * π) / 2 * (X + h + 2 + y + Y) ^ 2 *
      (X + h + 2 + y + Y) ^ ((X + h + 2 + 1) / 2) * (π * Real.exp 1) ^ ((X + h + 2) / 2)))

/-- **The pointwise bound on a horizontal piece** at height `y ± Y`. -/
theorem norm_f_horizontal_le {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs : 2 ≤ ‖s‖) {h : ℝ} (hh : 0 ≤ h) {Y : ℝ} (hYt : t * π ≤ Y) (hsec : X + h + 2 ≤ s.im - Y)
    (hy2 : 2 ≤ s.im - Y) {x' : ℝ} (hx' : x' ∈ uIcc (s.re + h) 2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖f t (J t s + h) ((x' : ℂ) + ((s.im + σ * Y : ℝ) : ℂ) * Complex.I)‖ ≤
      MH t X h Y s.im (2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6)) := by
  set z : ℂ := (x' : ℂ) + ((s.im + σ * Y : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := J t s + h with hw
  set ξ : ℝ := X + h + 2 with hξ
  set ξ₁ : ℝ := 2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6) with hξ₁
  have hY0 : 0 ≤ Y := le_trans (by positivity) hYt
  have hzre : z.re = x' := by simp [hz]
  have hzim : z.im = s.im + σ * Y := by simp [hz]
  have hx'abs : |x'| ≤ ξ := by
    have := abs_mem_uIcc_le hx'
    have h2 : |s.re + h| ≤ X + h := by
      calc |s.re + h| ≤ |s.re| + |h| := abs_add_le _ _
        _ = |s.re| + h := by rw [abs_of_nonneg hh]
        _ ≤ X + h := by linarith
    rw [hξ]
    norm_num at this
    linarith
  have hσY : |σ * Y| = Y := by
    rcases hσ with h1 | h1 <;> simp [h1, abs_of_nonneg hY0]
  have him_pos : 0 < z.im := by
    rw [hzim]
    have : -Y ≤ σ * Y := by linarith [neg_abs_le (σ * Y), hσY]
    linarith
  have him_ge : s.im - Y ≤ z.im := by
    rw [hzim]
    linarith [neg_abs_le (σ * Y), hσY]
  have him_le : z.im ≤ s.im + Y := by
    rw [hzim]
    linarith [le_abs_self (σ * Y), hσY]
  have hz2 : 2 ≤ ‖z‖ := le_trans hy2 (him_ge.trans (Complex.im_le_norm z))
  have hzZ : ‖z‖ ≤ ξ + s.im + Y := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ ξ + (s.im + Y) := by
          rw [hzre, abs_of_pos him_pos]
          gcongr
      _ = ξ + s.im + Y := by ring
  have hsecz : z / 2 ∈ Sector := by
    refine ⟨?_, Or.inr ?_⟩
    · intro h0
      have : z = 0 := by
        have h2 : z = 2 * (z / 2) := by ring
        rw [h2, h0, mul_zero]
      rw [this] at him_pos
      simp at him_pos
    · simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, abs_div, Nat.abs_ofNat]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [hzre, abs_of_pos him_pos]
      linarith
  -- the Gaussian factor
  have hre_w : w.re = s.re + t * (Λs s).re + h := by
    rw [hw, Complex.add_re, J_re, Complex.ofReal_re]
  have him_w : w.im = s.im + t * (Λs s).im := by
    rw [hw, Complex.add_im, J_im, Complex.ofReal_im, add_zero]
  have hre1 : |(z - w).re| ≤ ξ₁ := by
    rw [Complex.sub_re, hzre, hre_w]
    have h1 := abs_Λ_re_le hs
    calc |x' - (s.re + t * (Λs s).re + h)| ≤ |x'| + |s.re| + t * |(Λs s).re| + h := by
          have := abs_sub x' (s.re + t * (Λs s).re + h)
          have h2 : |s.re + t * (Λs s).re + h| ≤ |s.re| + t * |(Λs s).re| + h := by
            calc |s.re + t * (Λs s).re + h| ≤ |s.re + t * (Λs s).re| + |h| := abs_add_le _ _
              _ ≤ (|s.re| + |t * (Λs s).re|) + h := by
                  rw [abs_of_nonneg hh]
                  gcongr
                  exact abs_add_le _ _
              _ = |s.re| + t * |(Λs s).re| + h := by rw [abs_mul, abs_of_pos ht]
          linarith
      _ ≤ ξ + X + t * (Real.log ‖s‖ + 6) + h := by gcongr
      _ = ξ₁ := by rw [hξ, hξ₁]; ring
  have him1 : Y - t * π ≤ |(z - w).im| := by
    rw [Complex.sub_im, hzim, him_w]
    have h1 := abs_Λ_im_le s
    have : |s.im + σ * Y - (s.im + t * (Λs s).im)| = |σ * Y - t * (Λs s).im| := by ring_nf
    rw [this]
    have h2 := abs_sub_abs_le_abs_sub (σ * Y) (t * (Λs s).im)
    rw [hσY, abs_mul, abs_of_pos ht] at h2
    nlinarith
  have hgauss : ((z - w).re ^ 2 - (z - w).im ^ 2) / (4 * t) ≤ (ξ₁ ^ 2 - (Y - t * π) ^ 2) / (4 * t) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : (z - w).re ^ 2 ≤ ξ₁ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
    have h2 : (Y - t * π) ^ 2 ≤ (z - w).im ^ 2 := by
      rw [← sq_abs (z - w).im]
      exact pow_le_pow_left₀ (by linarith) him1 2
    linarith
  -- the Gamma factor
  have hγ : ‖γ₁ z‖ ≤ Real.exp (π / 4) * (√(2 * π) / 2 * (ξ + s.im + Y) ^ 2 *
      (ξ + s.im + Y) ^ ((ξ + 1) / 2) * (π * Real.exp 1) ^ (ξ / 2)) := by
    refine (norm_γ₁_le_g hsecz hz2).trans ?_
    gcongr
    refine (norm_g_le him_pos hz2).trans ?_
    have hZ1 : 1 ≤ ξ + s.im + Y := by linarith
    have hre_le : |z.re| ≤ ξ := by rw [hzre]; exact hx'abs
    have hπe : 1 ≤ π * Real.exp 1 := by nlinarith [Real.pi_gt_three, Real.add_one_le_exp 1]
    have e1 : ‖z‖ ^ 2 ≤ (ξ + s.im + Y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzZ 2
    have e2 : ‖z‖ ^ ((|z.re| + 1) / 2) ≤ (ξ + s.im + Y) ^ ((ξ + 1) / 2) :=
      (Real.rpow_le_rpow (norm_nonneg _) hzZ (by positivity)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith))
    have e3 : (π * Real.exp 1) ^ (|z.re| / 2) ≤ (π * Real.exp 1) ^ (ξ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hπe (by linarith)
    have hZ0 : 0 ≤ ξ + s.im + Y := by linarith
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) e2
      (by positivity) (by positivity)) e3 (by positivity) (by positivity)
  rw [norm_f_eq]
  unfold MH
  have : X + h + 2 + s.im + Y = ξ + s.im + Y := by rw [hξ]
  rw [this, show X + h + 2 + 1 = ξ + 1 by rw [hξ], show X + h + 2 = ξ by rw [hξ]]
  gcongr

/-! ## The pieces of `R'` -/

/-- **The horizontal pieces**: `‖H‖ ≤ 2 M_H (X + h + 2)`. -/
theorem norm_Hpiece_le {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs : 2 ≤ ‖s‖) {h : ℝ} (hh : 0 ≤ h) {Y : ℝ} (hYt : t * π ≤ Y) (hsec : X + h + 2 ≤ s.im - Y)
    (hy2 : 2 ≤ s.im - Y) :
    ‖Hpiece t s h Y‖ ≤
      2 * MH t X h Y s.im (2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6)) * (X + h + 2) := by
  set M := MH t X h Y s.im (2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6)) with hM
  have hY0 : 0 ≤ Y := le_trans (by positivity) hYt
  have hZ0 : 0 ≤ X + h + 2 + s.im + Y := by linarith
  have hM0 : 0 ≤ M := by
    rw [hM]
    unfold MH
    apply mul_nonneg (Real.exp_pos _).le
    apply mul_nonneg (Real.exp_pos _).le
    apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (Real.rpow_nonneg hZ0 _)) (Real.rpow_nonneg (by positivity) _)
  have hlen : |2 - (s.re + h)| ≤ X + h + 2 := by
    calc |2 - (s.re + h)| ≤ |(2 : ℝ)| + |s.re + h| := abs_sub _ _
      _ ≤ 2 + (|s.re| + |h|) := by
          rw [abs_two]
          gcongr
          exact abs_add_le _ _
      _ ≤ 2 + (X + h) := by
          rw [abs_of_nonneg hh]
          gcongr
      _ = X + h + 2 := by ring
  have hplus : ‖∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im + Y : ℝ) : ℂ) * Complex.I)‖ ≤
      M * |2 - (s.re + h)| := by
    apply norm_horizontal_le
    intro x hx
    have := norm_f_horizontal_le ht hX0 hX hs hh hYt hsec hy2 hx (σ := 1) (Or.inl rfl)
    simpa using this
  have hminus : ‖∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im - Y : ℝ) : ℂ) * Complex.I)‖ ≤
      M * |2 - (s.re + h)| := by
    apply norm_horizontal_le
    intro x hx
    have := norm_f_horizontal_le ht hX0 hX hs hh hYt hsec hy2 hx (σ := -1) (Or.inr rfl)
    rw [show s.im + (-1) * Y = s.im - Y by ring] at this
    exact this
  unfold Hpiece
  calc ‖(∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im + Y : ℝ) : ℂ) * Complex.I)) -
        ∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im - Y : ℝ) : ℂ) * Complex.I)‖
      ≤ M * |2 - (s.re + h)| + M * |2 - (s.re + h)| :=
        (norm_sub_le _ _).trans (add_le_add hplus hminus)
    _ ≤ M * (X + h + 2) + M * (X + h + 2) := by gcongr
    _ = 2 * M * (X + h + 2) := by ring

/-- **The tails**: `‖T‖ ≤ β_T`. -/
theorem norm_Tpiece_le {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs : 2 ≤ ‖s‖) {h : ℝ} (hh : 0 ≤ h) {Y : ℝ} (hY2 : 2 * t * π ≤ Y) :
    ‖Tpiece t s h Y‖ ≤
      2 * (Real.exp ((2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 / (4 * t)) / (2 * π)) *
        (1 + |s.im| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t))) := by
  set w : ℂ := J t s + h with hw
  have him_w : |w.im - s.im| ≤ t * π := by
    rw [hw, Complex.add_im, J_im, Complex.ofReal_im, add_zero]
    rw [show s.im + t * (Λs s).im - s.im = t * (Λs s).im by ring, abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (abs_Λ_im_le s) ht.le
  have hre_w : |2 - w.re| ≤ 2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6) := by
    rw [hw, Complex.add_re, J_re, Complex.ofReal_re]
    have h1 := abs_Λ_re_le hs
    calc |2 - (s.re + t * (Λs s).re + h)| ≤ |(2 : ℝ)| + |s.re + t * (Λs s).re + h| := abs_sub _ _
      _ ≤ 2 + (|s.re| + t * |(Λs s).re| + h) := by
          rw [abs_two]
          gcongr
          calc |s.re + t * (Λs s).re + h| ≤ |s.re + t * (Λs s).re| + |h| := abs_add_le _ _
            _ ≤ (|s.re| + |t * (Λs s).re|) + h := by
                rw [abs_of_nonneg hh]
                gcongr
                exact abs_add_le _ _
            _ = |s.re| + t * |(Λs s).re| + h := by rw [abs_mul, abs_of_pos ht]
      _ ≤ 2 + (X + t * (Real.log ‖s‖ + 6) + h) := by gcongr
      _ ≤ 2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6) := by linarith
  have htail := norm_tail_le ht w hY2 him_w
  have hexp : Real.exp ((2 - w.re) ^ 2 / (4 * t)) ≤
      Real.exp ((2 * X + 2 * h + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← sq_abs (2 - w.re)]
    exact pow_le_pow_left₀ (abs_nonneg _) hre_w 2
  unfold Tpiece
  refine htail.trans ?_
  gcongr

/-- The lower bound of the main term, `γ_low`. -/
def γlow (t X : ℝ) (s : ℂ) : ℝ :=
  cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) * Real.exp (-(t * π ^ 2 / 4))

theorem γlow_pos {t X : ℝ} {s : ℂ} (hs : 0 < ‖s‖) : 0 < γlow t X s := by
  unfold γlow
  have := cg_pos X
  have := Real.rpow_pos_of_pos hs (-((X + 1) / 2))
  positivity

/-- **The piece `R'` of the defect.** -/
theorem norm_Rpiece_le {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    (hs2π : 2 * π ≤ ‖s‖) {L : ℝ} (hL : 0 ≤ L) {Y : ℝ} (hY2 : 2 * t * π ≤ Y)
    (hsec : X + 2 * t * L + 2 ≤ s.im - Y) (hy2 : 2 ≤ s.im - Y) :
    ‖Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s‖ ≤
      (2 * MH t X (2 * t * L) Y s.im (2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) *
          (X + 2 * t * L + 2) +
        2 * (Real.exp ((2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 / (4 * t)) /
          (2 * π)) * (1 + |s.im| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t)))) *
        (√(4 * π * t))⁻¹ / γlow t X s := by
  have hs : 2 ≤ ‖s‖ := by linarith [Real.pi_gt_three]
  have hs0 : 0 < ‖s‖ := by linarith
  have hh : 0 ≤ 2 * t * L := by positivity
  have hYt : t * π ≤ Y := by nlinarith [Real.pi_pos]
  have hH := norm_Hpiece_le ht hX0 hX hs hh hYt hsec hy2
  have hT := norm_Tpiece_le ht hX0 hX hs hh hY2
  have hc := norm_exp_neg_tΛ_le hs2π ht.le hL
  have hγ := norm_γt'_ge ht.le hX0 hX hs
  have hγlow : 0 < γlow t X s := γlow_pos hs0
  have hσ : ‖((√(4 * π * t) : ℝ) : ℂ)⁻¹‖ = (√(4 * π * t))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  have hHT : ‖-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y‖ ≤
      ‖Hpiece t s (2 * t * L) Y‖ + ‖Tpiece t s (2 * t * L) Y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [norm_div, norm_mul, norm_mul, hσ]
  have hγn : γlow t X s ≤ ‖γt' t s‖ := hγ
  calc ‖Complex.exp (-(t : ℂ) * Λs s * L)‖ * (√(4 * π * t))⁻¹ *
        ‖-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y‖ / ‖γt' t s‖
      ≤ 1 * (√(4 * π * t))⁻¹ *
        (‖Hpiece t s (2 * t * L) Y‖ + ‖Tpiece t s (2 * t * L) Y‖) / γlow t X s := by
        gcongr
    _ ≤ 1 * (√(4 * π * t))⁻¹ *
        ((2 * MH t X (2 * t * L) Y s.im (2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) *
            (X + 2 * t * L + 2)) +
          (2 * (Real.exp ((2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 / (4 * t)) /
            (2 * π)) * (1 + |s.im| + 4 * √t) * √(64 * π * t) * Real.exp (-(Y ^ 2 / (64 * t))))) /
        γlow t X s := by
        gcongr
    _ = _ := by ring

end Soma.Holonics.RH.EventHorizontal
