import Mathlib
import ElementaryHolonics.RH.EventTail

/-!
# RT3 (iii-i): the event as its main term times `1 + r`

With `F₁ = e^{2tLε₁(s) + 2t²L²ℓ'(s)}`, `G₀ = (4πt)^{−1/2} G`, `I_W = ∫_{−Y}^{Y} gauss (1 + D)`, and
`R' = e^{−tΛL} (4πt)^{−1/2} (−i(H₊ − H₋) + T)/γ_t(s)`, the event is exactly

`∫ flowedTerm t (J s) n = γ_t(s) e^{−sL} e^{−tL²} (1 + r)`,  `r = F₁ G₀ (I_W/G) − 1 + R'`.

This file returns the identity, the general pointwise bound on `f`, and the supremum on a
horizontal piece.
-/

noncomputable section

namespace Soma.Holonics.RH.EventAssembly

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.FlowedGammaContour
open Soma.Holonics.RH.EventSaddle
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventWindow
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventTail

/-! ## The pointwise bound on `f` -/

theorem norm_f_eq {t : ℝ} (w z : ℂ) :
    ‖f t w z‖ = Real.exp (((z - w).re ^ 2 - (z - w).im ^ 2) / (4 * t)) * ‖γ₁ z‖ := by
  rw [f_apply, norm_mul, Complex.norm_exp]
  congr 2
  have h4 : (4 * (t : ℂ)) = ((4 * t : ℝ) : ℂ) := by push_cast; ring
  rw [h4, Complex.div_ofReal_re]
  simp [sq, Complex.mul_re]

/-! ## The identity -/

/-- `F₁ = e^{2tLε₁ + 2t²L²ℓ'}`. -/
def F₁ (t : ℝ) (s : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (2 * t * L * ε₁ s + 2 * t ^ 2 * L ^ 2 * ℓ' s)

/-- The window integral `I_W = ∫_{−Y}^{Y} gauss (1 + D)`. -/
def IW (t : ℝ) (s : ℂ) (h Y : ℝ) : ℂ := ∫ v in (-Y)..Y, gauss t s h v * (1 + D t s h v)

/-- The two horizontal pieces and the tails, for the event `w = J + h`. -/
def Hpiece (t : ℝ) (s : ℂ) (h Y : ℝ) : ℂ :=
  (∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im + Y : ℝ) : ℂ) * Complex.I)) -
    ∫ x in (s.re + h)..(2 : ℝ), f t (J t s + h) ((x : ℂ) + ((s.im - Y : ℝ) : ℂ) * Complex.I)

def Tpiece (t : ℝ) (s : ℂ) (h Y : ℝ) : ℂ :=
  (∫ y : ℝ, f t (J t s + h) (2 + Complex.I * y)) -
    ∫ y in (s.im - Y)..(s.im + Y), f t (J t s + h) (2 + Complex.I * y)

/-- The relative defect `r`. -/
def rdef (t : ℝ) (s : ℂ) (L Y : ℝ) : ℂ :=
  F₁ t s L * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)) *
      (IW t s (2 * t * L) Y / G t s (2 * t * L)) - 1 +
    Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hpiece t s (2 * t * L) Y + Tpiece t s (2 * t * L) Y) / γt' t s

theorem F₁_mul (t : ℝ) (s : ℂ) (L : ℝ) :
    Complex.exp (-(t : ℂ) * Λs s * L) * Complex.exp (P t s (2 * t * L)) =
      F₁ t s L * Complex.exp (t * (Λs s) ^ 2 / 4) := by
  unfold F₁ P
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have := ℓ_sub_half_Λ s
  have hℓ : ℓ s = Λs s / 2 + ε₁ s := by linear_combination this
  rw [hℓ]
  push_cast
  ring

/-- **The event as its main term times `1 + r`.** -/
theorem event_eq_main_mul {t : ℝ} (ht : 0 < t) {s : ℂ} (hg : g s ≠ 0) (hs : 2 ≤ ‖s‖)
    (hst : 12 * t ≤ ‖s‖) {n : ℤ} (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) (hy : Y < s.im) :
    ∫ u : ℝ, flowedTerm t (J t s) n u =
      γt' t s * Complex.exp (-s * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) *
        Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
        (1 + rdef t s (Real.log |(n : ℝ)|) Y) := by
  rw [event_decomp ht hg hn hY hy]
  set L : ℝ := Real.log |(n : ℝ)| with hL
  have hG : G t s (2 * t * L) ≠ 0 := by
    intro h0
    have := norm_G_ge ht hs hst (2 * t * L)
    rw [h0, norm_zero] at this
    have : 0 < √(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2)) := by positivity
    linarith
  have hγ : γt' t s ≠ 0 := by
    unfold γt'
    exact mul_ne_zero hg (Complex.exp_ne_zero _)
  have hsq : ((√(4 * π * t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * π * t)).ne'
  have hJ : Complex.exp (-(J t s) * (L : ℂ)) =
      Complex.exp (-s * (L : ℂ)) * Complex.exp (-(t : ℂ) * Λs s * L) := by
    rw [← Complex.exp_add]
    congr 1
    unfold J
    ring
  have hF := F₁_mul t s L
  have hγ' : γt' t s = g s * Complex.exp (t * (Λs s) ^ 2 / 4) := rfl
  rw [hJ]
  unfold rdef IW Hpiece Tpiece
  push_cast
  set W : ℂ := ∫ v in (-Y)..Y, gauss t s (2 * t * L) v * (1 + D t s (2 * t * L) v) with hW
  set Hp : ℂ := (∫ x in (s.re + 2 * t * L)..(2 : ℝ),
      f t (J t s + 2 * (t : ℂ) * (L : ℂ)) ((x : ℂ) + ((s.im : ℂ) + (Y : ℂ)) * Complex.I)) -
      ∫ x in (s.re + 2 * t * L)..(2 : ℝ),
      f t (J t s + 2 * (t : ℂ) * (L : ℂ)) ((x : ℂ) + ((s.im : ℂ) - (Y : ℂ)) * Complex.I) with hHp
  set Tp : ℂ := (∫ y : ℝ, f t (J t s + 2 * (t : ℂ) * (L : ℂ)) (2 + Complex.I * y)) -
      ∫ y in (s.im - Y)..(s.im + Y), f t (J t s + 2 * (t : ℂ) * (L : ℂ)) (2 + Complex.I * y) with hTp
  have k1 : W / G t s (2 * t * L) * G t s (2 * t * L) = W := div_mul_cancel₀ _ hG
  have k2 : (Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      (-Complex.I * Hp + Tp)) / γt' t s * γt' t s =
      Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * (-Complex.I * Hp + Tp) :=
    div_mul_cancel₀ _ hγ
  set X : ℂ := Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
    (-Complex.I * Hp + Tp) with hX
  have e1 : γt' t s * (X / γt' t s) = X := by
    rw [mul_comm]
    exact k2
  have e2 : γt' t s * (F₁ t s L * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)) *
      (W / G t s (2 * t * L))) =
      Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
        (g s * Complex.exp (P t s (2 * t * L)) * W) := by
    calc γt' t s * (F₁ t s L * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)) *
          (W / G t s (2 * t * L)))
        = g s * Complex.exp (t * (Λs s) ^ 2 / 4) * F₁ t s L * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
            (W / G t s (2 * t * L) * G t s (2 * t * L)) := by
          rw [hγ']
          ring
      _ = g s * (F₁ t s L * Complex.exp (t * (Λs s) ^ 2 / 4)) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * W := by
          rw [k1]
          ring
      _ = g s * (Complex.exp (-(t : ℂ) * Λs s * L) * Complex.exp (P t s (2 * t * L))) *
            ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * W := by
          rw [← hF]
      _ = _ := by ring
  calc Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2) *
        (Complex.exp (-s * (L : ℂ)) * Complex.exp (-(t : ℂ) * Λs s * L)) *
        (((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
          (g s * Complex.exp (P t s (2 * t * L)) * W - Complex.I * Hp + Tp))
      = Complex.exp (-s * (L : ℂ)) * Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2) *
          (Complex.exp (-(t : ℂ) * Λs s * L) * ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
            (g s * Complex.exp (P t s (2 * t * L)) * W) + X) := by
        rw [hX]
        ring
    _ = Complex.exp (-s * (L : ℂ)) * Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2) *
          (γt' t s * (F₁ t s L * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)) *
            (W / G t s (2 * t * L))) + γt' t s * (X / γt' t s)) := by
        rw [e1, e2]
    _ = γt' t s * Complex.exp (-s * (L : ℂ)) * Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2) *
          (1 + (F₁ t s L * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * G t s (2 * t * L)) *
            (W / G t s (2 * t * L)) - 1 + X / γt' t s)) := by ring

end Soma.Holonics.RH.EventAssembly
