import Mathlib
import ElementaryHolonics.RH.EventExplicit

/-!
# RT3 (iii-m): the majorant in `u = (Im s)^{1/3}`

With `y = Im s = u³`, `Y = u²/20`, `L ≤ u`, and `|Re s| ≤ X ≤ u³`, every piece of the explicit
defect bound is majorized by a function of `u` alone: `Bmaj t X u`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventMainRange

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventHorizontal
open Soma.Holonics.RH.EventAssembly
open Soma.Holonics.RH.EventExplicit

/-! ## The parameter constants -/

/-- `ξ ≤ cξ u`. -/
def cξ (t X : ℝ) : ℝ := X + 2 * t + 2
/-- `ξ₁ ≤ c₁ u`. -/
def c₁ (t X : ℝ) : ℝ := 2 * X + 2 + 14 * t
/-- `Z ≤ cZ u³`. -/
def cZ (t X : ℝ) : ℝ := cξ t X + 2

/-! ## Elementary majorizations -/

theorem log_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ u := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < u)]

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem norm_s_le {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) {u : ℝ} (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3)
    (hu : 0 ≤ u) : ‖s‖ ≤ 2 * u ^ 3 := by
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ X + u ^ 3 := by
        rw [hy, abs_of_nonneg (pow_nonneg hu 3)]
        exact add_le_add hX le_rfl
    _ ≤ 2 * u ^ 3 := by linarith

theorem norm_s_ge {s : ℂ} {u : ℝ} (hy : s.im = u ^ 3) (hu : 0 ≤ u) : u ^ 3 ≤ ‖s‖ := by
  calc u ^ 3 = s.im := hy.symm
    _ ≤ ‖s‖ := Complex.im_le_norm s

theorem log_norm_s_le {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) {u : ℝ} (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3)
    (hu : 1 ≤ u) : Real.log ‖s‖ ≤ 1 + 3 * u := by
  have h1 := norm_s_le hX hy hXu (by linarith)
  have hs0 : 0 < ‖s‖ := by
    have := norm_s_ge hy (by linarith)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < u) 3]
  calc Real.log ‖s‖ ≤ Real.log (2 * u ^ 3) := Real.log_le_log hs0 h1
    _ = Real.log 2 + 3 * Real.log u := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
    _ ≤ 1 + 3 * u := by
        have := log_le_self_of_one_le hu
        linarith [log_two_le_one]

theorem ξ_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {L u : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u) (hu : 1 ≤ u) :
    X + 2 * t * L + 2 ≤ cξ t X * u := by
  unfold cξ
  nlinarith

theorem ξ₁_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {s : ℂ} (hXs : |s.re| ≤ X) {L u : ℝ} (hL : 0 ≤ L)
    (hLu : L ≤ u) (hu : 1 ≤ u) (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3) :
    2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6) ≤ c₁ t X * u := by
  unfold c₁
  have h1 := log_norm_s_le hXs hy hXu hu
  have e1 : t * L ≤ t * u := mul_le_mul_of_nonneg_left hLu ht
  have e2 : t * Real.log ‖s‖ ≤ t * (1 + 3 * u) := mul_le_mul_of_nonneg_left h1 ht
  have e3 : 0 ≤ X * (u - 1) := mul_nonneg hX (sub_nonneg.mpr hu)
  have e4 : 0 ≤ t * (u - 1) := mul_nonneg ht (sub_nonneg.mpr hu)
  nlinarith [e1, e2, e3, e4]

theorem Z_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {L u : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u) (hu : 1 ≤ u) :
    X + 2 * t * L + 2 + u ^ 3 + u ^ 2 / 20 ≤ cZ t X * u ^ 3 := by
  unfold cZ
  have h1 := ξ_le ht hX hL hLu hu
  have hu0 : 0 ≤ u := by linarith
  have h2 : u ≤ u ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hu)) (by linarith : 0 ≤ u + 1)]
  have h3 : u ^ 2 / 20 ≤ u ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hu0 2) (sub_nonneg.mpr hu)]
  have hcξ : 0 ≤ cξ t X := by unfold cξ; linarith
  have h4 := mul_le_mul_of_nonneg_left h2 hcξ
  linarith

/-! ## The majorants of the four pieces -/

/-- `c₃ = 3/(32t)`, the Gaussian decay rate of the window estimates. -/
def c₃ (t : ℝ) : ℝ := 3 / (32 * t)
def I₀ (t : ℝ) : ℝ := √(π / c₃ t)
def I₃ (t : ℝ) : ℝ := 7 * (c₃ t) ^ (-(3 / 2 : ℝ)) * √(π / (3 * c₃ t / 4))

def Amaj (t u : ℝ) : ℝ := (12 * t + 12 * t ^ 2) / u
def Bmaj' (t u : ℝ) : ℝ := (36 * t + 4 * t * (3 + 6 * t) ^ 2) / u
def β₃maj (t u : ℝ) : ℝ :=
  2 * Real.exp (8 * t) * ((12864 * t ^ 3 + 2 * π / 3) * I₀ t + 1608 * I₃ t) / u
def β₄maj (t u : ℝ) : ℝ :=
  2 * Real.exp (8 * t) * √(2 * π / c₃ t) * Real.exp (-(c₃ t / 2) * (u ^ 2 / 20) ^ 2)
def Dmaj (t u : ℝ) : ℝ := Real.exp 1 / √(2 * π * t) * (β₃maj t u + β₄maj t u)
def Mmaj (t X u : ℝ) : ℝ :=
  Real.exp ((c₁ t X ^ 2 * u ^ 2 - u ^ 4 / 1600) / (4 * t)) *
    (Real.exp (π / 4) * (√(2 * π) / 2 * (cZ t X * u ^ 3) ^ 2 *
      (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) * (π * Real.exp 1) ^ (cξ t X * u / 2)))
def Tmaj (t X u : ℝ) : ℝ :=
  2 * (Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) / (2 * π)) * (1 + u ^ 3 + 4 * √t) *
    √(64 * π * t) * Real.exp (-(u ^ 4 / (25600 * t)))
def Γmaj (t X u : ℝ) : ℝ :=
  (1 / cg X) * (2 * u ^ 3) ^ ((X + 1) / 2) * Real.exp (π * u ^ 3) * Real.exp (t * π ^ 2 / 4)
def Emaj (t X u : ℝ) : ℝ :=
  (2 * Mmaj t X u * (cξ t X * u) + Tmaj t X u) * (√(4 * π * t))⁻¹ * Γmaj t X u
/-- The majorant of the relative defect. -/
def Bmaj (t X u : ℝ) : ℝ :=
  (Amaj t u * (1 + Bmaj' t u) + Bmaj' t u) * (1 + Dmaj t u) + Dmaj t u + Emaj t X u

theorem norm_q_le_u {t : ℝ} (ht : 0 < t) {s : ℂ} (hs2 : 2 ≤ ‖s‖) {u L : ℝ} (hu : 1 ≤ u)
    (hy : s.im = u ^ 3) (hL : 0 ≤ L) (hLu : L ≤ u) : ‖q s (2 * t * L)‖ ≤ (3 + 6 * t) / u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hsu := norm_s_ge hy hu0.le
  refine (norm_q_le hs2 (by positivity)).trans ?_
  have h1 : 3 + 3 * (2 * t * L) ≤ (3 + 6 * t) * u := by nlinarith [mul_le_mul_of_nonneg_left hLu ht.le]
  calc (3 + 3 * (2 * t * L)) / ‖s‖ ≤ ((3 + 6 * t) * u) / u ^ 3 := by gcongr
    _ = (3 + 6 * t) / u ^ 2 := by
        field_simp
        first | done | ring

theorem u_le_cube {u : ℝ} (hu : 1 ≤ u) : u ≤ u ^ 3 := by
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ u) (sub_nonneg.mpr hu))
    (by linarith : (0 : ℝ) ≤ u + 1)]

theorem I₀_nonneg (t : ℝ) : 0 ≤ I₀ t := Real.sqrt_nonneg _
theorem I₃_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ I₃ t := by
  unfold I₃
  have := Real.rpow_nonneg (by unfold c₃; positivity : (0 : ℝ) ≤ c₃ t) (-(3 / 2 : ℝ))
  positivity
theorem Dmaj_nonneg {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Dmaj t u := by
  unfold Dmaj β₃maj β₄maj
  have := I₀_nonneg t; have := I₃_nonneg ht
  positivity

theorem a_le_Amaj {t : ℝ} (ht : 0 < t) {s : ℂ} {u L : ℝ} (hu : 1 ≤ u) (hsu : u ^ 3 ≤ ‖s‖)
    (hL : 0 ≤ L) (hLu : L ≤ u) : 2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) ≤ Amaj t u := by
  have hu0 : 0 < u := by linarith
  unfold Amaj
  have h1 : 6 * t * L + 6 * t ^ 2 * L ^ 2 ≤ (6 * t + 6 * t ^ 2) * u ^ 2 := by
    have e1 : t * L ≤ t * u := mul_le_mul_of_nonneg_left hLu ht.le
    have e2 : L ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hL hLu 2
    nlinarith [mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 6 * t ^ 2),
      mul_nonneg ht.le (sub_nonneg.mpr hu), mul_nonneg ht.le hu0.le]
  calc 2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) ≤ 2 * (((6 * t + 6 * t ^ 2) * u ^ 2) / u ^ 3) := by
        gcongr
    _ = (12 * t + 12 * t ^ 2) / u := by
        field_simp
        first | done | ring

theorem b_le_Bmaj' {t : ℝ} (ht : 0 < t) {s : ℂ} {u L : ℝ} (hu : 1 ≤ u) (hsu : u ^ 3 ≤ ‖s‖)
    (hqu : ‖q s (2 * t * L)‖ ≤ (3 + 6 * t) / u ^ 2) :
    36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ Bmaj' t u := by
  have hu0 : 0 < u := by linarith
  unfold Bmaj'
  have h1 : 36 * t / ‖s‖ ≤ 36 * t / u := by
    apply div_le_div_of_nonneg_left (by positivity) hu0
    linarith [u_le_cube hu]
  have h2 : ‖q s (2 * t * L)‖ ^ 2 ≤ (3 + 6 * t) ^ 2 / u := by
    calc ‖q s (2 * t * L)‖ ^ 2 ≤ ((3 + 6 * t) / u ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hqu 2
      _ = (3 + 6 * t) ^ 2 / u ^ 4 := by ring
      _ ≤ (3 + 6 * t) ^ 2 / u := by
          apply div_le_div_of_nonneg_left (by positivity) hu0
          nlinarith [u_le_cube hu, mul_le_mul_of_nonneg_left (u_le_cube hu) hu0.le]
  calc 36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 36 * t / u + 4 * t * ((3 + 6 * t) ^ 2 / u) := by
        gcongr
    _ = (36 * t + 4 * t * (3 + 6 * t) ^ 2) / u := by ring

theorem β₃_le_β₃maj {t : ℝ} (ht : 0 < t) {s : ℂ} {u L : ℝ} (hu : 1 ≤ u) (hsu : u ^ 3 ≤ ‖s‖)
    (hL : 0 ≤ L) (hLu : L ≤ u) : β₃ t s (2 * t * L) ≤ β₃maj t u := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < ‖s‖ := by nlinarith [pow_pos hu0 3]
  unfold β₃ β₃maj
  have hI₀ := I₀_nonneg t
  have hI₃ := I₃_nonneg ht
  have e1 : 1608 * (2 * t * L) ^ 3 / ‖s‖ ^ 2 ≤ 12864 * t ^ 3 / u := by
    have : (2 * t * L) ^ 3 ≤ 8 * t ^ 3 * u ^ 3 := by
      have := pow_le_pow_left₀ hL hLu 3
      nlinarith [pow_nonneg ht.le 3]
    calc 1608 * (2 * t * L) ^ 3 / ‖s‖ ^ 2 ≤ 1608 * (8 * t ^ 3 * u ^ 3) / (u ^ 3) ^ 2 := by
          gcongr
      _ = 12864 * t ^ 3 / u ^ 3 := by
          field_simp
          first | done | ring
      _ ≤ 12864 * t ^ 3 / u := by
          apply div_le_div_of_nonneg_left (by positivity) hu0
          linarith [u_le_cube hu]
  have e2 : 2 * π / (3 * ‖s‖) ≤ (2 * π / 3) / u := by
    have : (2 * π / 3) / u = 2 * π / (3 * u) := by
      field_simp
    rw [this]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [u_le_cube hu]
  have e3 : 1608 / ‖s‖ ^ 2 ≤ 1608 / u := by
    apply div_le_div_of_nonneg_left (by norm_num) hu0
    have hs1 : 1 ≤ ‖s‖ := by linarith [u_le_cube hu]
    nlinarith [u_le_cube hu, mul_le_mul_of_nonneg_left hs1 (by linarith : (0 : ℝ) ≤ ‖s‖)]
  have hI₀' : √(π / (3 / (32 * t))) = I₀ t := rfl
  have hI₃' : 7 * (3 / (32 * t)) ^ (-(3 / 2 : ℝ)) * √(π / (3 * (3 / (32 * t)) / 4)) = I₃ t := rfl
  rw [hI₀', hI₃']
  calc 2 * Real.exp (8 * t) * ((1608 * (2 * t * L) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖)) * I₀ t +
        1608 / ‖s‖ ^ 2 * I₃ t)
      ≤ 2 * Real.exp (8 * t) * ((12864 * t ^ 3 / u + (2 * π / 3) / u) * I₀ t + 1608 / u * I₃ t) := by
        gcongr
    _ = 2 * Real.exp (8 * t) * ((12864 * t ^ 3 + 2 * π / 3) * I₀ t + 1608 * I₃ t) / u := by
        field_simp
        first | done | ring

theorem d_le_Dmaj {t : ℝ} (ht : 0 < t) {s : ℂ} {u L : ℝ} (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hq2 : 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1) (hβ₃ : β₃ t s (2 * t * L) ≤ β₃maj t u) :
    (β₃ t s (2 * t * L) + β₄ t (u ^ 2 / 20)) /
      (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2))) ≤ Dmaj t u := by
  unfold Dmaj
  have hI₀ := I₀_nonneg t
  have hI₃ := I₃_nonneg ht
  have hβ₄ : β₄ t (u ^ 2 / 20) = β₄maj t u := rfl
  have hβ₃0 : 0 ≤ β₃ t s (2 * t * L) := by unfold β₃; positivity
  have hβ₄0 : 0 ≤ β₄ t (u ^ 2 / 20) := by unfold β₄; positivity
  have hm0 : 0 ≤ β₃maj t u + β₄maj t u := by unfold β₃maj β₄maj; positivity
  have hden : √(2 * π * t) * Real.exp (-1) ≤
      √(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.exp_le_exp.mpr (by linarith)
  have hden0 : 0 < √(2 * π * t) * Real.exp (-1) := by positivity
  calc (β₃ t s (2 * t * L) + β₄ t (u ^ 2 / 20)) /
        (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2)))
      ≤ (β₃maj t u + β₄maj t u) / (√(2 * π * t) * Real.exp (-1)) := by
        apply div_le_div₀ hm0 _ hden0 hden
        rw [hβ₄]
        exact add_le_add hβ₃ le_rfl
    _ = Real.exp 1 / √(2 * π * t) * (β₃maj t u + β₄maj t u) := by
        rw [Real.exp_neg]
        field_simp

theorem Mmaj_nonneg {t X u : ℝ} (hcZ : 0 ≤ cZ t X * u ^ 3) : 0 ≤ Mmaj t X u := by
  unfold Mmaj
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (Real.rpow_nonneg hcZ _)) (Real.rpow_nonneg (by positivity) _)

theorem MH_nonneg {t X h Y y ξ₁ : ℝ} (hZ : 0 ≤ X + h + 2 + y + Y) : 0 ≤ MH t X h Y y ξ₁ := by
  unfold MH
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (Real.rpow_nonneg hZ _)) (Real.rpow_nonneg (by positivity) _)

theorem MH_le_Mmaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u L ξ₁ : ℝ} (hu : 1 ≤ u)
    (hL : 0 ≤ L) (hLu : L ≤ u) (hξ₁0 : 0 ≤ ξ₁) (hξ₁ : ξ₁ ≤ c₁ t X * u)
    (hY2 : 2 * t * π ≤ u ^ 2 / 20) :
    MH t X (2 * t * L) (u ^ 2 / 20) (u ^ 3) ξ₁ ≤ Mmaj t X u := by
  have hu0 : 0 < u := by linarith
  have hZ := Z_le ht.le hX0 hL hLu hu
  have hξ := ξ_le ht.le hX0 hL hLu hu
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hZ0 : 0 ≤ X + 2 * t * L + 2 + u ^ 3 + u ^ 2 / 20 := by positivity
  have hcZ1 : 1 ≤ cZ t X * u ^ 3 := by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    unfold cZ
    nlinarith
  unfold MH Mmaj
  have hexp : ξ₁ ^ 2 - (u ^ 2 / 20 - t * π) ^ 2 ≤ c₁ t X ^ 2 * u ^ 2 - u ^ 4 / 1600 := by
    have e1 : ξ₁ ^ 2 ≤ (c₁ t X * u) ^ 2 := pow_le_pow_left₀ hξ₁0 hξ₁ 2
    have e2 : (u ^ 2 / 40) ^ 2 ≤ (u ^ 2 / 20 - t * π) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.pi_pos]
    nlinarith
  have hπe : 1 ≤ π * Real.exp 1 := by nlinarith [Real.pi_gt_three, Real.add_one_le_exp 1]
  have e3 : (X + 2 * t * L + 2 + u ^ 3 + u ^ 2 / 20) ^ ((X + 2 * t * L + 2 + 1) / 2) ≤
      (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) :=
    (Real.rpow_le_rpow hZ0 hZ (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hcZ1 (by linarith))
  have e4 : (π * Real.exp 1) ^ ((X + 2 * t * L + 2) / 2) ≤ (π * Real.exp 1) ^ (cξ t X * u / 2) :=
    Real.rpow_le_rpow_of_exponent_le hπe (by linarith)
  have e5 : (X + 2 * t * L + 2 + u ^ 3 + u ^ 2 / 20) ^ 2 ≤ (cZ t X * u ^ 3) ^ 2 :=
    pow_le_pow_left₀ hZ0 hZ 2
  apply mul_le_mul (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hexp (by positivity)))
    _ (by positivity) (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e5 (by positivity)) e3
    (by positivity) (by positivity)) e4 (by positivity) (by positivity)

theorem T_le_Tmaj {t X : ℝ} (ht : 0 < t) {u ξ₁ : ℝ} (hu : 1 ≤ u)
    (hξ₁0 : 0 ≤ ξ₁) (hξ₁ : ξ₁ ≤ c₁ t X * u) :
    2 * (Real.exp (ξ₁ ^ 2 / (4 * t)) / (2 * π)) * (1 + |u ^ 3| + 4 * √t) * √(64 * π * t) *
      Real.exp (-((u ^ 2 / 20) ^ 2 / (64 * t))) ≤ Tmaj t X u := by
  have hu0 : 0 < u := by linarith
  unfold Tmaj
  rw [abs_of_nonneg (by positivity)]
  have e1 : Real.exp (ξ₁ ^ 2 / (4 * t)) ≤ Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := pow_le_pow_left₀ hξ₁0 hξ₁ 2
    nlinarith
  have e2 : Real.exp (-((u ^ 2 / 20) ^ 2 / (64 * t))) = Real.exp (-(u ^ 4 / (25600 * t))) := by
    congr 1
    field_simp
    first | done | ring
  rw [e2]
  gcongr

theorem inv_γlow_le_Γmaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {s : ℂ} {u : ℝ} (hu : 1 ≤ u)
    (hs1 : 1 ≤ ‖s‖) (hs2u : ‖s‖ ≤ 2 * u ^ 3) : 1 / γlow t X s ≤ Γmaj t X u := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  unfold γlow Γmaj
  have hcg := cg_pos X
  have h1 : 1 ≤ ‖s‖ ^ 2 := one_le_pow₀ hs1
  have h2 : ‖s‖ ^ (-((X + 1) / 2)) = (‖s‖ ^ ((X + 1) / 2))⁻¹ := Real.rpow_neg hs0.le _
  have h3 : ‖s‖ ^ ((X + 1) / 2) ≤ (2 * u ^ 3) ^ ((X + 1) / 2) :=
    Real.rpow_le_rpow hs0.le hs2u (by positivity)
  have h4 : Real.exp (-(π * u ^ 3)) ≤ Real.exp (-(π * ‖s‖ / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hpos2 : 0 < (2 * u ^ 3) ^ ((X + 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have h5 : ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ ≤ (‖s‖ ^ ((X + 1) / 2))⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hs0 _) h3
  have hlow : cg X * ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ * Real.exp (-(π * u ^ 3)) *
      Real.exp (-(t * π ^ 2 / 4)) ≤
      cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) *
        Real.exp (-(t * π ^ 2 / 4)) := by
    rw [h2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul _ h4 (Real.exp_pos _).le (by positivity)
    calc cg X * ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ = cg X * 1 * ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ := by
          ring
      _ ≤ cg X * ‖s‖ ^ 2 * (‖s‖ ^ ((X + 1) / 2))⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hcg.le) h5 (by positivity) (by positivity)
  have hlow0 : 0 < cg X * ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ * Real.exp (-(π * u ^ 3)) *
      Real.exp (-(t * π ^ 2 / 4)) := by positivity
  calc 1 / (cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) *
        Real.exp (-(t * π ^ 2 / 4)))
      ≤ 1 / (cg X * ((2 * u ^ 3) ^ ((X + 1) / 2))⁻¹ * Real.exp (-(π * u ^ 3)) *
        Real.exp (-(t * π ^ 2 / 4))) := div_le_div_of_nonneg_left (by norm_num) hlow0 hlow
    _ = 1 / cg X * (2 * u ^ 3) ^ ((X + 1) / 2) * Real.exp (π * u ^ 3) *
        Real.exp (t * π ^ 2 / 4) := by
        rw [Real.exp_neg, Real.exp_neg]
        field_simp

theorem Tmaj_nonneg {t X u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) : 0 ≤ Tmaj t X u := by
  unfold Tmaj; positivity

theorem epiece_le_Emaj {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    {u : ℝ} (hu : 1 ≤ u) (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3) {L : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u)
    (hY2 : 2 * t * π ≤ u ^ 2 / 20) : epiece t X s L (u ^ 2 / 20) ≤ Emaj t X u := by
  have hu0 : 0 < u := by linarith
  have hsu := norm_s_ge hy hu0.le
  have hs2u := norm_s_le hX hy hXu hu0.le
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
  have hs1 : 1 ≤ ‖s‖ := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  have hξ := ξ_le ht.le hX0 hL hLu hu
  have hξ₁ := ξ₁_le ht.le hX0 hX hL hLu hu hy hXu
  have hξ₁0 : 0 ≤ 2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6) := by
    have : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs1
    positivity
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hξ0 : 0 ≤ X + 2 * t * L + 2 := by positivity
  have hM := MH_le_Mmaj ht hX0 hu hL hLu hξ₁0 hξ₁ hY2
  have hT := T_le_Tmaj (X := X) ht hu hξ₁0 hξ₁
  have hΓ := inv_γlow_le_Γmaj (t := t) ht hX0 hu hs1 hs2u
  have hγpos : 0 < γlow t X s := γlow_pos hs0
  have hMH0 : 0 ≤ MH t X (2 * t * L) (u ^ 2 / 20) (u ^ 3)
      (2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) := MH_nonneg (by positivity)
  have hTm0 := Tmaj_nonneg (X := X) ht hu0.le
  have hMm0 : 0 ≤ Mmaj t X u := Mmaj_nonneg (by unfold cZ cξ; positivity)
  have hT0 : 0 ≤ 2 * (Real.exp ((2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6)) ^ 2 /
      (4 * t)) / (2 * π)) * (1 + |u ^ 3| + 4 * √t) * √(64 * π * t) *
      Real.exp (-((u ^ 2 / 20) ^ 2 / (64 * t))) := by positivity
  unfold epiece
  rw [hy]
  rw [div_eq_mul_one_div]
  apply mul_le_mul (mul_le_mul_of_nonneg_right _ (by positivity)) hΓ (by positivity) (by positivity)
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hξ hξ0
    (by positivity)) hT

/-- **The relative defect is majorized by `Bmaj t X u`.** -/
theorem norm_rdef_le_Bmaj {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X)
    {u : ℝ} (hu : 1 ≤ u) (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3) {L : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u)
    (hs2π : 2 * π ≤ ‖s‖) (hst : 12 * t ≤ ‖s‖) (hstrip : 4 * |s.re| ≤ s.im) (hy2' : 2 ≤ s.im)
    (hY2 : 2 * t * π ≤ u ^ 2 / 20)
    (hsec : X + 2 * t * L + 2 ≤ s.im - u ^ 2 / 20) (hy2 : 2 ≤ s.im - u ^ 2 / 20)
    (hζY : 2 * t * L + u ^ 2 / 20 ≤ ‖s‖ / 8)
    (hsmall : 402 * (2 * t * L + u ^ 2 / 20) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1)
    (hq : ‖q s (2 * t * L)‖ ≤ 1) (hq2 : 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1)
    (hF : (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ ≤ 1) :
    ‖rdef t s L (u ^ 2 / 20)‖ ≤ Bmaj t X u := by
  have hu0 : 0 < u := by linarith
  have hY : 0 < u ^ 2 / 20 := by positivity
  have hmain := norm_rdef_le_explicit ht hX0 hX hs2π hst hstrip hy2' hL hY hY2 hsec hy2 hζY hsmall
    hq hq2 hF
  refine hmain.trans ?_
  have hsu := norm_s_ge hy hu0.le
  have hs2 : 2 ≤ ‖s‖ := by nlinarith [Real.pi_gt_three]
  have hqu := norm_q_le_u ht hs2 hu hy hL hLu
  have ha := a_le_Amaj ht hu hsu hL hLu
  have hb := b_le_Bmaj' ht hu hsu hqu
  have hd := d_le_Dmaj ht hu0.le hL hq2 (β₃_le_β₃maj ht hu hsu hL hLu)
  have he := epiece_le_Emaj ht hX0 hX hu hy hXu hL hLu hY2
  have hDm0 := Dmaj_nonneg ht hu0.le
  have hAm0 : 0 ≤ Amaj t u := by unfold Amaj; positivity
  have hBm0 : 0 ≤ Bmaj' t u := by unfold Bmaj'; positivity
  have hd0 : 0 ≤ (β₃ t s (2 * t * L) + β₄ t (u ^ 2 / 20)) /
      (√(2 * π * t) * Real.exp (-(2 * t * ‖q s (2 * t * L)‖ ^ 2))) := by
    unfold β₃ β₄
    positivity
  have hb0 : 0 ≤ 36 * t / ‖s‖ + 4 * t * ‖q s (2 * t * L)‖ ^ 2 := by positivity
  have ha0 : 0 ≤ 2 * ((6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖) := by positivity
  unfold Bmaj
  gcongr

/-! ## The majorant vanishes at infinity -/

theorem tendsto_quartic_atBot {a : ℝ} (ha : 0 < a) (A B C D : ℝ) :
    Tendsto (fun u : ℝ => -a * u ^ 4 + A * u ^ 3 + B * u ^ 2 + C * u + D) atTop atBot := by
  have h1 : Tendsto (fun u : ℝ => -a + A / u + B / u ^ 2 + C / u ^ 3 + D / u ^ 4) atTop
      (𝓝 (-a + 0 + 0 + 0 + 0)) :=
    (((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num)))).add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num)))).add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num)))
  simp only [add_zero] at h1
  have h2 : Tendsto (fun u : ℝ => u ^ 4 * (-a + A / u + B / u ^ 2 + C / u ^ 3 + D / u ^ 4)) atTop
      atBot :=
    Tendsto.atTop_mul_neg (by linarith) (tendsto_pow_atTop (by norm_num)) h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  field_simp
  first | done | ring

theorem tendsto_exp_quartic {a : ℝ} (ha : 0 < a) (A B C D : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (-a * u ^ 4 + A * u ^ 3 + B * u ^ 2 + C * u + D)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_quartic_atBot ha A B C D)

theorem tendsto_const_div (c : ℝ) : Tendsto (fun u : ℝ => c / u) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_Amaj (t : ℝ) : Tendsto (fun u => Amaj t u) atTop (𝓝 0) := tendsto_const_div _
theorem tendsto_Bmaj' (t : ℝ) : Tendsto (fun u => Bmaj' t u) atTop (𝓝 0) := tendsto_const_div _
theorem tendsto_β₃maj (t : ℝ) : Tendsto (fun u => β₃maj t u) atTop (𝓝 0) := tendsto_const_div _

theorem tendsto_β₄maj {t : ℝ} (ht : 0 < t) : Tendsto (fun u => β₄maj t u) atTop (𝓝 0) := by
  have hc : 0 < c₃ t / 800 := by unfold c₃; positivity
  have h := (tendsto_exp_quartic hc 0 0 0 0).const_mul (2 * Real.exp (8 * t) * √(2 * π / c₃ t))
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun u => ?_)
  simp only [β₄maj]
  rw [show -(c₃ t / 2) * (u ^ 2 / 20) ^ 2 =
    -(c₃ t / 800) * u ^ 4 + 0 * u ^ 3 + 0 * u ^ 2 + 0 * u + 0 by ring]

theorem tendsto_Dmaj {t : ℝ} (ht : 0 < t) : Tendsto (fun u => Dmaj t u) atTop (𝓝 0) := by
  have h := ((tendsto_β₃maj t).add (tendsto_β₄maj ht)).const_mul (Real.exp 1 / √(2 * π * t))
  simpa [Dmaj] using h

theorem Mmaj_le_exp {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u : ℝ} (hu : 1 ≤ u) :
    Mmaj t X u ≤ Real.exp (-(1 / (6400 * t)) * u ^ 4 + 0 * u ^ 3 +
      (c₁ t X ^ 2 / (4 * t) + (cZ t X + 3) * (cξ t X + 1) / 2) * u ^ 2 +
      (2 * (cZ t X + 3) + 2 * cξ t X) * u + 2) := by
  have hu0 : 0 < u := by linarith
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hcZ : 2 ≤ cZ t X := by unfold cZ; linarith
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
  have hb : 1 ≤ cZ t X * u ^ 3 := by nlinarith
  have hb0 : 0 < cZ t X * u ^ 3 := by linarith
  have hlogb : Real.log (cZ t X * u ^ 3) ≤ (cZ t X + 3) * u := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < cZ t X)
    have := Real.log_le_sub_one_of_pos hu0
    push_cast
    nlinarith
  have hlogb0 : 0 ≤ Real.log (cZ t X * u ^ 3) := Real.log_nonneg hb
  have e1 : (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) ≤
      Real.exp ((cZ t X + 3) * (cξ t X + 1) / 2 * u ^ 2) := by
    rw [Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.mpr
    have h1 : cξ t X * u + 1 ≤ (cξ t X + 1) * u := by nlinarith
    calc Real.log (cZ t X * u ^ 3) * ((cξ t X * u + 1) / 2)
        ≤ ((cZ t X + 3) * u) * (((cξ t X + 1) * u) / 2) := by gcongr
      _ = (cZ t X + 3) * (cξ t X + 1) / 2 * u ^ 2 := by ring
  have e2 : (cZ t X * u ^ 3) ^ 2 ≤ Real.exp (2 * (cZ t X + 3) * u) := by
    rw [← Real.exp_log (by positivity : 0 < (cZ t X * u ^ 3) ^ 2), Real.log_pow]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have e3 : (π * Real.exp 1) ^ (cξ t X * u / 2) ≤ Real.exp (2 * cξ t X * u) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have := Real.pi_le_four
    have : 0 ≤ cξ t X * u := by positivity
    nlinarith
  have e4 : Real.exp (π / 4) * (√(2 * π) / 2) ≤ Real.exp 2 := by
    have h1 : Real.exp (π / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [Real.pi_le_four])
    have h2 : √(2 * π) ≤ 3 := by
      calc √(2 * π) ≤ √9 := Real.sqrt_le_sqrt (by nlinarith [Real.pi_le_four])
        _ = 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h4 := Real.add_one_le_exp (1 : ℝ)
    have h5 := Real.exp_pos (1 : ℝ)
    have h6 := Real.exp_pos (π / 4)
    rw [h3]
    nlinarith [Real.sqrt_nonneg (2 * π)]
  have hA0 : 0 ≤ (cZ t X * u ^ 3) ^ 2 := sq_nonneg _
  have hB0 : 0 ≤ (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) := Real.rpow_nonneg hb0.le _
  have hC0 : 0 ≤ (π * Real.exp 1) ^ (cξ t X * u / 2) := Real.rpow_nonneg (by positivity) _
  unfold Mmaj
  calc Real.exp ((c₁ t X ^ 2 * u ^ 2 - u ^ 4 / 1600) / (4 * t)) *
        (Real.exp (π / 4) * (√(2 * π) / 2 * (cZ t X * u ^ 3) ^ 2 *
          (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) * (π * Real.exp 1) ^ (cξ t X * u / 2)))
      = Real.exp ((c₁ t X ^ 2 * u ^ 2 - u ^ 4 / 1600) / (4 * t)) *
        ((Real.exp (π / 4) * (√(2 * π) / 2)) * ((cZ t X * u ^ 3) ^ 2 *
          (cZ t X * u ^ 3) ^ ((cξ t X * u + 1) / 2) * (π * Real.exp 1) ^ (cξ t X * u / 2))) := by
        ring
    _ ≤ Real.exp ((c₁ t X ^ 2 * u ^ 2 - u ^ 4 / 1600) / (4 * t)) *
        (Real.exp 2 * (Real.exp (2 * (cZ t X + 3) * u) *
          Real.exp ((cZ t X + 3) * (cξ t X + 1) / 2 * u ^ 2) * Real.exp (2 * cξ t X * u))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul e4 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul (mul_le_mul e2 e1 hB0 (Real.exp_pos _).le) e3 hC0 (by positivity)
    _ = Real.exp (-(1 / (6400 * t)) * u ^ 4 + 0 * u ^ 3 +
        (c₁ t X ^ 2 / (4 * t) + (cZ t X + 3) * (cξ t X + 1) / 2) * u ^ 2 +
        (2 * (cZ t X + 3) + 2 * cξ t X) * u + 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring

theorem Tmaj_le_exp {t X : ℝ} (ht : 0 < t) {u : ℝ} (hu : 1 ≤ u) :
    Tmaj t X u ≤ Real.exp (-(1 / (25600 * t)) * u ^ 4 + 1 * u ^ 3 +
      (c₁ t X ^ 2 / (4 * t)) * u ^ 2 + 0 * u + (4 * √t + √(64 * π * t))) := by
  have hu0 : 0 ≤ u := by linarith
  unfold Tmaj
  have hE := Real.exp_pos (c₁ t X ^ 2 * u ^ 2 / (4 * t))
  have e1 : 2 * (Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) / (2 * π)) ≤
      Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) := by
    calc 2 * (Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) / (2 * π))
        = Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) / π := by
          field_simp
          first | done | ring
      _ ≤ Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) :=
          div_le_self hE.le (by linarith [Real.pi_gt_three])
  have e2 : 1 + u ^ 3 + 4 * √t ≤ Real.exp (u ^ 3 + 4 * √t) := by
    have := Real.add_one_le_exp (u ^ 3 + 4 * √t); linarith
  have e3 : √(64 * π * t) ≤ Real.exp (√(64 * π * t)) := by
    have := Real.add_one_le_exp (√(64 * π * t)); linarith
  calc 2 * (Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) / (2 * π)) * (1 + u ^ 3 + 4 * √t) *
        √(64 * π * t) * Real.exp (-(u ^ 4 / (25600 * t)))
      ≤ Real.exp (c₁ t X ^ 2 * u ^ 2 / (4 * t)) * Real.exp (u ^ 3 + 4 * √t) *
        Real.exp (√(64 * π * t)) * Real.exp (-(u ^ 4 / (25600 * t))) := by
        gcongr
    _ = Real.exp (-(1 / (25600 * t)) * u ^ 4 + 1 * u ^ 3 +
        (c₁ t X ^ 2 / (4 * t)) * u ^ 2 + 0 * u + (4 * √t + √(64 * π * t))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring

theorem Γmaj_le_exp {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u : ℝ} (hu : 1 ≤ u) :
    Γmaj t X u ≤ Real.exp (π * u ^ 3 + 3 * (X + 1) / 2 * u + (Real.log (1 / cg X) + t * π ^ 2 / 4)) := by
  have hu0 : 0 < u := by linarith
  unfold Γmaj
  have hcg := cg_pos X
  have e1 : 1 / cg X = Real.exp (Real.log (1 / cg X)) := (Real.exp_log (by positivity)).symm
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
  have e2 : (2 * u ^ 3) ^ ((X + 1) / 2) ≤ Real.exp (3 * (X + 1) / 2 * u) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    have hl : Real.log (2 * u ^ 3) ≤ 3 * u := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have := Real.log_two_lt_d9
      have := Real.log_le_sub_one_of_pos hu0
      push_cast
      nlinarith
    have hl0 : 0 ≤ Real.log (2 * u ^ 3) := Real.log_nonneg (by nlinarith)
    calc Real.log (2 * u ^ 3) * ((X + 1) / 2) ≤ 3 * u * ((X + 1) / 2) := by gcongr
      _ = 3 * (X + 1) / 2 * u := by ring
  calc 1 / cg X * (2 * u ^ 3) ^ ((X + 1) / 2) * Real.exp (π * u ^ 3) * Real.exp (t * π ^ 2 / 4)
      ≤ Real.exp (Real.log (1 / cg X)) * Real.exp (3 * (X + 1) / 2 * u) * Real.exp (π * u ^ 3) *
        Real.exp (t * π ^ 2 / 4) := by
        rw [← e1]
        gcongr
    _ = Real.exp (π * u ^ 3 + 3 * (X + 1) / 2 * u + (Real.log (1 / cg X) + t * π ^ 2 / 4)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- The exponent majorizing the `M`-part of `Emaj`. -/
def PM (t X u : ℝ) : ℝ := -(1 / (6400 * t)) * u ^ 4 + π * u ^ 3 +
  (c₁ t X ^ 2 / (4 * t) + (cZ t X + 3) * (cξ t X + 1) / 2) * u ^ 2 +
  (2 * (cZ t X + 3) + 2 * cξ t X + 2 * cξ t X + 3 * (X + 1) / 2) * u +
  (2 + Real.log ((√(4 * π * t))⁻¹) + Real.log (1 / cg X) + t * π ^ 2 / 4)
/-- The exponent majorizing the `T`-part of `Emaj`. -/
def PT (t X u : ℝ) : ℝ := -(1 / (25600 * t)) * u ^ 4 + (1 + π) * u ^ 3 +
  (c₁ t X ^ 2 / (4 * t)) * u ^ 2 + (3 * (X + 1) / 2) * u +
  (4 * √t + √(64 * π * t) + Real.log ((√(4 * π * t))⁻¹) + Real.log (1 / cg X) + t * π ^ 2 / 4)

theorem Emaj_le_exp {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u : ℝ} (hu : 1 ≤ u) :
    Emaj t X u ≤ Real.exp (PM t X u) + Real.exp (PT t X u) := by
  have hu0 : 0 < u := by linarith
  have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
  have hM := Mmaj_le_exp ht hX0 hu
  have hT := Tmaj_le_exp (X := X) ht hu
  have hΓ := Γmaj_le_exp ht hX0 hu
  have hk : (√(4 * π * t))⁻¹ = Real.exp (Real.log ((√(4 * π * t))⁻¹)) :=
    (Real.exp_log (by positivity)).symm
  have hcu : 2 * (cξ t X * u) ≤ Real.exp (2 * cξ t X * u) := by
    have := Real.add_one_le_exp (2 * cξ t X * u); linarith
  have hMm0 : 0 ≤ Mmaj t X u := Mmaj_nonneg (by unfold cZ cξ; positivity)
  have hTm0 := Tmaj_nonneg (X := X) ht hu0.le
  have hΓ0 : 0 ≤ Γmaj t X u := by
    unfold Γmaj
    have := cg_pos X
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * u ^ 3) ((X + 1) / 2)
    positivity
  unfold Emaj
  calc (2 * Mmaj t X u * (cξ t X * u) + Tmaj t X u) * (√(4 * π * t))⁻¹ * Γmaj t X u
      = (Mmaj t X u * (2 * (cξ t X * u)) + Tmaj t X u) * (√(4 * π * t))⁻¹ * Γmaj t X u := by ring
    _ ≤ (Real.exp (-(1 / (6400 * t)) * u ^ 4 + 0 * u ^ 3 +
          (c₁ t X ^ 2 / (4 * t) + (cZ t X + 3) * (cξ t X + 1) / 2) * u ^ 2 +
          (2 * (cZ t X + 3) + 2 * cξ t X) * u + 2) * Real.exp (2 * cξ t X * u) +
          Real.exp (-(1 / (25600 * t)) * u ^ 4 + 1 * u ^ 3 +
          (c₁ t X ^ 2 / (4 * t)) * u ^ 2 + 0 * u + (4 * √t + √(64 * π * t)))) *
        Real.exp (Real.log ((√(4 * π * t))⁻¹)) *
        Real.exp (π * u ^ 3 + 3 * (X + 1) / 2 * u + (Real.log (1 / cg X) + t * π ^ 2 / 4)) := by
        rw [← hk]
        apply mul_le_mul (mul_le_mul_of_nonneg_right _ (by positivity)) hΓ hΓ0 (by positivity)
        exact add_le_add (mul_le_mul hM hcu (by positivity) (Real.exp_pos _).le) hT
    _ = Real.exp (PM t X u) + Real.exp (PT t X u) := by
        unfold PM PT
        rw [add_mul, add_mul]
        simp only [← Real.exp_add]
        congr 1 <;> congr 1 <;> ring

theorem tendsto_Emaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    Tendsto (fun u => Emaj t X u) atTop (𝓝 0) := by
  have hPM : Tendsto (fun u => Real.exp (PM t X u)) atTop (𝓝 0) :=
    tendsto_exp_quartic (by positivity) _ _ _ _
  have hPT : Tendsto (fun u => Real.exp (PT t X u)) atTop (𝓝 0) :=
    tendsto_exp_quartic (by positivity) _ _ _ _
  have h := hPM.add hPT
  rw [add_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 1] with u hu
    have hu0 : 0 ≤ u := by linarith
    have hMm0 : 0 ≤ Mmaj t X u := Mmaj_nonneg (by unfold cZ cξ; positivity)
    have hTm0 := Tmaj_nonneg (X := X) ht hu0
    have hcξ : 0 ≤ cξ t X := by unfold cξ; positivity
    have hΓ0 : 0 ≤ Γmaj t X u := by
      unfold Γmaj
      have := cg_pos X
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * u ^ 3) ((X + 1) / 2)
      positivity
    unfold Emaj
    positivity
  · filter_upwards [eventually_ge_atTop 1] with u hu
    exact Emaj_le_exp ht hX0 hu

/-- **The majorant of the relative defect vanishes as `u → ∞`.** -/
theorem tendsto_Bmaj {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) :
    Tendsto (fun u => Bmaj t X u) atTop (𝓝 0) := by
  have hA := tendsto_Amaj t
  have hB := tendsto_Bmaj' t
  have hD := tendsto_Dmaj ht
  have hE := tendsto_Emaj ht hX0
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := ((((hA.mul (h1.add hB)).add hB).mul (h1.add hD)).add hD).add hE
  simpa [Bmaj] using h

/-! ## The threshold and the main-range event theorem -/

/-- The threshold in `u` beyond which every side condition of the main-range bound holds. -/
def u₀ (t X : ℝ) : ℝ :=
  3 + 4 * X + 160 * t + 2 * (X + 2 * t + 2) + 16 * t + 40 * t + (3 + 6 * t) +
    2 * t * (3 + 6 * t) ^ 2 + (6 * t + 6 * t ^ 2)

theorem u₀_pos {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) : 3 ≤ u₀ t X := by
  unfold u₀
  have := sq_nonneg (3 + 6 * t)
  nlinarith [mul_nonneg ht.le (sq_nonneg (3 + 6 * t)), mul_nonneg ht.le ht.le]

theorem side_sec {t X u L : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) (hu1 : 1 ≤ u) (hL0 : 0 ≤ L)
    (hLu : L ≤ u) (h : 2 * (X + 2 * t + 2) ≤ u) : X + 2 * t * L + 2 ≤ u ^ 3 - u ^ 2 / 20 := by
  have e1 : 2 * t * L ≤ 2 * t * u := by nlinarith
  have e2 : X + 2 * t * u + 2 ≤ (X + 2 * t + 2) * u := by nlinarith
  have hu0 : 0 ≤ u := by linarith
  have e3 : (X + 2 * t + 2) * u ≤ u ^ 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h hu0, mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)]
  have e4 : u ^ 2 / 20 ≤ u ^ 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)]
  linarith

theorem side_ζY {t u L : ℝ} (ht : 0 < t) (hu1 : 1 ≤ u) (hL0 : 0 ≤ L) (hLu : L ≤ u)
    (h : 16 * t + 1 ≤ u) : 2 * t * L + u ^ 2 / 20 ≤ u ^ 3 / 8 := by
  have hu0 : 0 ≤ u := by linarith
  have huu : u ≤ u ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hu1 hu0]
  have e1 : 2 * t * L ≤ 2 * t * u ^ 2 :=
    mul_le_mul_of_nonneg_left (hLu.trans huu) (by positivity)
  have e2 : (2 * t + 1 / 20) * u ^ 2 ≤ u ^ 3 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg u)]
  linarith

theorem side_small {t u L : ℝ} {s : ℂ} (ht : 0 < t) (hu3 : 3 ≤ u) (hL0 : 0 ≤ L) (hLu : L ≤ u)
    (h : 40 * t ≤ u) (hsu : u ^ 3 ≤ ‖s‖) :
    402 * (2 * t * L + u ^ 2 / 20) ^ 3 / ‖s‖ ^ 2 + 2 * π / (3 * ‖s‖) ≤ 1 := by
  have hu0 : 0 < u := by linarith
  have e1 : 2 * t * L + u ^ 2 / 20 ≤ u ^ 2 / 10 := by
    have : 2 * t * L ≤ 2 * t * u := by nlinarith
    nlinarith
  have e2 : (2 * t * L + u ^ 2 / 20) ^ 3 ≤ (u ^ 2 / 10) ^ 3 :=
    pow_le_pow_left₀ (by positivity) e1 3
  have e3 : (u ^ 3) ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ (by positivity) hsu 2
  have hu27 : 27 ≤ u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hu3 3]
  have e4 : 402 * (2 * t * L + u ^ 2 / 20) ^ 3 / ‖s‖ ^ 2 ≤ 402 / 1000 := by
    calc 402 * (2 * t * L + u ^ 2 / 20) ^ 3 / ‖s‖ ^ 2 ≤ 402 * (u ^ 2 / 10) ^ 3 / (u ^ 3) ^ 2 := by
          gcongr
      _ = 402 / 1000 := by
          field_simp
          first | done | ring
  have e5 : 2 * π / (3 * ‖s‖) ≤ 2 * π / (3 * 27) := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have e6 : 2 * π / (3 * 27) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [Real.pi_le_four]
  linarith

theorem side_q2 {t u : ℝ} {s : ℂ} {L : ℝ} (ht : 0 < t) (hu1 : 1 ≤ u)
    (hqu : ‖q s (2 * t * L)‖ ≤ (3 + 6 * t) / u ^ 2) (h : 2 * t * (3 + 6 * t) ^ 2 ≤ u) :
    2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 1 := by
  have hu0 : 0 < u := by linarith
  have e1 : ‖q s (2 * t * L)‖ ^ 2 ≤ ((3 + 6 * t) / u ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hqu 2
  have e2 : ((3 + 6 * t) / u ^ 2) ^ 2 ≤ (3 + 6 * t) ^ 2 / u := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hu0]
    have huu : u ≤ u ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hu1 hu0.le]
    have h2 : u ^ 2 ≤ (u ^ 2) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hu1.trans huu) (sq_nonneg u)]
    nlinarith [sq_nonneg (3 + 6 * t)]
  have e3 : 2 * t * ((3 + 6 * t) ^ 2 / u) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hu0]
    linarith
  calc 2 * t * ‖q s (2 * t * L)‖ ^ 2 ≤ 2 * t * ((3 + 6 * t) ^ 2 / u) := by
        gcongr
        exact e1.trans e2
    _ ≤ 1 := e3

theorem side_Y2 {t u : ℝ} (ht : 0 < t) (hu1 : 1 ≤ u) (h : 160 * t ≤ u) :
    2 * t * π ≤ u ^ 2 / 20 := by
  nlinarith [Real.pi_le_four, mul_le_mul_of_nonneg_left hu1 ht.le]

theorem g_ne_zero_of {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : |s.re| ≤ X) (hs2 : 2 ≤ ‖s‖) :
    g s ≠ 0 := by
  have hs0 : 0 < ‖s‖ := by linarith
  have hlow := norm_g_ge hX0 hX hs2
  have hpos : 0 < cg X * ‖s‖ ^ 2 * ‖s‖ ^ (-((X + 1) / 2)) * Real.exp (-(π * ‖s‖ / 2)) :=
    mul_pos (mul_pos (mul_pos (cg_pos X) (by positivity)) (Real.rpow_pos_of_pos hs0 _))
      (Real.exp_pos _)
  exact norm_pos_iff.mp (hpos.trans_le hlow)

/-- **The main-range event theorem.** For `u ≥ u₀ t X`, `s = x + i u³` with `|x| ≤ X`, and every
`n ≠ 0` with `log |n| ≤ u`, the flowed event at `J_t(s)` equals the steepest-descent main term
times `1 + r` with `‖r‖ ≤ Bmaj t X u`, and `Bmaj t X u → 0`. -/
theorem event_main {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {u : ℝ} (hu : u₀ t X ≤ u) {s : ℂ}
    (hX : |s.re| ≤ X) (hy : s.im = u ^ 3) {n : ℤ} (hn : n ≠ 0) (hLu : Real.log |(n : ℝ)| ≤ u) :
    (∫ v : ℝ, flowedTerm t (J t s) n v) =
      γt' t s * Complex.exp (-s * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) *
        Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
        (1 + rdef t s (Real.log |(n : ℝ)|) (u ^ 2 / 20)) ∧
      ‖rdef t s (Real.log |(n : ℝ)|) (u ^ 2 / 20)‖ ≤ Bmaj t X u := by
  set L : ℝ := Real.log |(n : ℝ)| with hLdef
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    have := Int.one_le_abs hn
    exact_mod_cast this
  have hu3 : 3 ≤ u := (u₀_pos ht hX0).trans hu
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hu₀ : u₀ t X ≤ u := hu
  unfold u₀ at hu₀
  have ht2 : 0 ≤ t * (3 + 6 * t) ^ 2 := by positivity
  have ht3 : 0 ≤ t ^ 2 := sq_nonneg t
  have hucube := u_le_cube hu1
  have huu : u ≤ u ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hu1 hu0.le]
  have hu23 : u ^ 2 ≤ u ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)]
  have hXu : X ≤ u ^ 3 := by linarith
  have hsu := norm_s_ge hy hu0.le
  have hs2 : 2 ≤ ‖s‖ := by linarith
  have hs2π : 2 * π ≤ ‖s‖ := by linarith [Real.pi_le_four]
  have hst : 12 * t ≤ ‖s‖ := by linarith
  have hstrip : 4 * |s.re| ≤ s.im := by rw [hy]; linarith
  have hy2' : 2 ≤ s.im := by rw [hy]; linarith
  have hY2 : 2 * t * π ≤ u ^ 2 / 20 := side_Y2 ht hu1 (by linarith)
  have hsec : X + 2 * t * L + 2 ≤ s.im - u ^ 2 / 20 := by
    rw [hy]; exact side_sec ht hX0 hu1 hL0 hLu (by linarith)
  have hy2 : 2 ≤ s.im - u ^ 2 / 20 := by
    rw [hy]
    have := side_sec ht hX0 hu1 hL0 hLu (by linarith)
    linarith
  have hζY : 2 * t * L + u ^ 2 / 20 ≤ ‖s‖ / 8 := by
    have := side_ζY ht hu1 hL0 hLu (by linarith)
    linarith
  have hsmall := side_small ht hu3 hL0 hLu (by linarith) hsu
  have hqu := norm_q_le_u ht hs2 hu1 hy hL0 hLu
  have hq : ‖q s (2 * t * L)‖ ≤ 1 := by
    refine hqu.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hq2 := side_q2 ht hu1 hqu (by linarith)
  have hF : (6 * t * L + 6 * t ^ 2 * L ^ 2) / ‖s‖ ≤ 1 := by
    have h := a_le_Amaj ht hu1 hsu hL0 hLu
    unfold Amaj at h
    have : (12 * t + 12 * t ^ 2) / u ≤ 2 := by
      rw [div_le_iff₀ hu0]; linarith
    linarith
  have hg : g s ≠ 0 := g_ne_zero_of hX0 hX hs2
  have hY : 0 < u ^ 2 / 20 := by positivity
  have hyY : u ^ 2 / 20 < s.im := by
    rw [hy]
    linarith [pow_pos hu0 2]
  refine ⟨event_eq_main_mul ht hg hs2 hst hn hY hyY, ?_⟩
  exact norm_rdef_le_Bmaj ht hX0 hX hu1 hy hXu hL0 hLu hs2π hst hstrip hy2' hY2 hsec hy2 hζY
    hsmall hq hq2 hF

end Soma.Holonics.RH.EventMainRange
