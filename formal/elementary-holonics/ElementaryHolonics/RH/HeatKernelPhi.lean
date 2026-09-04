import Mathlib
import ElementaryHolonics.RH.XiCentre
import ElementaryHolonics.RH.HeatFlowEntire

/-!
# FT4 (ii): the kernel `Φ` of the flow

`θ(x) = Σ_{n ∈ ℤ} e^{−π n² x}` is the theta kernel of Mathlib's even Hurwitz FE-pair at `a = 0`;
it is termwise twice differentiable on `(0, ∞)`, and its functional equation
`θ(x) = x^{−1/2} θ(1/x)` differentiates to the reflection law of

```text
Ψ(x) := 2x² θ″(x) + 3x θ′(x) = Σ_{n ∈ ℤ} (2π² n⁴ x² − 3π n² x) e^{−π n² x},   Ψ(1/x) = x^{1/2} Ψ(x).
```

The kernel is `Φ(u) := e^{u/2} Ψ(e^{2u})`: even, positive, and of double-exponential decay. FT4 (iii)
returns `ξ(s) = ∫ e^{(s − ½)u} Φ(u) du` and the flow identity. Every theorem is discharged with no
`sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.HeatKernelPhi

open Real Set Filter Topology MeasureTheory HurwitzZeta
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire

/-! ## The theta series and its termwise derivatives -/

/-- The theta kernel at `a = 0`. -/
abbrev θ (x : ℝ) : ℝ := evenKernel 0 x

/-- The theta term. -/
def θterm (n : ℤ) (x : ℝ) : ℝ := Real.exp (-π * (n : ℝ) ^ 2 * x)

theorem hasSum_theta {x : ℝ} (hx : 0 < x) : HasSum (fun n : ℤ => θterm n x) (θ x) := by
  have h := hasSum_int_evenKernel₀ (0 : ℝ) hx
  simp only [add_zero, QuotientAddGroup.mk_zero, eq_self_iff_true, if_true, Int.cast_eq_zero] at h
  have h1 : HasSum (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have h2 := h.add h1
  rw [sub_add_cancel] at h2
  refine h2.congr_fun ?_
  intro n
  unfold θterm
  by_cases hn : n = 0
  · subst hn
    simp
  · simp [hn]

/-- Summability of `n^k e^{−c n²}` over the integers. -/
theorem summable_pow_mul_exp_neg_sq {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ k * Real.exp (-c * (n : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ 2)) := by
    have hr : ‖Real.exp (-c)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    refine (summable_pow_mul_geometric_of_norm_lt_one k hr).of_nonneg_of_le
      (fun n => by positivity) (fun n => ?_)
    rw [← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp
      · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hnat.congr fun n => ?_
    simp
  · refine hnat.congr fun n => ?_
    simp

/-- A general term `c n^k e^{−π n² x}` of the theta-type series. -/
def gterm (c : ℝ) (k : ℕ) (n : ℤ) (x : ℝ) : ℝ := c * (n : ℝ) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * x)

theorem hasDerivAt_gterm (c : ℝ) (k : ℕ) (n : ℤ) (x : ℝ) :
    HasDerivAt (gterm c k n) (gterm (c * -π) (k + 2) n x) x := by
  unfold gterm
  have h : HasDerivAt (fun y : ℝ => -π * (n : ℝ) ^ 2 * y) (-π * (n : ℝ) ^ 2) x := by
    have := (hasDerivAt_id x).const_mul (-π * (n : ℝ) ^ 2)
    simpa using this
  have h2 := (h.exp).const_mul (c * (n : ℝ) ^ k)
  refine h2.congr_deriv ?_
  ring

theorem norm_gterm_le {n : ℤ} {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ < x) (c : ℝ) (k : ℕ) :
    ‖gterm c k n x‖ ≤ |c| * (|(n : ℝ)| ^ k * Real.exp (-(π * x₀) * (n : ℝ) ^ 2)) := by
  unfold gterm
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
    abs_of_pos (Real.exp_pos _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have h1 : π * (n : ℝ) ^ 2 * x₀ ≤ π * (n : ℝ) ^ 2 * x :=
    mul_le_mul_of_nonneg_left hx.le (mul_nonneg Real.pi_pos.le h0)
  linarith

theorem summable_gterm {c : ℝ} (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℤ => gterm c k n x) := by
  have hs := (summable_pow_mul_exp_neg_sq (c := π * (x / 2)) (by positivity) k).mul_left |c|
  refine hs.of_norm_bounded fun n => ?_
  exact norm_gterm_le (by positivity : 0 < x / 2) (by linarith : x / 2 < x) c k

/-- **The theta-type series differentiates termwise on `(0, ∞)`.** -/
theorem hasDerivAt_tsum_gterm (c : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => ∑' n : ℤ, gterm c k n z) (∑' n : ℤ, gterm (c * -π) (k + 2) n x) x := by
  have hx2 : 0 < x / 2 := by positivity
  have hu : Summable (fun n : ℤ => |c * -π| * (|(n : ℝ)| ^ (k + 2) *
      Real.exp (-(π * (x / 2)) * (n : ℝ) ^ 2))) :=
    (summable_pow_mul_exp_neg_sq (c := π * (x / 2)) (by positivity) (k + 2)).mul_left _
  have hg : ∀ (n : ℤ) (y : ℝ), y ∈ Ioi (x / 2) →
      HasDerivAt (gterm c k n) (gterm (c * -π) (k + 2) n y) y :=
    fun n y _ => hasDerivAt_gterm c k n y
  have hg' : ∀ (n : ℤ) (y : ℝ), y ∈ Ioi (x / 2) → ‖gterm (c * -π) (k + 2) n y‖ ≤
      |c * -π| * (|(n : ℝ)| ^ (k + 2) * Real.exp (-(π * (x / 2)) * (n : ℝ) ^ 2)) :=
    fun n y hy => norm_gterm_le hx2 (show x / 2 < y from hy) _ _
  have hx' : x ∈ Ioi (x / 2) := by
    simp only [mem_Ioi]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hg hg' hx'
    (summable_gterm k hx) hx'

/-- The first derivative series of theta. -/
def θ' (x : ℝ) : ℝ := ∑' n : ℤ, gterm (-π) 2 n x

/-- The second derivative series of theta. -/
def θ'' (x : ℝ) : ℝ := ∑' n : ℤ, gterm (π ^ 2) 4 n x

theorem theta_eq_tsum_gterm {x : ℝ} (hx : 0 < x) : θ x = ∑' n : ℤ, gterm 1 0 n x := by
  rw [← (hasSum_theta hx).tsum_eq]
  apply tsum_congr
  intro n
  unfold θterm gterm
  ring

/-- **`θ` is differentiable on `(0, ∞)` with derivative `θ′`.** -/
theorem hasDerivAt_theta {x : ℝ} (hx : 0 < x) : HasDerivAt θ (θ' x) x := by
  have h := hasDerivAt_tsum_gterm 1 0 hx
  have hev : (fun z => ∑' n : ℤ, gterm 1 0 n z) =ᶠ[𝓝 x] θ := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact (theta_eq_tsum_gterm hz).symm
  have h' := h.congr_of_eventuallyEq hev.symm
  refine h'.congr_deriv ?_
  unfold θ'
  apply tsum_congr
  intro n
  unfold gterm
  ring_nf

/-- **`θ′` is differentiable on `(0, ∞)` with derivative `θ″`.** -/
theorem hasDerivAt_theta' {x : ℝ} (hx : 0 < x) : HasDerivAt θ' (θ'' x) x := by
  have h := hasDerivAt_tsum_gterm (-π) 2 hx
  refine h.congr_deriv ?_
  unfold θ''
  apply tsum_congr
  intro n
  unfold gterm
  ring_nf

/-! ## The functional equation, differentiated -/

theorem theta_fe {x : ℝ} (hx : 0 < x) : θ x = x ^ (-(1 / 2 : ℝ)) * θ x⁻¹ := by
  have h := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [Real.rpow_neg hx.le, ← one_div, ← one_div]
  exact h

/-- The reflected kernel `x^{−1/2} θ(1/x)`. -/
def F (x : ℝ) : ℝ := x ^ (-(1 / 2 : ℝ)) * θ x⁻¹

theorem hasDerivAt_F {x : ℝ} (hx : 0 < x) :
    HasDerivAt F (-(1 / 2) * x ^ (-(1 / 2 : ℝ) - 1) * θ x⁻¹ +
      x ^ (-(1 / 2 : ℝ)) * (θ' x⁻¹ * -(x ^ 2)⁻¹)) x := by
  unfold F
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
      (1 * (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ) - 1)) x :=
    (hasDerivAt_id' x).rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => θ y⁻¹) (θ' x⁻¹ * -(x ^ 2)⁻¹) x :=
    (hasDerivAt_theta (inv_pos.mpr hx)).comp x (hasDerivAt_inv hx.ne')
  refine (h1.mul h2).congr_deriv ?_
  ring

theorem theta'_eq {x : ℝ} (hx : 0 < x) :
    θ' x = -(1 / 2) * x ^ (-(1 / 2 : ℝ) - 1) * θ x⁻¹ +
      x ^ (-(1 / 2 : ℝ)) * (θ' x⁻¹ * -(x ^ 2)⁻¹) := by
  have hF := hasDerivAt_F hx
  have hev : θ =ᶠ[𝓝 x] F := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact theta_fe hy
  exact (hasDerivAt_theta hx).unique (hF.congr_of_eventuallyEq hev)

/-- The reflected first derivative. -/
def G (x : ℝ) : ℝ :=
  -(1 / 2) * x ^ (-(1 / 2 : ℝ) - 1) * θ x⁻¹ + x ^ (-(1 / 2 : ℝ)) * (θ' x⁻¹ * -(x ^ 2)⁻¹)

theorem hasDerivAt_G {x : ℝ} (hx : 0 < x) :
    HasDerivAt G
      (-(1 / 2) * ((1 * (-(1 / 2 : ℝ) - 1) * x ^ (-(1 / 2 : ℝ) - 1 - 1)) * θ x⁻¹ +
          x ^ (-(1 / 2 : ℝ) - 1) * (θ' x⁻¹ * -(x ^ 2)⁻¹)) +
        ((1 * (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ) - 1)) * (θ' x⁻¹ * -(x ^ 2)⁻¹) +
          x ^ (-(1 / 2 : ℝ)) * ((θ'' x⁻¹ * -(x ^ 2)⁻¹) * -(x ^ 2)⁻¹ +
            θ' x⁻¹ * -(-(2 * x ^ 1) / (x ^ 2) ^ 2)))) x := by
  unfold G
  have hp1 : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2 : ℝ) - 1))
      (1 * (-(1 / 2 : ℝ) - 1) * x ^ (-(1 / 2 : ℝ) - 1 - 1)) x :=
    (hasDerivAt_id' x).rpow_const (Or.inl hx.ne')
  have hp2 : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
      (1 * (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ) - 1)) x :=
    (hasDerivAt_id' x).rpow_const (Or.inl hx.ne')
  have hθ : HasDerivAt (fun y : ℝ => θ y⁻¹) (θ' x⁻¹ * -(x ^ 2)⁻¹) x :=
    (hasDerivAt_theta (inv_pos.mpr hx)).comp x (hasDerivAt_inv hx.ne')
  have hθ' : HasDerivAt (fun y : ℝ => θ' y⁻¹) (θ'' x⁻¹ * -(x ^ 2)⁻¹) x :=
    (hasDerivAt_theta' (inv_pos.mpr hx)).comp x (hasDerivAt_inv hx.ne')
  have hinv : HasDerivAt (fun y : ℝ => -(y ^ 2)⁻¹) (-(-(2 * x ^ 1) / (x ^ 2) ^ 2)) x :=
    ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx.ne')).neg
  have hA : HasDerivAt (fun y : ℝ => -(1 / 2) * y ^ (-(1 / 2 : ℝ) - 1) * θ y⁻¹)
      (-(1 / 2) * ((1 * (-(1 / 2 : ℝ) - 1) * x ^ (-(1 / 2 : ℝ) - 1 - 1)) * θ x⁻¹ +
        x ^ (-(1 / 2 : ℝ) - 1) * (θ' x⁻¹ * -(x ^ 2)⁻¹))) x := by
    have := (hp1.const_mul (-(1 / 2 : ℝ))).mul hθ
    refine this.congr_deriv ?_
    ring
  have hB : HasDerivAt (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (θ' y⁻¹ * -(y ^ 2)⁻¹))
      ((1 * (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ) - 1)) * (θ' x⁻¹ * -(x ^ 2)⁻¹) +
        x ^ (-(1 / 2 : ℝ)) * ((θ'' x⁻¹ * -(x ^ 2)⁻¹) * -(x ^ 2)⁻¹ +
          θ' x⁻¹ * -(-(2 * x ^ 1) / (x ^ 2) ^ 2))) x :=
    hp2.mul (hθ'.mul hinv)
  exact hA.add hB

theorem theta''_eq {x : ℝ} (hx : 0 < x) :
    θ'' x = -(1 / 2) * ((1 * (-(1 / 2 : ℝ) - 1) * x ^ (-(1 / 2 : ℝ) - 1 - 1)) * θ x⁻¹ +
          x ^ (-(1 / 2 : ℝ) - 1) * (θ' x⁻¹ * -(x ^ 2)⁻¹)) +
        ((1 * (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ) - 1)) * (θ' x⁻¹ * -(x ^ 2)⁻¹) +
          x ^ (-(1 / 2 : ℝ)) * ((θ'' x⁻¹ * -(x ^ 2)⁻¹) * -(x ^ 2)⁻¹ +
            θ' x⁻¹ * -(-(2 * x ^ 1) / (x ^ 2) ^ 2))) := by
  have hG := hasDerivAt_G hx
  have hev : θ' =ᶠ[𝓝 x] G := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact theta'_eq hy
  exact (hasDerivAt_theta' hx).unique (hG.congr_of_eventuallyEq hev)

/-- `Ψ(x) = 2x² θ″(x) + 3x θ′(x)`. -/
def Ψ (x : ℝ) : ℝ := 2 * x ^ 2 * θ'' x + 3 * x * θ' x

/-- **The reflection law of `Ψ`: `Ψ(1/x) = x^{1/2} Ψ(x)`.** -/
theorem Ψ_inv {x : ℝ} (hx : 0 < x) : Ψ x⁻¹ = x ^ (1 / 2 : ℝ) * Ψ x := by
  have h1 := theta'_eq hx
  have h2 := theta''_eq hx
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx
  have hsx : s ^ 2 = x := Real.sq_sqrt hx.le
  have hr : x ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg hx.le, hs, Real.sqrt_eq_rpow]
  have hr1 : x ^ (-(1 / 2 : ℝ) - 1) = s⁻¹ / x := by rw [Real.rpow_sub_one hx.ne', hr]
  have hr2 : x ^ (-(1 / 2 : ℝ) - 1 - 1) = s⁻¹ / x / x := by
    rw [Real.rpow_sub_one hx.ne', Real.rpow_sub_one hx.ne', hr]
  have hr3 : x ^ (1 / 2 : ℝ) = s := by rw [hs, Real.sqrt_eq_rpow]
  unfold Ψ
  rw [h1, h2, hr1, hr2, hr3, hr]
  rw [← hsx]
  have hs0' : s ≠ 0 := hs0.ne'
  field_simp
  ring

/-! ## `Ψ` as a series, and its positivity on `[1, ∞)` -/

/-- The term of `Ψ`. -/
def Ψterm (n : ℤ) (x : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 - 3 * π * (n : ℝ) ^ 2 * x) * Real.exp (-π * (n : ℝ) ^ 2 * x)

theorem hasSum_Ψ {x : ℝ} (hx : 0 < x) : HasSum (fun n : ℤ => Ψterm n x) (Ψ x) := by
  unfold Ψ θ'' θ'
  have h4 := (summable_gterm (c := π ^ 2) 4 hx).hasSum.mul_left (2 * x ^ 2)
  have h2 := (summable_gterm (c := -π) 2 hx).hasSum.mul_left (3 * x)
  refine (h4.add h2).congr_fun ?_
  intro n
  unfold Ψterm gterm
  ring

theorem Ψterm_nonneg {n : ℤ} {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Ψterm n x := by
  unfold Ψterm
  apply mul_nonneg _ (Real.exp_pos _).le
  by_cases hn : n = 0
  · subst hn
    simp
  · have habs : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have hpi := Real.pi_gt_three
    have hA : 0 ≤ π * (n : ℝ) ^ 2 * x := by positivity
    have hnx : 1 ≤ (n : ℝ) ^ 2 * x := by nlinarith
    have hB : 0 ≤ 2 * π * (n : ℝ) ^ 2 * x - 3 := by
      have := mul_le_mul_of_nonneg_left hnx (by linarith : (0 : ℝ) ≤ 2 * π)
      nlinarith
    have key : 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 - 3 * π * (n : ℝ) ^ 2 * x =
        (π * (n : ℝ) ^ 2 * x) * (2 * π * (n : ℝ) ^ 2 * x - 3) := by ring
    rw [key]
    exact mul_nonneg hA hB

theorem Ψterm_one_pos {x : ℝ} (hx : 1 ≤ x) : 0 < Ψterm 1 x := by
  unfold Ψterm
  apply mul_pos _ (Real.exp_pos _)
  have hpi := Real.pi_gt_three
  push_cast
  have key : 2 * π ^ 2 * 1 ^ 4 * x ^ 2 - 3 * π * 1 ^ 2 * x = (π * x) * (2 * π * x - 3) := by ring
  rw [key]
  apply mul_pos (by positivity)
  nlinarith

/-- **`Ψ` is positive on `[1, ∞)`.** -/
theorem Ψ_pos {x : ℝ} (hx : 1 ≤ x) : 0 < Ψ x := by
  rw [← (hasSum_Ψ (by linarith)).tsum_eq]
  exact (hasSum_Ψ (by linarith)).summable.tsum_pos (fun n => Ψterm_nonneg hx) 1 (Ψterm_one_pos hx)

/-! ## The kernel `Φ` -/

/-- **The kernel of the flow**: `Φ(u) = e^{u/2} Ψ(e^{2u})`. -/
def Φ (u : ℝ) : ℝ := Real.exp (u / 2) * Ψ (Real.exp (2 * u))

/-- **`Φ` is even.** -/
theorem Φ_neg (u : ℝ) : Φ (-u) = Φ u := by
  unfold Φ
  have hx : 0 < Real.exp (2 * u) := Real.exp_pos _
  have h1 : Real.exp (2 * -u) = (Real.exp (2 * u))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have h2 : Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by
    rw [Real.rpow_def_of_pos hx, Real.log_exp]
    congr 1
    ring
  rw [h1, Ψ_inv hx, h2, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **`Φ` is positive.** -/
theorem Φ_pos (u : ℝ) : 0 < Φ u := by
  rcases le_or_gt 0 u with hu | hu
  · unfold Φ
    apply mul_pos (Real.exp_pos _)
    apply Ψ_pos
    rw [Real.one_le_exp_iff]
    linarith
  · rw [← Φ_neg]
    unfold Φ
    apply mul_pos (Real.exp_pos _)
    apply Ψ_pos
    rw [Real.one_le_exp_iff]
    linarith

theorem Φ_abs (u : ℝ) : Φ u = Φ |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, Φ_neg]

/-! ## Decay -/

/-- The constant of the decay bound of `Ψ`: `e^π Σ_n n⁴ e^{−π n²}`. -/
def C₄ : ℝ := Real.exp π * ∑' n : ℤ, |(n : ℝ)| ^ 4 * Real.exp (-π * (n : ℝ) ^ 2)

theorem C₄_nonneg : 0 ≤ C₄ :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun n => by positivity)

theorem Ψterm_le {n : ℤ} {x : ℝ} (hx : 1 ≤ x) :
    Ψterm n x ≤ 2 * π ^ 2 * x ^ 2 * Real.exp (-π * x) *
      (Real.exp π * (|(n : ℝ)| ^ 4 * Real.exp (-π * (n : ℝ) ^ 2))) := by
  by_cases hn : n = 0
  · subst hn
    unfold Ψterm
    simp
  · have habs : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have hE : Real.exp (-π * (n : ℝ) ^ 2 * x) ≤
        Real.exp (-π * x) * (Real.exp π * Real.exp (-π * (n : ℝ) ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1))
        (by linarith : (0 : ℝ) ≤ x - 1)
      nlinarith
    have hn4 : |(n : ℝ)| ^ 4 = (n : ℝ) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
    unfold Ψterm
    have h0 : 0 ≤ Real.exp (-π * (n : ℝ) ^ 2 * x) := (Real.exp_pos _).le
    have hdrop : (2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 - 3 * π * (n : ℝ) ^ 2 * x) *
        Real.exp (-π * (n : ℝ) ^ 2 * x) ≤
        2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * x) := by
      apply mul_le_mul_of_nonneg_right _ h0
      have : 0 ≤ 3 * π * (n : ℝ) ^ 2 * x := by positivity
      linarith
    refine hdrop.trans ?_
    rw [hn4]
    have hc : 0 ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 := by positivity
    calc 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * x)
        ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 *
          (Real.exp (-π * x) * (Real.exp π * Real.exp (-π * (n : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hE hc
      _ = 2 * π ^ 2 * x ^ 2 * Real.exp (-π * x) *
          (Real.exp π * ((n : ℝ) ^ 4 * Real.exp (-π * (n : ℝ) ^ 2))) := by ring

/-- **The decay of `Ψ` on `[1, ∞)`.** -/
theorem Ψ_le {x : ℝ} (hx : 1 ≤ x) : Ψ x ≤ 2 * π ^ 2 * C₄ * x ^ 2 * Real.exp (-π * x) := by
  rw [← (hasSum_Ψ (by linarith)).tsum_eq]
  have hsum := (hasSum_Ψ (by linarith)).summable
  have hmaj : Summable (fun n : ℤ => 2 * π ^ 2 * x ^ 2 * Real.exp (-π * x) *
      (Real.exp π * (|(n : ℝ)| ^ 4 * Real.exp (-π * (n : ℝ) ^ 2)))) :=
    ((summable_pow_mul_exp_neg_sq (c := π) Real.pi_pos 4).mul_left (Real.exp π)).mul_left _
  calc ∑' n : ℤ, Ψterm n x
      ≤ ∑' n : ℤ, 2 * π ^ 2 * x ^ 2 * Real.exp (-π * x) *
          (Real.exp π * (|(n : ℝ)| ^ 4 * Real.exp (-π * (n : ℝ) ^ 2))) :=
        Summable.tsum_le_tsum (fun n => Ψterm_le hx) hsum hmaj
    _ = 2 * π ^ 2 * C₄ * x ^ 2 * Real.exp (-π * x) := by
        rw [tsum_mul_left, tsum_mul_left]
        unfold C₄
        ring

/-- **The decay of `Φ`**: `Φ(u) ≤ 2π² C₄ e^{9|u|/2} e^{−π e^{2|u|}}`. -/
theorem Φ_le (u : ℝ) :
    Φ u ≤ 2 * π ^ 2 * C₄ * Real.exp (9 / 2 * |u|) * Real.exp (-π * Real.exp (2 * |u|)) := by
  rw [Φ_abs]
  unfold Φ
  have hx : 1 ≤ Real.exp (2 * |u|) := by
    rw [Real.one_le_exp_iff]
    positivity
  have h := Ψ_le hx
  calc Real.exp (|u| / 2) * Ψ (Real.exp (2 * |u|))
      ≤ Real.exp (|u| / 2) * (2 * π ^ 2 * C₄ * Real.exp (2 * |u|) ^ 2 *
          Real.exp (-π * Real.exp (2 * |u|))) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 2 * π ^ 2 * C₄ * Real.exp (9 / 2 * |u|) * Real.exp (-π * Real.exp (2 * |u|)) := by
        rw [← Real.exp_nat_mul, show (9 / 2 * |u|) = |u| / 2 + (2 : ℕ) * (2 * |u|) by push_cast; ring,
          Real.exp_add]
        ring

theorem quartic_dominates {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (u : ℝ) :
    A * u ^ 2 + B * |u| ≤ (A + B) + (A + B) ^ 2 + u ^ 4 := by
  have h1 : |u| ≤ 1 + u ^ 2 := by
    have := abs_nonneg u
    nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have h2 : (A + B) * u ^ 2 ≤ (A + B) ^ 2 + u ^ 4 := by
    nlinarith [sq_nonneg (A + B - u ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]

/-- **Gaussian domination**: `e^{a u² + b|u|} Φ(u) ≤ K e^{−u²}`. -/
theorem exp_mul_Φ_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : ℝ) :
    Real.exp (a * u ^ 2 + b * |u|) * Φ u ≤
      2 * π ^ 2 * C₄ * Real.exp ((a + 1 + (b + 9 / 2)) + (a + 1 + (b + 9 / 2)) ^ 2) *
        Real.exp (-u ^ 2) := by
  have hΦ := Φ_le u
  have hpi := Real.pi_gt_three
  have hquart : (2 * |u|) ^ 4 / (4 : ℕ).factorial ≤ Real.exp (2 * |u|) :=
    Real.pow_div_factorial_le_exp (2 * |u|) (by positivity) 4
  have hfac : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at hquart
  have hq : 2 * u ^ 4 ≤ π * Real.exp (2 * |u|) := by
    have h1 : (2 * |u|) ^ 4 / 24 = 2 / 3 * u ^ 4 := by
      rw [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num,
        show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
      ring
    rw [h1] at hquart
    have h2 : 0 ≤ Real.exp (2 * |u|) := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hquart (by linarith : (0 : ℝ) ≤ 3)]
  have hdom := quartic_dominates (A := a + 1) (B := b + 9 / 2) (by linarith) (by linarith) u
  have hC : 0 ≤ 2 * π ^ 2 * C₄ := by
    have := C₄_nonneg
    positivity
  calc Real.exp (a * u ^ 2 + b * |u|) * Φ u
      ≤ Real.exp (a * u ^ 2 + b * |u|) *
          (2 * π ^ 2 * C₄ * Real.exp (9 / 2 * |u|) * Real.exp (-π * Real.exp (2 * |u|))) :=
        mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le
    _ = 2 * π ^ 2 * C₄ *
          Real.exp (a * u ^ 2 + b * |u| + 9 / 2 * |u| + -π * Real.exp (2 * |u|)) := by
        simp only [Real.exp_add]
        ring
    _ ≤ 2 * π ^ 2 * C₄ *
          Real.exp ((a + 1 + (b + 9 / 2)) + (a + 1 + (b + 9 / 2)) ^ 2 + -u ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = 2 * π ^ 2 * C₄ * Real.exp ((a + 1 + (b + 9 / 2)) + (a + 1 + (b + 9 / 2)) ^ 2) *
          Real.exp (-u ^ 2) := by
        rw [Real.exp_add]
        ring

/-! ## Continuity and integrability -/

theorem continuousAt_theta'' {x : ℝ} (hx : 0 < x) : ContinuousAt θ'' x :=
  (hasDerivAt_tsum_gterm (π ^ 2) 4 hx).continuousAt

theorem continuousAt_Ψ {x : ℝ} (hx : 0 < x) : ContinuousAt Ψ x := by
  unfold Ψ
  exact ((continuousAt_const.mul (continuousAt_id.pow 2)).mul (continuousAt_theta'' hx)).add
    ((continuousAt_const.mul continuousAt_id).mul (hasDerivAt_theta' hx).continuousAt)

/-- **`Φ` is continuous.** -/
theorem continuous_Φ : Continuous Φ := by
  unfold Φ
  apply Continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2))
  apply continuous_iff_continuousAt.mpr
  intro u
  have hc : Continuous fun u : ℝ => Real.exp (2 * u) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact ContinuousAt.comp (f := fun u => Real.exp (2 * u)) (g := Ψ)
    (continuousAt_Ψ (Real.exp_pos (2 * u))) hc.continuousAt

/-- The Laplace integrand `e^{(s − ½) u} Φ(u)`. -/
def lap (s : ℂ) (u : ℝ) : ℂ := Complex.exp ((s - 1 / 2) * u) * (Φ u : ℂ)

theorem continuous_lap (s : ℂ) : Continuous (lap s) := by
  unfold lap
  exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp continuous_Φ)

theorem norm_lap (s : ℂ) (u : ℝ) : ‖lap s u‖ = Real.exp ((s.re - 1 / 2) * u) * Φ u := by
  unfold lap
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Φ_pos u)]
  congr 2
  simp [Complex.mul_re]

/-- **The Laplace integrand is integrable for every `s`.** -/
theorem integrable_lap (s : ℂ) : Integrable (lap s) := by
  have hK := exp_mul_Φ_le (a := 0) (b := |s.re - 1 / 2|) le_rfl (abs_nonneg _)
  set K := 2 * π ^ 2 * C₄ * Real.exp ((0 + 1 + (|s.re - 1 / 2| + 9 / 2)) +
    (0 + 1 + (|s.re - 1 / 2| + 9 / 2)) ^ 2) with hKdef
  have hg : Integrable (fun u : ℝ => K * Real.exp (-u ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul K |>.congr (by
      refine Filter.Eventually.of_forall fun u => ?_
      simp)
  refine hg.mono' (continuous_lap s).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [norm_lap]
  have h1 : Real.exp ((s.re - 1 / 2) * u) ≤ Real.exp (0 * u ^ 2 + |s.re - 1 / 2| * |u|) := by
    apply Real.exp_le_exp.mpr
    have := abs_mul (s.re - 1 / 2) u
    have := le_abs_self ((s.re - 1 / 2) * u)
    nlinarith
  calc Real.exp ((s.re - 1 / 2) * u) * Φ u
      ≤ Real.exp (0 * u ^ 2 + |s.re - 1 / 2| * |u|) * Φ u :=
        mul_le_mul_of_nonneg_right h1 (Φ_pos u).le
    _ ≤ K * Real.exp (-u ^ 2) := hK u

/-- **The two-sided Laplace transform of `Φ`.** -/
def L (s : ℂ) : ℂ := ∫ u : ℝ, lap s u

/-! ## The substitution `x = e^{2u}` -/

/-- **Substitution `x = e^{2u}` on the whole line**: `∫_ℝ 2 e^{2u} g(e^{2u}) du = ∫_0^∞ g`. -/
theorem integral_comp_exp_two (g : ℝ → ℂ) :
    ∫ u : ℝ, (2 * Real.exp (2 * u)) • g (Real.exp (2 * u)) = ∫ x in Ioi (0 : ℝ), g x := by
  have himg : (fun u : ℝ => Real.exp (2 * u)) '' univ = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact Real.exp_pos _
    · intro hx
      exact ⟨Real.log x / 2, mem_univ _, by
        show Real.exp (2 * (Real.log x / 2)) = x
        rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hx]⟩
  have hderiv : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (2 * u)) (2 * Real.exp (2 * u)) univ u := by
    intro u _
    have := ((hasDerivAt_id' u).const_mul 2).exp
    refine this.hasDerivWithinAt.congr_deriv ?_
    ring
  have hinj : InjOn (fun u : ℝ => Real.exp (2 * u)) univ := by
    intro a _ b _ h
    have := Real.exp_injective h
    linarith
  have := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  rw [himg, setIntegral_univ] at this
  rw [this]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun u => ?_
  simp only
  rw [abs_of_pos (by positivity)]

/-! ## The term integrals: Gamma functions -/

theorem integrableOn_cpow_mul_exp {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (a - 1) * Complex.exp (-(r * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent ha
  have h2 := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => (Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) 0 hr).mpr (by simpa using h)
  have hr0 : (r : ℂ) ^ (a - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast hr.ne'
  have h3 : IntegrableOn (fun x : ℝ => ((r : ℂ) ^ (a - 1))⁻¹ *
      ((Real.exp (-(r * x)) : ℂ) * ((r * x : ℝ) : ℂ) ^ (a - 1))) (Ioi 0) :=
    h2.const_mul _
  refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt hx), Complex.ofReal_exp]
  push_cast
  field_simp

/-- The signed term of `Ψ`: `ε = −1` is `Ψterm`, `ε = 1` its absolute majorant. -/
def Ψterm' (ε : ℝ) (n : ℤ) (x : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 + ε * (3 * π * (n : ℝ) ^ 2 * x)) * Real.exp (-π * (n : ℝ) ^ 2 * x)

theorem Ψterm_eq (n : ℤ) (x : ℝ) : Ψterm n x = Ψterm' (-1) n x := by
  unfold Ψterm Ψterm'
  ring

theorem abs_Ψterm_le {n : ℤ} {x : ℝ} (hx : 0 < x) : |Ψterm n x| ≤ Ψterm' 1 n x := by
  unfold Ψterm Ψterm'
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have h1 : 0 ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 := by positivity
  have h2 : 0 ≤ 3 * π * (n : ℝ) ^ 2 * x := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- The `n`-th term of the Laplace integrand, with sign `ε`. -/
def lapTerm (ε : ℝ) (s : ℂ) (n : ℤ) (u : ℝ) : ℂ :=
  Complex.exp ((s - 1 / 2) * u) * ((Real.exp (u / 2) * Ψterm' ε n (Real.exp (2 * u)) : ℝ) : ℂ)

theorem hasSum_lapTerm (s : ℂ) (u : ℝ) : HasSum (fun n : ℤ => lapTerm (-1) s n u) (lap s u) := by
  unfold lapTerm lap Φ
  have h := (hasSum_Ψ (Real.exp_pos (2 * u))).mul_left (Real.exp (u / 2))
  have h2 := (h.mapL Complex.ofRealCLM).mul_left (Complex.exp ((s - 1 / 2) * u))
  refine h2.congr_fun ?_
  intro n
  simp [Ψterm_eq]

/-- The Mellin-side term. -/
def melTerm (ε : ℝ) (s : ℂ) (n : ℤ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ((x : ℂ) ^ (s / 2 - 1) *
    ((2 * π ^ 2 * (n : ℂ) ^ 4 * (x : ℂ) ^ 2 + (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 * (x : ℂ))) *
      Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ)))))

theorem lapTerm_eq_smul (ε : ℝ) (s : ℂ) (n : ℤ) (u : ℝ) :
    (2 * Real.exp (2 * u)) • melTerm ε s n (Real.exp (2 * u)) = lapTerm ε s n u := by
  unfold melTerm lapTerm Ψterm'
  have hx : ((Real.exp (2 * u) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have hcpow : ((Real.exp (2 * u) : ℝ) : ℂ) ^ (s / 2 - 1) =
      Complex.exp ((s / 2 - 1) * (2 * u)) := by
    rw [Complex.cpow_def_of_ne_zero hx, Complex.ofReal_exp, Complex.log_exp (by simp; linarith [Real.pi_pos])
      (by simp; linarith [Real.pi_pos])]
    push_cast
    ring_nf
  rw [hcpow]
  have hE : Complex.exp (2 * (u : ℂ)) * Complex.exp ((s / 2 - 1) * (2 * u)) =
      Complex.exp ((s - 1 / 2) * u) * Complex.exp ((u : ℂ) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [Complex.real_smul]
  push_cast
  simp only [neg_mul]
  linear_combination
    ((2 * π ^ 2 * (n : ℂ) ^ 4 * Complex.exp (2 * u) ^ 2 + (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 * Complex.exp (2 * u))) *
      Complex.exp (-(π * (n : ℂ) ^ 2 * Complex.exp (2 * u)))) * hE

/-- The value of a term: two Gamma integrals. -/
def termValue (ε : ℝ) (s : ℂ) (n : ℤ) : ℂ :=
  (1 / 2 : ℂ) * (2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((1 / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ (s / 2 + 2) * Complex.Gamma (s / 2 + 2)) +
    (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 *
      ((1 / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ (s / 2 + 1) * Complex.Gamma (s / 2 + 1))))

theorem re_pos_of {s : ℂ} (hs : 1 < s.re) : 0 < (s / 2 + 2).re ∧ 0 < (s / 2 + 1).re := by
  constructor
  · simp only [Complex.add_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
    linarith
  · simp only [Complex.add_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
    norm_num
    linarith

/-- The Mellin-side term, split into its two Gamma integrands. -/
def melTerm2 (ε : ℝ) (s : ℂ) (n : ℤ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((x : ℂ) ^ (s / 2 + 2 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ)))) +
    (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 *
      ((x : ℂ) ^ (s / 2 + 1 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ))))))

theorem melTerm_eqOn (ε : ℝ) (s : ℂ) (n : ℤ) : EqOn (melTerm ε s n) (melTerm2 ε s n) (Ioi 0) := by
  intro x hx
  unfold melTerm melTerm2
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have h2 : (x : ℂ) ^ (s / 2 + 2 - 1) = (x : ℂ) ^ (s / 2 - 1) * (x : ℂ) ^ 2 := by
    rw [show s / 2 + 2 - 1 = (s / 2 - 1) + ((2 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hx0, Complex.cpow_natCast]
  have h1 : (x : ℂ) ^ (s / 2 + 1 - 1) = (x : ℂ) ^ (s / 2 - 1) * (x : ℂ) := by
    rw [show s / 2 + 1 - 1 = (s / 2 - 1) + ((1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hx0, Complex.cpow_natCast, pow_one]
  rw [h2, h1]
  ring

theorem integrableOn_melTerm (ε : ℝ) {s : ℂ} (hs : 1 < s.re) {n : ℤ} (hn : n ≠ 0) :
    IntegrableOn (melTerm ε s n) (Ioi 0) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hr : 0 < π * (n : ℝ) ^ 2 := by positivity
  obtain ⟨hA, hB⟩ := re_pos_of hs
  have h1 : IntegrableOn (fun x : ℝ => 2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((x : ℂ) ^ (s / 2 + 2 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ))))) (Ioi 0) :=
    (integrableOn_cpow_mul_exp hA hr).const_mul _
  have h2 : IntegrableOn (fun x : ℝ => (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 *
      ((x : ℂ) ^ (s / 2 + 1 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ)))))) (Ioi 0) :=
    ((integrableOn_cpow_mul_exp hB hr).const_mul _).const_mul _
  have h3 : IntegrableOn (fun x : ℝ => (1 / 2 : ℂ) * (2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((x : ℂ) ^ (s / 2 + 2 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ)))) +
      (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 *
        ((x : ℂ) ^ (s / 2 + 1 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ))))))) (Ioi 0) :=
    (h1.add h2).const_mul _
  exact IntegrableOn.congr_fun h3 (melTerm_eqOn ε s n).symm measurableSet_Ioi

theorem integral_melTerm (ε : ℝ) {s : ℂ} (hs : 1 < s.re) {n : ℤ} (hn : n ≠ 0) :
    ∫ x in Ioi (0 : ℝ), melTerm ε s n x = termValue ε s n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hr : 0 < π * (n : ℝ) ^ 2 := by positivity
  obtain ⟨hA, hB⟩ := re_pos_of hs
  have hIA := integrableOn_cpow_mul_exp hA hr
  have hIB := integrableOn_cpow_mul_exp hB hr
  have h1 : IntegrableOn (fun x : ℝ => 2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((x : ℂ) ^ (s / 2 + 2 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ))))) (Ioi 0) :=
    hIA.const_mul _
  have h2 : IntegrableOn (fun x : ℝ => (ε : ℂ) * (3 * π * (n : ℂ) ^ 2 *
      ((x : ℂ) ^ (s / 2 + 1 - 1) * Complex.exp (-(((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * (x : ℂ)))))) (Ioi 0) :=
    (hIB.const_mul _).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi (melTerm_eqOn ε s n)]
  unfold melTerm2
  rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hA hr,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hB hr]
  rfl

/-! ## The exponential change of variables, as a diffeomorphism -/

theorem exp_two_image : (fun u : ℝ => Real.exp (2 * u)) '' univ = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    exact Real.exp_pos _
  · intro hx
    exact ⟨Real.log x / 2, mem_univ _, by
      show Real.exp (2 * (Real.log x / 2)) = x
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hx]⟩

theorem exp_two_deriv : ∀ u ∈ (univ : Set ℝ),
    HasDerivWithinAt (fun u : ℝ => Real.exp (2 * u)) (2 * Real.exp (2 * u)) univ u := by
  intro u _
  have := ((hasDerivAt_id' u).const_mul 2).exp
  refine this.hasDerivWithinAt.congr_deriv ?_
  ring

theorem exp_two_injOn : InjOn (fun u : ℝ => Real.exp (2 * u)) univ := by
  intro a _ b _ h
  have := Real.exp_injective h
  linarith

/-- **The term integrand is integrable** for `Re s > 1`. -/
theorem integrable_lapTerm (ε : ℝ) {s : ℂ} (hs : 1 < s.re) (n : ℤ) : Integrable (lapTerm ε s n) := by
  by_cases hn : n = 0
  · subst hn
    have : lapTerm ε s 0 = fun _ => 0 := by
      funext u
      unfold lapTerm Ψterm'
      simp
    rw [this]
    exact integrable_zero _ _ _
  · have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ exp_two_deriv
      exp_two_injOn (melTerm ε s n)).mp (by rw [exp_two_image]; exact integrableOn_melTerm ε hs hn)
    rw [integrableOn_univ] at h
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [abs_of_pos (by positivity), lapTerm_eq_smul]

/-- **The term integral**: `∫ lapTerm ε s n = termValue ε s n` for `n ≠ 0`. -/
theorem integral_lapTerm (ε : ℝ) {s : ℂ} (hs : 1 < s.re) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : ℝ, lapTerm ε s n u = termValue ε s n := by
  rw [← integral_melTerm ε hs hn, ← integral_comp_exp_two]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => (lapTerm_eq_smul ε s n u).symm

theorem lapTerm_zero (ε : ℝ) (s : ℂ) (u : ℝ) : lapTerm ε s 0 u = 0 := by
  unfold lapTerm Ψterm'
  simp

/-! ## The sum of the term integrals is the transform -/

/-- The majorant term is real and nonnegative at real `σ`. -/
theorem lapTerm_one_re (σ : ℝ) (n : ℤ) (u : ℝ) :
    (lapTerm 1 (σ : ℂ) n u).re = Real.exp ((σ - 1 / 2) * u) * (Real.exp (u / 2) * Ψterm' 1 n (Real.exp (2 * u))) := by
  unfold lapTerm
  rw [show ((σ : ℂ) - 1 / 2) * (u : ℂ) = (((σ - 1 / 2) * u : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem norm_lapTerm_le (s : ℂ) (n : ℤ) (u : ℝ) :
    ‖lapTerm (-1) s n u‖ ≤ (lapTerm 1 (s.re : ℂ) n u).re := by
  rw [lapTerm_one_re]
  unfold lapTerm
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by
    simp [Complex.mul_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have := abs_Ψterm_le (n := n) (Real.exp_pos (2 * u))
  rwa [Ψterm_eq] at this

theorem lapTerm_one_re_nonneg (σ : ℝ) (n : ℤ) (u : ℝ) : 0 ≤ (lapTerm 1 (σ : ℂ) n u).re := by
  rw [lapTerm_one_re]
  unfold Ψterm'
  positivity

/-- The majorant's value at real `σ`, as a real number. -/
theorem termValue_one_re {σ : ℝ} (hσ : 1 < σ) {n : ℤ} (hn : n ≠ 0) :
    (termValue 1 (σ : ℂ) n).re =
      (1 / 2 : ℝ) * (2 * π ^ 2 * (n : ℝ) ^ 4 *
          ((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 2) * Real.Gamma (σ / 2 + 2)) +
        3 * π * (n : ℝ) ^ 2 * ((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 1) * Real.Gamma (σ / 2 + 1))) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hr : 0 ≤ 1 / (π * (n : ℝ) ^ 2) := by positivity
  unfold termValue
  have e1 : ((1 : ℂ) / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ ((σ : ℂ) / 2 + 2) =
      (((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hr]
    push_cast
    ring_nf
  have e2 : ((1 : ℂ) / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ ((σ : ℂ) / 2 + 1) =
      (((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hr]
    push_cast
    ring_nf
  have g1 : Complex.Gamma ((σ : ℂ) / 2 + 2) = ((Real.Gamma (σ / 2 + 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    push_cast
    ring_nf
  have g2 : Complex.Gamma ((σ : ℂ) / 2 + 1) = ((Real.Gamma (σ / 2 + 1) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    push_cast
    ring_nf
  rw [e1, e2, g1, g2]
  have : ((1 / 2 : ℂ) * (2 * π ^ 2 * (n : ℂ) ^ 4 *
      ((((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 2) : ℝ) : ℂ) * ((Real.Gamma (σ / 2 + 2) : ℝ) : ℂ)) +
      ((1 : ℝ) : ℂ) * (3 * π * (n : ℂ) ^ 2 *
        ((((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 1) : ℝ) : ℂ) * ((Real.Gamma (σ / 2 + 1) : ℝ) : ℂ))))) =
      (((1 / 2 : ℝ) * (2 * π ^ 2 * (n : ℝ) ^ 4 *
          ((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 2) * Real.Gamma (σ / 2 + 2)) +
        3 * π * (n : ℝ) ^ 2 * ((1 / (π * (n : ℝ) ^ 2)) ^ (σ / 2 + 1) * Real.Gamma (σ / 2 + 1))) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.ofReal_re]

theorem continuous_Ψterm' (ε : ℝ) (n : ℤ) : Continuous (Ψterm' ε n) := by
  unfold Ψterm'
  fun_prop

theorem continuous_lapTerm (ε : ℝ) (s : ℂ) (n : ℤ) : Continuous (lapTerm ε s n) := by
  unfold lapTerm
  apply Continuous.mul
  · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  · apply Complex.continuous_ofReal.comp
    apply Continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2))
    exact (continuous_Ψterm' ε n).comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

/-- The constant of the majorant's value. -/
def Cmaj (σ : ℝ) : ℝ := (1 / 2 : ℝ) * π ^ (-(σ / 2)) * (2 * Real.Gamma (σ / 2 + 2) + 3 * Real.Gamma (σ / 2 + 1))

/-- **The majorant's value is `Cmaj σ · |n|^{−σ}`.** -/
theorem termValue_one_re_eq {σ : ℝ} (hσ : 1 < σ) {n : ℤ} (hn : n ≠ 0) :
    (termValue 1 (σ : ℂ) n).re = Cmaj σ * |(n : ℝ)| ^ (-σ) := by
  rw [termValue_one_re hσ hn]
  set a : ℝ := |(n : ℝ)| with ha
  have ha0 : 0 < a := by
    rw [ha]
    exact abs_pos.mpr (by exact_mod_cast hn)
  have hn2 : (n : ℝ) ^ 2 = a ^ 2 := (sq_abs _).symm
  have hn4 : (n : ℝ) ^ 4 = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hn2, ← pow_mul]
  have hpow : ∀ p : ℝ, (1 / (π * a ^ 2)) ^ p = (π ^ p)⁻¹ * (a ^ (2 * p))⁻¹ := by
    intro p
    rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le (by positivity),
      mul_inv, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha0.le]
    push_cast
    ring_nf
  rw [hn4, hn2, hpow, hpow]
  have e1 : a ^ (2 * (σ / 2 + 2)) = a ^ σ * a ^ 4 := by
    rw [show 2 * (σ / 2 + 2) = σ + (4 : ℕ) by push_cast; ring, Real.rpow_add ha0, Real.rpow_natCast]
  have e2 : a ^ (2 * (σ / 2 + 1)) = a ^ σ * a ^ 2 := by
    rw [show 2 * (σ / 2 + 1) = σ + (2 : ℕ) by push_cast; ring, Real.rpow_add ha0, Real.rpow_natCast]
  have e3 : π ^ (σ / 2 + 2) = π ^ (σ / 2) * π ^ 2 := by
    rw [show σ / 2 + 2 = σ / 2 + (2 : ℕ) by push_cast; ring, Real.rpow_add Real.pi_pos, Real.rpow_natCast]
  have e4 : π ^ (σ / 2 + 1) = π ^ (σ / 2) * π := by
    rw [Real.rpow_add_one Real.pi_pos.ne']
  have e5 : a ^ (-σ) = (a ^ σ)⁻¹ := Real.rpow_neg ha0.le σ
  have e6 : π ^ (-(σ / 2)) = (π ^ (σ / 2))⁻¹ := Real.rpow_neg Real.pi_pos.le _
  rw [e1, e2, e3, e4]
  unfold Cmaj
  rw [e5, e6]
  have hσ0 : a ^ σ ≠ 0 := (Real.rpow_pos_of_pos ha0 σ).ne'
  have hπ0 : π ^ (σ / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp

theorem Cmaj_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ Cmaj σ := by
  unfold Cmaj
  have h1 : 0 < Real.Gamma (σ / 2 + 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (σ / 2 + 1) := Real.Gamma_pos_of_pos (by linarith)
  positivity

/-- The majorant's values are summable. -/
theorem summable_termValue_one_re {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ => (termValue 1 (σ : ℂ) n).re) := by
  refine ((Real.summable_abs_int_rpow hσ).mul_left (Cmaj σ)).of_nonneg_of_le ?_ ?_
  · intro n
    by_cases hn : n = 0
    · subst hn
      unfold termValue
      simp
    · rw [termValue_one_re_eq hσ hn]
      exact mul_nonneg (Cmaj_nonneg hσ) (Real.rpow_nonneg (abs_nonneg _) _)
  · intro n
    by_cases hn : n = 0
    · subst hn
      unfold termValue
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_mul, add_zero, Complex.zero_re, abs_zero, le_refl]
      exact mul_nonneg (Cmaj_nonneg hσ) (Real.rpow_nonneg le_rfl _)
    · rw [termValue_one_re_eq hσ hn]

/-- **The norm of a term integral is at most the majorant's value.** -/
theorem norm_integral_lapTerm_le {s : ℂ} (hs : 1 < s.re) (n : ℤ) :
    ‖∫ u : ℝ, lapTerm (-1) s n u‖ ≤ (termValue 1 (s.re : ℂ) n).re := by
  by_cases hn : n = 0
  · subst hn
    simp only [lapTerm_zero, integral_zero, norm_zero]
    unfold termValue
    simp
  · have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
    have hint := integrable_lapTerm 1 hs' n
    calc ‖∫ u : ℝ, lapTerm (-1) s n u‖ ≤ ∫ u : ℝ, ‖lapTerm (-1) s n u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, (lapTerm 1 (s.re : ℂ) n u).re :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hint.re
            (Filter.Eventually.of_forall fun u => norm_lapTerm_le s n u)
      _ = (∫ u : ℝ, lapTerm 1 (s.re : ℂ) n u).re := by
          have := Complex.reCLM.integral_comp_comm hint
          simpa using this
      _ = (termValue 1 (s.re : ℂ) n).re := by rw [integral_lapTerm 1 hs' hn]

theorem lintegral_lapTerm_le {s : ℂ} (hs : 1 < s.re) (n : ℤ) :
    ∫⁻ u : ℝ, ‖lapTerm (-1) s n u‖ₑ ≤ ENNReal.ofReal ((termValue 1 (s.re : ℂ) n).re) := by
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hint := integrable_lapTerm 1 hs' n
  calc ∫⁻ u : ℝ, ‖lapTerm (-1) s n u‖ₑ
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal ((lapTerm 1 (s.re : ℂ) n u).re) := by
        apply lintegral_mono
        intro u
        simp only
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (norm_lapTerm_le s n u)
    _ = ENNReal.ofReal (∫ u : ℝ, (lapTerm 1 (s.re : ℂ) n u).re) :=
        (ofReal_integral_eq_lintegral_ofReal hint.re
          (Filter.Eventually.of_forall fun u => lapTerm_one_re_nonneg _ n u)).symm
    _ = ENNReal.ofReal ((termValue 1 (s.re : ℂ) n).re) := by
        congr 1
        by_cases hn : n = 0
        · subst hn
          simp only [lapTerm_zero, Complex.zero_re, integral_zero]
          unfold termValue
          simp
        · have := Complex.reCLM.integral_comp_comm hint
          simp only [Complex.reCLM_apply] at this
          rw [this, integral_lapTerm 1 hs' hn]

/-- **The transform is the sum of the term integrals**, for `Re s > 1`. -/
theorem hasSum_integral_lapTerm {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => ∫ u : ℝ, lapTerm (-1) s n u) (L s) := by
  have hsum : Summable (fun n : ℤ => ∫ u : ℝ, lapTerm (-1) s n u) :=
    (summable_termValue_one_re hs).of_norm_bounded (norm_integral_lapTerm_le hs)
  have hfin : ∑' n : ℤ, ∫⁻ u : ℝ, ‖lapTerm (-1) s n u‖ₑ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∑' n : ℤ, ENNReal.ofReal ((termValue 1 (s.re : ℂ) n).re))
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => ?_) (summable_termValue_one_re hs)]
      · exact ENNReal.ofReal_ne_top
      · by_cases hn : n = 0
        · subst hn
          unfold termValue
          simp
        · rw [termValue_one_re_eq hs hn]
          exact mul_nonneg (Cmaj_nonneg hs) (Real.rpow_nonneg (abs_nonneg _) _)
    · exact ENNReal.tsum_le_tsum (lintegral_lapTerm_le hs)
  have h := integral_tsum (fun n => (continuous_lapTerm (-1) s n).aestronglyMeasurable) hfin
  have hL : L s = ∫ u : ℝ, ∑' n : ℤ, lapTerm (-1) s n u := by
    unfold L
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => (hasSum_lapTerm s u).tsum_eq.symm
  rw [hL, h]
  exact hsum.hasSum

/-! ## The transform is entire -/

/-- The derivative integrand `u e^{(s−½)u} Φ(u)`. -/
def lap' (s : ℂ) (u : ℝ) : ℂ := (u : ℂ) * lap s u

theorem continuous_lap' (s : ℂ) : Continuous (lap' s) :=
  Complex.continuous_ofReal.mul (continuous_lap s)

theorem hasDerivAt_lap (u : ℝ) (s : ℂ) : HasDerivAt (fun z => lap z u) (lap' s u) s := by
  unfold lap' lap
  have h : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (u : ℂ)) ((u : ℂ)) s := by
    have := ((hasDerivAt_id' s).sub_const (1 / 2 : ℂ)).mul_const (u : ℂ)
    simpa using this
  have := (h.cexp).mul_const ((Φ u : ℝ) : ℂ)
  refine this.congr_deriv ?_
  ring

theorem norm_lap'_le {s₀ s : ℂ} (hs : s ∈ Metric.ball s₀ 1) (u : ℝ) :
    ‖lap' s u‖ ≤ Real.exp (0 * u ^ 2 + (|s₀.re| + 5 / 2) * |u|) * Φ u := by
  unfold lap'
  rw [norm_mul, norm_lap, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|, abs_nonneg u]
  have hre : |s.re - s₀.re| < 1 := by
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [Metric.mem_ball, dist_eq_norm] at hs
    rw [Complex.sub_re] at h
    linarith
  have h2 : |s.re - 1 / 2| ≤ |s₀.re| + 3 / 2 := by
    have := abs_sub_abs_le_abs_sub (s.re) (s₀.re)
    have := abs_sub (s.re) (1 / 2 : ℝ)
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith [abs_abs (s₀.re), abs_sub_abs_le_abs_sub s.re s₀.re]
  have h3 : (s.re - 1 / 2) * u ≤ (|s₀.re| + 3 / 2) * |u| := by
    calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
      _ = |s.re - 1 / 2| * |u| := abs_mul _ _
      _ ≤ (|s₀.re| + 3 / 2) * |u| := mul_le_mul_of_nonneg_right h2 (abs_nonneg u)
  have hΦ := (Φ_pos u).le
  calc |u| * (Real.exp ((s.re - 1 / 2) * u) * Φ u)
      ≤ Real.exp |u| * (Real.exp ((|s₀.re| + 3 / 2) * |u|) * Φ u) := by
        apply mul_le_mul h1 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h3) hΦ
    _ = Real.exp (0 * u ^ 2 + (|s₀.re| + 5 / 2) * |u|) * Φ u := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The transform is differentiable at every point.** -/
theorem hasDerivAt_L (s₀ : ℂ) : HasDerivAt L (∫ u : ℝ, lap' s₀ u) s₀ := by
  have hK := exp_mul_Φ_le (a := 0) (b := |s₀.re| + 5 / 2) le_rfl (by positivity)
  set K := 2 * π ^ 2 * C₄ * Real.exp ((0 + 1 + (|s₀.re| + 5 / 2 + 9 / 2)) +
    (0 + 1 + (|s₀.re| + 5 / 2 + 9 / 2)) ^ 2) with hKdef
  have hbound : Integrable (fun u : ℝ => K * Real.exp (-u ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul K |>.congr (by
      refine Filter.Eventually.of_forall fun u => ?_
      simp)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun z u => lap z u)
    (F' := fun z u => lap' z u) (x₀ := s₀) (bound := fun u => K * Real.exp (-u ^ 2))
    (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun z => (continuous_lap z).aestronglyMeasurable)
    (integrable_lap s₀) (continuous_lap' s₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u z hz => (norm_lap'_le hz u).trans (hK u))
    hbound (Filter.Eventually.of_forall fun u z _ => hasDerivAt_lap u z)
  exact h.2

theorem differentiable_L : Differentiable ℂ L := fun s => (hasDerivAt_L s).differentiableAt

/-! ## The sum of the term values is `ξ` -/

theorem cpow_ofReal_pos_ne_zero {r : ℝ} (hr : 0 < r) (w : ℂ) : ((r : ℝ) : ℂ) ^ w ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast hr.ne'

/-- The term value at `ε = −1`, `n ≠ 0`: `¼ s(s−1) π^{−s/2} Γ(s/2) |n|^{−s}`. -/
theorem termValue_neg_one_eq {s : ℂ} (hs : 1 < s.re) {n : ℤ} (hn : n ≠ 0) :
    termValue (-1) s n = (1 / 4 : ℂ) * (s * (s - 1)) *
      ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) * (((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
  set a : ℝ := |(n : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr (by exact_mod_cast hn)
  have hn2 : (n : ℂ) ^ 2 = (a : ℂ) ^ 2 := by
    rw [ha, ← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
    push_cast
    rfl
  have hn4 : (n : ℂ) ^ 4 = (a : ℂ) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hn2, ← pow_mul]
  have hbase : ((1 : ℂ) / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) = (((π * a ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [one_div, ha, sq_abs]
  have harg : (((π * a ^ 2 : ℝ) : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  have hcp : ∀ w : ℂ, (((π * a ^ 2 : ℝ) : ℂ))⁻¹ ^ w = ((π : ℂ) ^ w * (a : ℂ) ^ (2 * w))⁻¹ := by
    intro w
    rw [Complex.inv_cpow _ _ harg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le
      (by positivity), Complex.ofReal_pow]
    congr 2
    have him : (Complex.log (a : ℂ) * ((2 : ℕ) : ℂ)).im = 0 := by
      simp [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg ha0.le]
    rw [show (2 : ℂ) * w = ((2 : ℕ) : ℂ) * w by norm_num, Complex.cpow_mul, Complex.cpow_natCast]
    · rw [him]
      linarith [Real.pi_pos]
    · rw [him]
      exact Real.pi_pos.le
  have hs0 : s / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 : s / 2 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hG2 : Complex.Gamma (s / 2 + 2) = (s / 2 + 1) * ((s / 2) * Complex.Gamma (s / 2)) := by
    rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring, Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0]
  have hG1 : Complex.Gamma (s / 2 + 1) = (s / 2) * Complex.Gamma (s / 2) := Complex.Gamma_add_one _ hs0
  unfold termValue
  rw [hn4, hn2, hbase, hcp, hcp, hG2, hG1]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have e1 : (π : ℂ) ^ (s / 2 + 2) = (π : ℂ) ^ (s / 2) * (π : ℂ) ^ 2 := by
    rw [show s / 2 + 2 = s / 2 + ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_add _ _ hπ, Complex.cpow_natCast]
  have e2 : (π : ℂ) ^ (s / 2 + 1) = (π : ℂ) ^ (s / 2) * (π : ℂ) := by
    rw [show s / 2 + 1 = s / 2 + ((1 : ℕ) : ℂ) by norm_num, Complex.cpow_add _ _ hπ, Complex.cpow_natCast, pow_one]
  have e3 : (a : ℂ) ^ (2 * (s / 2 + 2)) = (a : ℂ) ^ s * (a : ℂ) ^ 4 := by
    rw [show 2 * (s / 2 + 2) = s + ((4 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_add _ _ ha', Complex.cpow_natCast]
  have e4 : (a : ℂ) ^ (2 * (s / 2 + 1)) = (a : ℂ) ^ s * (a : ℂ) ^ 2 := by
    rw [show 2 * (s / 2 + 1) = s + ((2 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_add _ _ ha', Complex.cpow_natCast]
  have e5 : (π : ℂ) ^ (-s / 2) = ((π : ℂ) ^ (s / 2))⁻¹ := by
    rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg]
  have e6 : (a : ℂ) ^ (-s) = ((a : ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
  rw [e1, e2, e3, e4, e5, e6]
  have hP : (π : ℂ) ^ (s / 2) ≠ 0 := cpow_ofReal_pos_ne_zero Real.pi_pos _
  have hA : (a : ℂ) ^ s ≠ 0 := cpow_ofReal_pos_ne_zero ha0 _
  push_cast
  field_simp
  ring

/-- **The sum of the term values is `ξ(s)`**, for `Re s > 1`. -/
theorem hasSum_termValue {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => termValue (-1) s n) (riemannXi s) := by
  set c : ℂ := (1 / 4 : ℂ) * (s * (s - 1)) * ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) with hc
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  -- the zeta series over ℕ, with its zero term
  have hζ : HasSum (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    exact (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  have hζ' : HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ s) (riemannZeta s) := by
    have h := (hasSum_nat_add_iff' (f := fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ s) 1).mpr hζ
    simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow hs0, div_zero, sub_zero] at h
    refine h.congr_fun ?_
    intro k
    push_cast
    rfl
  -- the term values along ℕ and along the negatives
  have h1 : HasSum (fun k : ℕ => termValue (-1) s (k : ℤ)) (c * riemannZeta s) := by
    refine (hζ.mul_left c).congr_fun ?_
    intro k
    by_cases hk : k = 0
    · subst hk
      unfold termValue
      simp [Complex.zero_cpow hs0]
    · rw [termValue_neg_one_eq hs (by exact_mod_cast hk)]
      have : ((|((k : ℤ) : ℝ)| : ℝ) : ℂ) = (k : ℂ) := by
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]
        simp
      rw [this, Complex.cpow_neg, hc]
      ring
  have h2 : HasSum (fun k : ℕ => termValue (-1) s (-((k : ℤ) + 1))) (c * riemannZeta s) := by
    refine (hζ'.mul_left c).congr_fun ?_
    intro k
    rw [termValue_neg_one_eq hs (by omega)]
    have : ((|((-((k : ℤ) + 1) : ℤ) : ℝ)| : ℝ) : ℂ) = (k : ℂ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
      push_cast
      rfl
    rw [this, Complex.cpow_neg, hc]
    ring
  have h := HasSum.of_nat_of_neg_add_one h1 h2
  -- identify the sum with ξ
  have hΛ : completedRiemannZeta s = (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
    have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have := riemannZeta_def_of_ne_zero hs0
    rw [eq_div_iff hG] at this
    rw [← this, Complex.Gammaℝ_def]
    ring
  have hξ : riemannXi s = c * riemannZeta s + c * riemannZeta s := by
    unfold riemannXi
    have h₀ := completedRiemannZeta_eq s
    have hs1 : (1 : ℂ) - s ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
      rw [h₀]
      ring
    rw [this, hΛ, hc]
    field_simp
    ring
  rw [hξ]
  exact h

/-- **The representation on `Re s > 1`: `L(s) = ξ(s)`.** -/
theorem L_eq_riemannXi {s : ℂ} (hs : 1 < s.re) : L s = riemannXi s := by
  have h1 := hasSum_integral_lapTerm hs
  have h2 : HasSum (fun n : ℤ => ∫ u : ℝ, lapTerm (-1) s n u) (riemannXi s) := by
    refine (hasSum_termValue hs).congr_fun ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [lapTerm_zero, integral_zero]
      unfold termValue
      simp
    · exact integral_lapTerm (-1) hs hn
  exact h1.unique h2

/-- **`ξ(s) = ∫ e^{(s − ½)u} Φ(u) du` for every `s`.** -/
theorem riemannXi_eq_L (s : ℂ) : riemannXi s = L s := by
  have hξ : AnalyticOnNhd ℂ riemannXi univ := fun z _ => differentiable_riemannXi.analyticAt z
  have hL : AnalyticOnNhd ℂ L univ := fun z _ => differentiable_L.analyticAt z
  have hev : riemannXi =ᶠ[𝓝 (2 : ℂ)] L := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact (L_eq_riemannXi hz).symm
  exact (hξ.eqOn_of_preconnected_of_eventuallyEq hL isPreconnected_univ (mem_univ 2) hev) (mem_univ s)

/-! ## The derivative ladder of the transform -/

/-- The `m`-th moment integrand `u^m e^{(s−½)u} Φ(u)`. -/
def lapM (m : ℕ) (s : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ m * lap s u

/-- The `m`-th moment transform. -/
def LM (m : ℕ) (s : ℂ) : ℂ := ∫ u : ℝ, lapM m s u

theorem continuous_lapM (m : ℕ) (s : ℂ) : Continuous (lapM m s) :=
  (Complex.continuous_ofReal.pow m).mul (continuous_lap s)

theorem norm_lapM (m : ℕ) (s : ℂ) (u : ℝ) :
    ‖lapM m s u‖ = |u| ^ m * (Real.exp ((s.re - 1 / 2) * u) * Φ u) := by
  unfold lapM
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_lap]

theorem hasDerivAt_lapM (m : ℕ) (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => lapM m z u) (lapM (m + 1) s u) s := by
  unfold lapM
  have := (hasDerivAt_lap u s).const_mul ((u : ℂ) ^ m)
  refine this.congr_deriv ?_
  unfold lap'
  ring

/-- The bound of the `m`-th moment integrand on a unit ball of parameters. -/
theorem norm_lapM_le {m : ℕ} {s₀ s : ℂ} (hs : s ∈ Metric.ball s₀ 1) (u : ℝ) :
    ‖lapM m s u‖ ≤ Real.exp (0 * u ^ 2 + (|s₀.re| + 3 / 2 + m) * |u|) * Φ u := by
  rw [norm_lapM]
  have h1 : |u| ^ m ≤ Real.exp (m * |u|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg u) (by linarith [Real.add_one_le_exp |u|, abs_nonneg u]) m
  have hre : |s.re - s₀.re| < 1 := by
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [Metric.mem_ball, dist_eq_norm] at hs
    rw [Complex.sub_re] at h
    linarith
  have h2 : |s.re - 1 / 2| ≤ |s₀.re| + 3 / 2 := by
    have := abs_sub (s.re) (1 / 2 : ℝ)
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith [abs_sub_abs_le_abs_sub s.re s₀.re]
  have h3 : (s.re - 1 / 2) * u ≤ (|s₀.re| + 3 / 2) * |u| := by
    calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
      _ = |s.re - 1 / 2| * |u| := abs_mul _ _
      _ ≤ (|s₀.re| + 3 / 2) * |u| := mul_le_mul_of_nonneg_right h2 (abs_nonneg u)
  have hΦ := (Φ_pos u).le
  calc |u| ^ m * (Real.exp ((s.re - 1 / 2) * u) * Φ u)
      ≤ Real.exp (m * |u|) * (Real.exp ((|s₀.re| + 3 / 2) * |u|) * Φ u) := by
        apply mul_le_mul h1 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h3) hΦ
    _ = Real.exp (0 * u ^ 2 + (|s₀.re| + 3 / 2 + m) * |u|) * Φ u := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem integrable_lapM (m : ℕ) (s : ℂ) : Integrable (lapM m s) := by
  have hK := exp_mul_Φ_le (a := 0) (b := |s.re| + 3 / 2 + m) le_rfl (by positivity)
  set K := 2 * π ^ 2 * C₄ * Real.exp ((0 + 1 + (|s.re| + 3 / 2 + m + 9 / 2)) +
    (0 + 1 + (|s.re| + 3 / 2 + m + 9 / 2)) ^ 2) with hKdef
  have hg : Integrable (fun u : ℝ => K * Real.exp (-u ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul K |>.congr (by
      refine Filter.Eventually.of_forall fun u => ?_
      simp)
  refine hg.mono' (continuous_lapM m s).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  exact (norm_lapM_le (Metric.mem_ball_self one_pos) u).trans (hK u)

/-- **The moment transforms form a derivative ladder.** -/
theorem hasDerivAt_LM (m : ℕ) (s₀ : ℂ) : HasDerivAt (LM m) (LM (m + 1) s₀) s₀ := by
  have hK := exp_mul_Φ_le (a := 0) (b := |s₀.re| + 3 / 2 + (m + 1 : ℕ)) le_rfl (by positivity)
  set K := 2 * π ^ 2 * C₄ * Real.exp ((0 + 1 + (|s₀.re| + 3 / 2 + (m + 1 : ℕ) + 9 / 2)) +
    (0 + 1 + (|s₀.re| + 3 / 2 + (m + 1 : ℕ) + 9 / 2)) ^ 2) with hKdef
  have hbound : Integrable (fun u : ℝ => K * Real.exp (-u ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul K |>.congr (by
      refine Filter.Eventually.of_forall fun u => ?_
      simp)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z u => lapM m z u) (F' := fun z u => lapM (m + 1) z u) (x₀ := s₀)
    (bound := fun u => K * Real.exp (-u ^ 2)) (s := Metric.ball s₀ 1)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun z => (continuous_lapM m z).aestronglyMeasurable)
    (integrable_lapM m s₀) (continuous_lapM (m + 1) s₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u z hz => (norm_lapM_le hz u).trans (hK u))
    hbound (Filter.Eventually.of_forall fun u z _ => hasDerivAt_lapM m u z)
  exact h.2

theorem LM_zero : LM 0 = L := by
  funext s
  unfold LM L lapM
  simp

/-- **`L^{(m)} = LM m`.** -/
theorem iteratedDeriv_L (m : ℕ) : iteratedDeriv m L = LM m := by
  induction m with
  | zero => simp [LM_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (hasDerivAt_LM m s).deriv

/-! ## The flow identity -/

/-- The flowed integrand `e^{−t u²} e^{(z−½)u} Φ(u)`. -/
def flowLap (t : ℝ) (z : ℂ) (u : ℝ) : ℂ := Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) * lap z u

theorem hasSum_flow_series (t : ℝ) (z : ℂ) (u : ℝ) :
    HasSum (fun k : ℕ => ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u) (flowLap t z u) := by
  unfold flowLap lapM
  have h := NormedSpace.expSeries_div_hasSum_exp (-(t : ℂ) * (u : ℂ) ^ 2)
  rw [← Complex.exp_eq_exp_ℂ] at h
  refine (h.mul_right (lap z u)).congr_fun ?_
  intro k
  rw [mul_pow, pow_mul]
  ring

theorem heatTerm_L (t : ℝ) (z : ℂ) (k : ℕ) :
    heatTerm t L z k = ∫ u : ℝ, ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u := by
  unfold heatTerm
  rw [iteratedDeriv_L, integral_const_mul]
  rfl

theorem norm_flow_term (t : ℝ) (z : ℂ) (k : ℕ) (u : ℝ) :
    ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u‖ =
      (|t| * u ^ 2) ^ k / (k.factorial : ℝ) * ‖lap z u‖ := by
  unfold lapM
  rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs,
    mul_pow]
  ring

theorem hasSum_norm_flow (t : ℝ) (z : ℂ) (u : ℝ) :
    HasSum (fun k : ℕ => (|t| * u ^ 2) ^ k / (k.factorial : ℝ) * ‖lap z u‖)
      (Real.exp (|t| * u ^ 2) * ‖lap z u‖) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (|t| * u ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.mul_right _

theorem flow_dominant (t : ℝ) (z : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ Integrable (fun u : ℝ => K * Real.exp (-u ^ 2)) ∧
      ∀ u, Real.exp (|t| * u ^ 2) * ‖lap z u‖ ≤ K * Real.exp (-u ^ 2) := by
  have hK := exp_mul_Φ_le (a := |t|) (b := |z.re - 1 / 2|) (abs_nonneg _) (abs_nonneg _)
  set K := 2 * π ^ 2 * C₄ * Real.exp ((|t| + 1 + (|z.re - 1 / 2| + 9 / 2)) +
    (|t| + 1 + (|z.re - 1 / 2| + 9 / 2)) ^ 2) with hKdef
  refine ⟨K, ?_, ?_, ?_⟩
  · have := C₄_nonneg
    rw [hKdef]
    positivity
  · exact (integrable_exp_neg_mul_sq one_pos).const_mul K |>.congr (by
      refine Filter.Eventually.of_forall fun u => ?_
      simp)
  · intro u
    rw [norm_lap]
    have h1 : Real.exp ((z.re - 1 / 2) * u) ≤ Real.exp (|z.re - 1 / 2| * |u|) := by
      apply Real.exp_le_exp.mpr
      calc (z.re - 1 / 2) * u ≤ |(z.re - 1 / 2) * u| := le_abs_self _
        _ = |z.re - 1 / 2| * |u| := abs_mul _ _
    calc Real.exp (|t| * u ^ 2) * (Real.exp ((z.re - 1 / 2) * u) * Φ u)
        ≤ Real.exp (|t| * u ^ 2) * (Real.exp (|z.re - 1 / 2| * |u|) * Φ u) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right h1 (Φ_pos u).le
      _ = Real.exp (|t| * u ^ 2 + |z.re - 1 / 2| * |u|) * Φ u := by
          rw [Real.exp_add]
          ring
      _ ≤ K * Real.exp (-u ^ 2) := hK u

/-- **The flow identity for the transform: `heatE t L z = ∫ e^{−t u²} e^{(z−½)u} Φ(u) du`.** -/
theorem heatE_L (t : ℝ) (z : ℂ) : heatE t L z = ∫ u : ℝ, flowLap t z u := by
  obtain ⟨K, hK0, hbound, hdom⟩ := flow_dominant t z
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun u : ℝ => ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u) volume :=
    fun k => (continuous_const.mul (continuous_lapM _ z)).aestronglyMeasurable
  have hpt : ∀ u : ℝ, ∑' k : ℕ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u‖ₑ =
      ENNReal.ofReal (Real.exp (|t| * u ^ 2) * ‖lap z u‖) := by
    intro u
    rw [← (hasSum_norm_flow t z u).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (hasSum_norm_flow t z u).summable]
    apply tsum_congr
    intro k
    rw [← ofReal_norm_eq_enorm, norm_flow_term]
  have hfin : ∑' k : ℕ, ∫⁻ u : ℝ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun k => (hmeas k).enorm)]
    have hcongr : ∫⁻ u : ℝ, ∑' k : ℕ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * lapM (2 * k) z u‖ₑ =
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (|t| * u ^ 2) * ‖lap z u‖) :=
      lintegral_congr fun u => hpt u
    rw [hcongr]
    apply ne_top_of_le_ne_top (b := ∫⁻ u : ℝ, ENNReal.ofReal (K * Real.exp (-u ^ 2)))
    · rw [← ofReal_integral_eq_lintegral_ofReal hbound
        (Filter.Eventually.of_forall fun u => by positivity)]
      exact ENNReal.ofReal_ne_top
    · exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hdom u)
  have h := integral_tsum hmeas hfin
  unfold heatE
  simp_rw [heatTerm_L]
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => (hasSum_flow_series t z u).tsum_eq

/-- **The flow identity for `ξ`.** -/
theorem heatE_riemannXi (t : ℝ) (z : ℂ) : heatE t riemannXi z = ∫ u : ℝ, flowLap t z u := by
  have : riemannXi = L := funext riemannXi_eq_L
  rw [this, heatE_L]

/-- The flowed integrand at the centre is real and positive. -/
theorem flowLap_half (t : ℝ) (u : ℝ) :
    flowLap t (1 / 2) u = ((Real.exp (-t * u ^ 2) * Φ u : ℝ) : ℂ) := by
  unfold flowLap lap
  push_cast
  rw [sub_self, zero_mul, Complex.exp_zero, one_mul]

theorem integrable_flow_half (t : ℝ) : Integrable (fun u : ℝ => Real.exp (-t * u ^ 2) * Φ u) := by
  obtain ⟨K, hK0, hbound, hdom⟩ := flow_dominant t (1 / 2)
  refine hbound.mono' ((Real.continuous_exp.comp (by fun_prop)).mul continuous_Φ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Φ_pos u))]
  have h1 : Real.exp (-t * u ^ 2) ≤ Real.exp (|t| * u ^ 2) := by
    apply Real.exp_le_exp.mpr
    have := neg_abs_le t
    nlinarith [sq_nonneg u]
  have h2 : ‖lap (1 / 2) u‖ = Φ u := by
    rw [norm_lap]
    simp
  calc Real.exp (-t * u ^ 2) * Φ u ≤ Real.exp (|t| * u ^ 2) * Φ u :=
        mul_le_mul_of_nonneg_right h1 (Φ_pos u).le
    _ = Real.exp (|t| * u ^ 2) * ‖lap (1 / 2) u‖ := by rw [h2]
    _ ≤ K * Real.exp (-u ^ 2) := hdom u

/-- **The centre value of the flow is positive at every time.** -/
theorem heatE_riemannXi_half_pos (t : ℝ) :
    ∃ v : ℝ, 0 < v ∧ heatE t riemannXi (1 / 2) = (v : ℂ) := by
  refine ⟨∫ u : ℝ, Real.exp (-t * u ^ 2) * Φ u, ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => (mul_pos (Real.exp_pos _) (Φ_pos u)).le)
      (integrable_flow_half t)]
    have hsupp : Function.support (fun u : ℝ => Real.exp (-t * u ^ 2) * Φ u) = univ := by
      ext u
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (mul_pos (Real.exp_pos _) (Φ_pos u)).ne'
    rw [hsupp]
    simp
  · rw [heatE_riemannXi]
    simp_rw [flowLap_half]
    exact integral_ofReal

/-- **The centre value of the flow is nonzero at every time.** -/
theorem heatE_riemannXi_half_ne_zero (t : ℝ) : heatE t riemannXi (1 / 2) ≠ 0 := by
  obtain ⟨v, hv, h⟩ := heatE_riemannXi_half_pos t
  rw [h]
  exact_mod_cast hv.ne'

end Soma.Holonics.RH.HeatKernelPhi
