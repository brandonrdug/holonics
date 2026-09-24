import ElementaryHolonics.RH.XiGrowth
import ElementaryHolonics.RH.ZeroComb
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The backward heat equation for the derivative-series flow, and reflection symmetry

For an entire `f` of order below two, `∂_z heatE t f = heatE t (f')`, so
`∂_z² heatE t f = heatE t (f'')`, and differentiating the series in `t` termwise on a bounded
interval gives `∂_t heatE t f = −heatE t (f'')`.  Hence `H_t = heatE t f` obeys the backward heat
equation `∂_t H = −∂_z² H`, the equation whose zero dynamics is the comb flux of
`HeatFlowOfPolynomials`.  If `f (1 − s) = f s` then `heatE t f (1 − s) = heatE t f s`; for `Ξ`
this is the reflection symmetry of `H_t`.
-/

open Complex Metric Filter Topology Set
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth

namespace Soma.Holonics.RH.HeatEquationEntire

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- The derivative of an entire function with a growth bound has a growth bound. -/
theorem hasGrowth_deriv (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    HasGrowth (deriv f) (A * Real.exp (B * 2 ^ ρ)) (B * 2 ^ ρ) ρ := by
  intro z
  have h1 := norm_iteratedDeriv_le hf hg hA hB hρ 1 z one_pos
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one, div_one] at h1
  refine h1.trans ?_
  have h2 : (‖z‖ + 1) ^ ρ ≤ 2 ^ ρ * (‖z‖ ^ ρ + 1 ^ ρ) := add_rpow_le hρ (norm_nonneg z) zero_le_one
  rw [Real.one_rpow] at h2
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  nlinarith [Real.rpow_nonneg (norm_nonneg z) ρ, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ρ]

theorem differentiable_iteratedDeriv (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n f) :=
  hf.contDiff.differentiable_iteratedDeriv' n

/-- `∂_z` of a heat term is the heat term of `f'`. -/
theorem deriv_heatTerm (hf : Differentiable ℂ f) (t : ℝ) (z : ℂ) (k : ℕ) :
    deriv (fun w => heatTerm t f w k) z = heatTerm t (deriv f) z k := by
  unfold heatTerm
  rw [deriv_const_mul _ (differentiable_iteratedDeriv hf _ z), ← iteratedDeriv_succ,
    iteratedDeriv_succ']

/-- `∂_z heatE t f = heatE t (f')`. -/
theorem deriv_heatE (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (t : ℝ) (z : ℂ) :
    deriv (heatE t f) z = heatE t (deriv f) z := by
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hsum := (summable_majorant (C := 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ))
    (by positivity) hδ).mul_left (A * Real.exp (B * 2 ^ ρ * (‖z‖ + 1) ^ ρ))
  have hS : HasSum (fun k => deriv (fun w => heatTerm t f w k) z) (deriv (heatE t f) z) := by
    unfold heatE
    refine hasSum_deriv_of_summable_norm (U := ball 0 (‖z‖ + 1)) hsum
      (fun k => (differentiable_heatTerm hf t k).differentiableOn) isOpen_ball ?_ ?_
    · intro k w hw
      rw [mem_ball_zero_iff] at hw
      exact norm_heatTerm_le_majorant hf hg hA hB hρ0 t (by positivity) hw.le k
    · rw [mem_ball_zero_iff]
      linarith
  simp only [deriv_heatTerm hf] at hS
  exact hS.tsum_eq.symm

/-- The derivative of a heat term in `t`. -/
theorem hasDerivAt_heatTerm_succ (f : ℂ → ℂ) (z : ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => heatTerm t f z (k + 1))
      (-heatTerm t (deriv (deriv f)) z k) t := by
  set c : ℂ := iteratedDeriv (2 * (k + 1)) f z with hc
  have h1 : HasDerivAt (fun τ : ℂ => (-τ) ^ (k + 1) / ((k + 1).factorial : ℂ) * c)
      ((((k + 1 : ℕ) : ℂ) * (-(t : ℂ)) ^ k) * (-1) / ((k + 1).factorial : ℂ) * c) (t : ℂ) := by
    have := (((hasDerivAt_pow (k + 1) (-(t : ℂ))).comp (t : ℂ) (hasDerivAt_neg (t : ℂ))).div_const
      ((k + 1).factorial : ℂ)).mul_const c
    exact this.congr_deriv (by simp)
  have h2 := h1.comp_ofReal
  refine h2.congr_deriv ?_
  have h3 : iteratedDeriv (2 * k) (deriv (deriv f)) z = c := by
    rw [hc, ← iteratedDeriv_succ', ← iteratedDeriv_succ']
    congr 1
  unfold heatTerm
  rw [h3, Nat.factorial_succ]
  push_cast
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

theorem hasDerivAt_heatTerm_zero (f : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => heatTerm t f z 0) 0 t := by
  have : (fun t : ℝ => heatTerm t f z 0) = fun _ => f z := by
    funext t
    exact heatTerm_zero t f z
  rw [this]
  exact hasDerivAt_const _ _

theorem majorant_mono {C C' δ : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (k : ℕ) :
    majorant C δ k ≤ majorant C' δ k := by
  unfold majorant
  split_ifs
  · exact le_rfl
  · apply pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg k) _))
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- The `t`-derivative of the shifted term sequence, `0` at `k = 0`. -/
noncomputable def tDeriv (f : ℂ → ℂ) (z : ℂ) : ℕ → ℝ → ℂ
  | 0, _ => 0
  | k + 1, t => -heatTerm t (deriv (deriv f)) z k

/-- `∂_t heatE t f = −heatE t (f'')`. -/
theorem hasDerivAt_heatE_t (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (z : ℂ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => heatE t f z) (-heatE t₀ (deriv (deriv f)) z) t₀ := by
  -- growth of `f''`
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hf'' : Differentiable ℂ (deriv (deriv f)) := hf'.deriv
  have hg' := hasGrowth_deriv hf hg hA hB hρ0.le
  have hA' : 0 ≤ A * Real.exp (B * 2 ^ ρ) := by positivity
  have hB' : 0 ≤ B * 2 ^ ρ := by positivity
  have hg'' := hasGrowth_deriv hf' hg' hA' hB' hρ0.le
  set A'' := A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ) with hA''
  set B'' := B * 2 ^ ρ * 2 ^ ρ with hB''
  have hA''0 : 0 ≤ A'' := by positivity
  have hB''0 : 0 ≤ B'' := by positivity
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  set T : ℝ := |t₀| + 1 with hT
  set CT : ℝ := 4 * Real.exp 1 * T * Real.exp (B'' * 2 ^ ρ) with hCT
  set M : ℝ := A'' * Real.exp (B'' * 2 ^ ρ * ‖z‖ ^ ρ) with hM
  have hM0 : 0 ≤ M := by positivity
  set u : ℕ → ℝ := fun k => M * majorant CT (2 / ρ - 1) (k - 1) with hu
  have hu_sum : Summable u := by
    have hv := (summable_majorant (C := CT) (by positivity) hδ).mul_left M
    refine (summable_nat_add_iff 1).mp ?_
    simpa [hu] using hv
  have hopen : IsOpen (Ioo (-T) T) := isOpen_Ioo
  have hconn : IsPreconnected (Ioo (-T) T) := isPreconnected_Ioo
  have ht₀ : t₀ ∈ Ioo (-T) T := by
    rw [mem_Ioo]
    constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀]
  have hderiv : ∀ k (t : ℝ), t ∈ Ioo (-T) T →
      HasDerivAt (fun t : ℝ => heatTerm t f z k) (tDeriv f z k t) t := by
    intro k t _
    cases k with
    | zero => exact hasDerivAt_heatTerm_zero f z t
    | succ k => exact hasDerivAt_heatTerm_succ f z k t
  have hbound : ∀ k (t : ℝ), t ∈ Ioo (-T) T → ‖tDeriv f z k t‖ ≤ u k := by
    intro k t ht
    rw [mem_Ioo] at ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    cases k with
    | zero =>
      simp only [tDeriv, norm_zero, hu]
      exact mul_nonneg hM0 (by unfold majorant; simp)
    | succ k =>
      simp only [tDeriv, norm_neg, hu, Nat.add_sub_cancel]
      refine (norm_heatTerm_le_majorant hf'' hg'' hA''0 hB''0 hρ0 t (norm_nonneg z) le_rfl k).trans ?_
      apply mul_le_mul_of_nonneg_left _ hM0
      apply majorant_mono (by positivity) _ k
      have : 0 ≤ 4 * Real.exp 1 * Real.exp (B'' * 2 ^ ρ) := by positivity
      calc 4 * Real.exp 1 * |t| * Real.exp (B'' * 2 ^ ρ)
          = (4 * Real.exp 1 * Real.exp (B'' * 2 ^ ρ)) * |t| := by ring
        _ ≤ (4 * Real.exp 1 * Real.exp (B'' * 2 ^ ρ)) * T := mul_le_mul_of_nonneg_left htT this
        _ = CT := by ring
  have hg0 : Summable (fun k => heatTerm t₀ f z k) :=
    (summable_heatTerm hf hg hA hB hρ0 hρ2 t₀ z).of_norm
  have hmain := hasDerivAt_tsum_of_isPreconnected hu_sum hopen hconn hderiv hbound ht₀ hg0 ht₀
  refine hmain.congr_deriv ?_
  have hsum' : Summable (fun k => tDeriv f z k t₀) :=
    Summable.of_norm_bounded hu_sum (fun k => hbound k t₀ ht₀)
  rw [hsum'.tsum_eq_zero_add]
  simp only [tDeriv, zero_add]
  rw [tsum_neg]
  rfl

/-- The backward heat equation `∂_t H_t = −∂_z² H_t` for `H_t = heatE t f`. -/
theorem heat_equation (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => heatE t f z) (-deriv (deriv (heatE t f)) z) t := by
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hg' := hasGrowth_deriv hf hg hA hB hρ0.le
  have h1 : deriv (heatE t f) = heatE t (deriv f) := funext (deriv_heatE hf hg hA hB hρ0 hρ2 t)
  have h2 : deriv (heatE t (deriv f)) z = heatE t (deriv (deriv f)) z :=
    deriv_heatE hf' hg' (by positivity) (by positivity) hρ0 hρ2 t z
  rw [h1, h2]
  exact hasDerivAt_heatE_t hf hg hA hB hρ0 hρ2 z t

/-- Iterated derivatives of `f (1 − s)`. -/
theorem iteratedDeriv_comp_one_sub (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun s => f (1 - s)) = fun s => (-1) ^ n * iteratedDeriv n f (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have hd : Differentiable ℂ (iteratedDeriv n f) := differentiable_iteratedDeriv hf n
    have hd' : DifferentiableAt ℂ (fun s => iteratedDeriv n f (1 - s)) s :=
      (hd (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)
    rw [deriv_const_mul _ hd', deriv_comp_const_sub, iteratedDeriv_succ]
    ring

/-- Reflection symmetry passes through the flow. -/
theorem heatE_one_sub (hf : Differentiable ℂ f) (hsym : ∀ s, f (1 - s) = f s) (t : ℝ) (s : ℂ) :
    heatE t f (1 - s) = heatE t f s := by
  have hfun : (fun s => f (1 - s)) = f := funext hsym
  unfold heatE heatTerm
  congr 1
  funext k
  have := congrFun (iteratedDeriv_comp_one_sub hf (2 * k)) s
  rw [hfun] at this
  rw [this, pow_mul]
  simp

/-- `H_t(1 − s) = H_t(s)` for the flow of `Ξ`. -/
theorem heatE_riemannXi_one_sub (t : ℝ) (s : ℂ) :
    heatE t riemannXi (1 - s) = heatE t riemannXi s :=
  heatE_one_sub differentiable_riemannXi
    (fun s => congrFun Soma.Holonics.RH.ZeroComb.riemannXi_comp_reflection s) t s

/-- The backward heat equation for `H_t = e^{−tD²} Ξ`. -/
theorem heat_equation_riemannXi (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => heatE t riemannXi z) (-deriv (deriv (heatE t riemannXi)) z) t :=
  heat_equation differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num) (by norm_num)
    (by norm_num) z t

end Soma.Holonics.RH.HeatEquationEntire
