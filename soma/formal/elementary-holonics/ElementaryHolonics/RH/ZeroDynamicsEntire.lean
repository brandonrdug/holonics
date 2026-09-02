import ElementaryHolonics.RH.HeatEquationEntire

/-!
# Zero dynamics of `H_t` along a differentiable curve of simple zeros

Along a `C¹` curve `z(s)` the composite `s ↦ heatE s f (z s)` is differentiable with derivative
`−heatE s f″ (z s) + heatE s f′ (z s) · z′(s)`, the chain rule for the backward heat equation.  If
the curve consists of zeros of `H_s` and the zero at `t₀` is simple, then
`z′(t₀) = ∂_z² H_{t₀}(z t₀) / ∂_z H_{t₀}(z t₀)`: the velocity of a simple zero is the second
logarithmic derivative, exactly the first half of `zero_curve_flux` at the polynomial face.  The
second half, the expansion of `H″/H′` as a sum over the other zeros, is the Hadamard product and
remains open at the entire face.
-/

open Complex Metric Filter Topology Set
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.HeatEquationEntire

namespace Soma.Holonics.RH.ZeroDynamicsEntire

variable {f : ℂ → ℂ} {A B ρ : ℝ}

theorem hasDerivAt_coeff (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (-(s : ℂ)) ^ k / (k.factorial : ℂ))
      ((k : ℂ) * (-(t : ℂ)) ^ (k - 1) * (-1) / (k.factorial : ℂ)) t := by
  have h0 : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) t := (hasDerivAt_id t).ofReal_comp.neg
  exact (h0.pow k).div_const _

theorem coeff_deriv_succ (k : ℕ) (t : ℝ) :
    (((k + 1 : ℕ) : ℂ) * (-(t : ℂ)) ^ (k + 1 - 1) * (-1)) / ((k + 1).factorial : ℂ) =
      -((-(t : ℂ)) ^ k / (k.factorial : ℂ)) := by
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

theorem iteratedDeriv_two_mul_succ (f : ℂ → ℂ) (k : ℕ) :
    iteratedDeriv (2 * (k + 1)) f = iteratedDeriv (2 * k) (deriv (deriv f)) := by
  rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
  congr 1

theorem deriv_iteratedDeriv_two_mul (f : ℂ → ℂ) (k : ℕ) :
    deriv (iteratedDeriv (2 * k) f) = iteratedDeriv (2 * k) (deriv f) := by
  rw [← iteratedDeriv_succ, iteratedDeriv_succ']

/-- The derivative of a term along the curve. -/
noncomputable def curveDeriv (f : ℂ → ℂ) (z z' : ℝ → ℂ) (k : ℕ) (s : ℝ) : ℂ :=
  (k : ℂ) * (-(s : ℂ)) ^ (k - 1) * (-1) / (k.factorial : ℂ) * iteratedDeriv (2 * k) f (z s) +
    heatTerm s (deriv f) (z s) k * z' s

theorem hasDerivAt_heatTerm_comp (hf : Differentiable ℂ f) {z z' : ℝ → ℂ} {t : ℝ}
    (hz : HasDerivAt z (z' t) t) (k : ℕ) :
    HasDerivAt (fun s : ℝ => heatTerm s f (z s) k) (curveDeriv f z z' k t) t := by
  have h1 := hasDerivAt_coeff k t
  have h2 : HasDerivAt (fun s : ℝ => iteratedDeriv (2 * k) f (z s))
      (iteratedDeriv (2 * k) (deriv f) (z t) * z' t) t := by
    have := ((differentiable_iteratedDeriv hf (2 * k)) (z t)).hasDerivAt.comp t hz
    rw [deriv_iteratedDeriv_two_mul] at this
    exact this
  have := h1.mul h2
  refine this.congr_deriv ?_
  unfold curveDeriv heatTerm
  ring

/-- The first summand of `curveDeriv` is minus the previous term of `f″`. -/
theorem curveDeriv_first_succ (f : ℂ → ℂ) (z : ℝ → ℂ) (k : ℕ) (s : ℝ) :
    ((k + 1 : ℕ) : ℂ) * (-(s : ℂ)) ^ (k + 1 - 1) * (-1) / ((k + 1).factorial : ℂ) *
      iteratedDeriv (2 * (k + 1)) f (z s) = -heatTerm s (deriv (deriv f)) (z s) k := by
  rw [coeff_deriv_succ, iteratedDeriv_two_mul_succ]
  unfold heatTerm
  ring

/-- Chain rule for the flow along a `C¹` curve. -/
theorem hasDerivAt_heatE_comp (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z z' : ℝ → ℂ} (hz : ∀ s, HasDerivAt z (z' s) s)
    (hz' : Continuous z') (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => heatE s f (z s))
      (-heatE t₀ (deriv (deriv f)) (z t₀) + heatE t₀ (deriv f) (z t₀) * z' t₀) t₀ := by
  -- growth of the derivatives
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hf'' : Differentiable ℂ (deriv (deriv f)) := hf'.deriv
  have hg' := hasGrowth_deriv hf hg hA hB hρ0.le
  have hA' : 0 ≤ A * Real.exp (B * 2 ^ ρ) := by positivity
  have hB' : 0 ≤ B * 2 ^ ρ := by positivity
  have hg'' := hasGrowth_deriv hf' hg' hA' hB' hρ0.le
  have hA'' : 0 ≤ A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ) := by positivity
  have hB'' : 0 ≤ B * 2 ^ ρ * 2 ^ ρ := by positivity
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  -- bounds on the curve on the closed interval
  have hzc : Continuous z := continuous_iff_continuousAt.mpr fun s => (hz s).continuousAt
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := t₀ - 1) (b := t₀ + 1)).exists_bound_of_continuousOn
    hzc.continuousOn
  obtain ⟨V₀, hV₀⟩ := (isCompact_Icc (a := t₀ - 1) (b := t₀ + 1)).exists_bound_of_continuousOn
    hz'.continuousOn
  set R := max R₀ 0 with hR
  set V := max V₀ 0 with hV
  have hR0 : 0 ≤ R := le_max_right _ _
  have hV0 : 0 ≤ V := le_max_right _ _
  set T : ℝ := |t₀| + 1 with hT
  set I : Set ℝ := Ioo (t₀ - 1) (t₀ + 1) with hI
  have hopen : IsOpen I := isOpen_Ioo
  have hconn : IsPreconnected I := isPreconnected_Ioo
  have ht₀ : t₀ ∈ I := by
    rw [hI, mem_Ioo]
    constructor <;> linarith
  have hmemI : ∀ s ∈ I, |s| ≤ T ∧ ‖z s‖ ≤ R ∧ ‖z' s‖ ≤ V := by
    intro s hs
    rw [hI, mem_Ioo] at hs
    have hs' : s ∈ Icc (t₀ - 1) (t₀ + 1) := ⟨hs.1.le, hs.2.le⟩
    refine ⟨?_, (hR₀ s hs').trans (le_max_left _ _), (hV₀ s hs').trans (le_max_left _ _)⟩
    rw [hT, abs_le]
    constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀]
  -- the majorants
  set C1 : ℝ := 4 * Real.exp 1 * T * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ) with hC1
  set M1 : ℝ := A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ) *
    Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ * R ^ ρ) with hM1
  set C2 : ℝ := 4 * Real.exp 1 * T * Real.exp (B * 2 ^ ρ * 2 ^ ρ) with hC2
  set M2 : ℝ := A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ * R ^ ρ) with hM2
  have hM10 : 0 ≤ M1 := by positivity
  have hM20 : 0 ≤ M2 := by positivity
  set u : ℕ → ℝ := fun k =>
    M1 * majorant C1 (2 / ρ - 1) (k - 1) + V * (M2 * majorant C2 (2 / ρ - 1) k) with hu
  have hu_sum : Summable u := by
    have hv1 := (summable_majorant (C := C1) (by positivity) hδ).mul_left M1
    have hv1' : Summable (fun k => M1 * majorant C1 (2 / ρ - 1) (k - 1)) := by
      refine (summable_nat_add_iff 1).mp ?_
      simpa using hv1
    have hv2 := ((summable_majorant (C := C2) (by positivity) hδ).mul_left M2).mul_left V
    exact hv1'.add hv2
  -- termwise derivatives and bounds
  have hderiv : ∀ k (s : ℝ), s ∈ I →
      HasDerivAt (fun s : ℝ => heatTerm s f (z s) k) (curveDeriv f z z' k s) s :=
    fun k s _ => hasDerivAt_heatTerm_comp hf (hz s) k
  have hbound : ∀ k (s : ℝ), s ∈ I → ‖curveDeriv f z z' k s‖ ≤ u k := by
    intro k s hs
    obtain ⟨hsT, hzs, hz's⟩ := hmemI s hs
    unfold curveDeriv
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · cases k with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, zero_div, norm_zero, hu]
        exact mul_nonneg hM10 (by unfold majorant; simp)
      | succ k =>
        rw [curveDeriv_first_succ, norm_neg]
        simp only [Nat.add_sub_cancel]
        refine (norm_heatTerm_le_majorant hf'' hg'' hA'' hB'' hρ0 s hR0 hzs k).trans ?_
        apply mul_le_mul_of_nonneg_left _ hM10
        apply majorant_mono (by positivity) _ k
        have : 0 ≤ 4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ) := by positivity
        calc 4 * Real.exp 1 * |s| * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)
            = (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)) * |s| := by ring
          _ ≤ (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)) * T :=
              mul_le_mul_of_nonneg_left hsT this
          _ = C1 := by ring
    · rw [norm_mul]
      have h1 := norm_heatTerm_le_majorant hf' hg' hA' hB' hρ0 s hR0 hzs k
      have h2 : majorant (4 * Real.exp 1 * |s| * Real.exp (B * 2 ^ ρ * 2 ^ ρ)) (2 / ρ - 1) k ≤
          majorant C2 (2 / ρ - 1) k := by
        apply majorant_mono (by positivity) _ k
        have : 0 ≤ 4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ) := by positivity
        calc 4 * Real.exp 1 * |s| * Real.exp (B * 2 ^ ρ * 2 ^ ρ)
            = (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ)) * |s| := by ring
          _ ≤ (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ)) * T :=
              mul_le_mul_of_nonneg_left hsT this
          _ = C2 := by ring
      have hmaj0 : 0 ≤ majorant C2 (2 / ρ - 1) k := by
        unfold majorant
        split_ifs
        · norm_num
        · positivity
      calc ‖heatTerm s (deriv f) (z s) k‖ * ‖z' s‖
          ≤ (M2 * majorant C2 (2 / ρ - 1) k) * V := by
            apply mul_le_mul _ hz's (norm_nonneg _) (mul_nonneg hM20 hmaj0)
            exact h1.trans (mul_le_mul_of_nonneg_left h2 hM20)
        _ = V * (M2 * majorant C2 (2 / ρ - 1) k) := by ring
  have hg0 : Summable (fun k => heatTerm t₀ f (z t₀) k) :=
    (summable_heatTerm hf hg hA hB hρ0 hρ2 t₀ (z t₀)).of_norm
  have hmain := hasDerivAt_tsum_of_isPreconnected hu_sum hopen hconn hderiv hbound ht₀ hg0 ht₀
  refine hmain.congr_deriv ?_
  -- the value of the derivative series
  have hs1 : Summable (fun k : ℕ => ((k : ℂ) * (-(t₀ : ℂ)) ^ (k - 1) * (-1) / (k.factorial : ℂ) *
      iteratedDeriv (2 * k) f (z t₀))) := by
    refine Summable.of_norm_bounded (g := fun k => M1 * majorant C1 (2 / ρ - 1) (k - 1)) ?_ ?_
    · have hv1 := (summable_majorant (C := C1) (by positivity) hδ).mul_left M1
      refine (summable_nat_add_iff 1).mp ?_
      simpa using hv1
    · intro k
      have := hbound k t₀ ht₀
      unfold curveDeriv at this
      -- extract the first summand bound directly
      obtain ⟨hsT, hzs, _⟩ := hmemI t₀ ht₀
      cases k with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, zero_div, norm_zero]
        exact mul_nonneg hM10 (by unfold majorant; simp)
      | succ k =>
        rw [curveDeriv_first_succ, norm_neg]
        simp only [Nat.add_sub_cancel]
        refine (norm_heatTerm_le_majorant hf'' hg'' hA'' hB'' hρ0 t₀ hR0 hzs k).trans ?_
        apply mul_le_mul_of_nonneg_left _ hM10
        apply majorant_mono (by positivity) _ k
        have : 0 ≤ 4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ) := by positivity
        calc 4 * Real.exp 1 * |t₀| * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)
            = (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)) * |t₀| := by ring
          _ ≤ (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ * 2 ^ ρ * 2 ^ ρ)) * T :=
              mul_le_mul_of_nonneg_left hsT this
          _ = C1 := by ring
  have hs2 : Summable (fun k => heatTerm t₀ (deriv f) (z t₀) k * z' t₀) :=
    ((summable_heatTerm hf' hg' hA' hB' hρ0 hρ2 t₀ (z t₀)).of_norm).mul_right _
  unfold curveDeriv
  rw [hs1.tsum_add hs2, tsum_mul_right, hs1.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
  have hshift : (fun k => ((k + 1 : ℕ) : ℂ) * (-(t₀ : ℂ)) ^ (k + 1 - 1) * (-1) /
      ((k + 1).factorial : ℂ) * iteratedDeriv (2 * (k + 1)) f (z t₀)) =
      fun k => -heatTerm t₀ (deriv (deriv f)) (z t₀) k := by
    funext k
    exact curveDeriv_first_succ f z k t₀
  rw [hshift, tsum_neg]
  rfl

/-- The velocity of a simple zero along a `C¹` curve of zeros of `H_s`. -/
theorem zero_curve_velocity (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z z' : ℝ → ℂ} (hz : ∀ s, HasDerivAt z (z' s) s)
    (hz' : Continuous z') (hzero : ∀ s, heatE s f (z s) = 0) {t₀ : ℝ}
    (hs : deriv (heatE t₀ f) (z t₀) ≠ 0) :
    z' t₀ = deriv (deriv (heatE t₀ f)) (z t₀) / deriv (heatE t₀ f) (z t₀) := by
  have hF := hasDerivAt_heatE_comp hf hg hA hB hρ0 hρ2 hz hz' t₀
  have hconst : HasDerivAt (fun s : ℝ => heatE s f (z s)) 0 t₀ := by
    have : (fun s : ℝ => heatE s f (z s)) = fun _ => (0 : ℂ) := funext hzero
    rw [this]
    exact hasDerivAt_const t₀ (0 : ℂ)
  have h0 := hF.unique hconst
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hg' := hasGrowth_deriv hf hg hA hB hρ0.le
  have h1 : deriv (heatE t₀ f) = heatE t₀ (deriv f) := funext (deriv_heatE hf hg hA hB hρ0 hρ2 t₀)
  have h2 : deriv (heatE t₀ (deriv f)) (z t₀) = heatE t₀ (deriv (deriv f)) (z t₀) :=
    deriv_heatE hf' hg' (by positivity) (by positivity) hρ0 hρ2 t₀ (z t₀)
  rw [h1, h2]
  rw [h1] at hs
  field_simp
  linear_combination h0

/-- The velocity of a simple zero of `H_t = e^{−tD²} Ξ` along a `C¹` curve of zeros. -/
theorem zero_curve_velocity_riemannXi {z z' : ℝ → ℂ} (hz : ∀ s, HasDerivAt z (z' s) s)
    (hz' : Continuous z') (hzero : ∀ s, heatE s riemannXi (z s) = 0) {t₀ : ℝ}
    (hs : deriv (heatE t₀ riemannXi) (z t₀) ≠ 0) :
    z' t₀ = deriv (deriv (heatE t₀ riemannXi)) (z t₀) / deriv (heatE t₀ riemannXi) (z t₀) :=
  zero_curve_velocity differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) hz hz' hzero hs

end Soma.Holonics.RH.ZeroDynamicsEntire
