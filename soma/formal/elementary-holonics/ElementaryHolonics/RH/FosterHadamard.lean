import Mathlib
import ElementaryHolonics.RH.FosterSplit
import ElementaryHolonics.RH.AbscissaGrowth

/-!
# FT3 (ii): Hadamard — `ξ² = ξ(½)² · P`, and the full Foster form

The defect `G = 2 ξ′/ξ − P′/P` is analytic on the nonzero set `U` of `ξ`. On the disc of radius
`R` about `½` it agrees with the analytic `F_R` of FT3 (i), bounded by `bound R`, and Cauchy's
estimate at scale `r` with `R = 8(|w − ½| + r) + 8` gives `‖G′(w)‖ ≤ bound R / r`. Landau's
remainder is logarithmic in `R` and the tail of the inverse squares vanishes, so the right side
tends to zero and `G′ = 0` on `U`. `U` is the complement of a countable set, hence connected, so
`G` is constant on `U`; the reflection `z ↦ 1 − z` makes `G` odd, so the constant is zero. Hence

```text
ξ′/ξ(z) = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²),      ξ(z)² = ξ(½)² · P(z).
```

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterHadamard

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.LandauXi
open Soma.Holonics.RH.JensenCountsTheComb
open Soma.Holonics.RH.AbscissaGrowth
open Soma.Holonics.RH.FosterTanks
open Soma.Holonics.RH.FosterCount
open Soma.Holonics.RH.FosterProduct
open Soma.Holonics.RH.FosterSplit
open scoped Classical

/-! ## Landau's remainder is logarithmic in the radius -/

/-- `log 2 / log (3/2)`. -/
def cq : ℝ := Real.log 2 / Real.log (3 / 2)

theorem cq_pos : 0 < cq := by
  unfold cq
  apply div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- The slope of the logarithmic bound on Landau's remainder. -/
def landauB : ℝ := 16 * (1 + cq) * (5 * pointC)

/-- The intercept of the logarithmic bound on Landau's remainder. -/
def landauA : ℝ := 16 * (1 + cq) * (1 + L₀ + 5 * pointC * Real.log 5) + 16 * cq * L₀

theorem L₀_nonneg : 0 ≤ L₀ := le_max_left _ _

theorem neg_log_le_L₀ : -Real.log ‖riemannXi (1 / 2)‖ ≤ L₀ := le_max_right _ _

theorem norm_xi_half_pos : 0 < ‖riemannXi (1 / 2)‖ :=
  norm_pos_iff.mpr XiCentre.riemannXi_one_half_ne_zero

theorem xiBudget_le_log {R : ℝ} (hR : 1 ≤ R) :
    xiBudget pointC (1 / 2) R ≤ 1 + L₀ + 5 * pointC * R * (Real.log 5 + Real.log R) := by
  unfold xiBudget
  rw [norm_half]
  have hpc := pointC_pos
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hL := L₀_nonneg
  have hprod : 0 ≤ 5 * pointC * R * (Real.log 5 + Real.log R) := by positivity
  apply max_le
  · linarith
  · have hs1 : (1 : ℝ) ≤ 1 / 2 + R + 3 := by linarith
    have hs2 : 1 / 2 + R + 3 ≤ 5 * R := by linarith
    have hmono := mulLog_mono_on_one hs1 hs2
    have h5 : Real.log (5 * R) = Real.log 5 + Real.log R :=
      Real.log_mul (by norm_num) (by linarith)
    rw [h5] at hmono
    have := neg_log_le_L₀
    have hm2 := mul_le_mul_of_nonneg_left hmono hpc.le
    nlinarith

theorem log_jensen_le {R : ℝ} :
    Real.log (jensenCeiling pointC (1 / 2) R / ‖riemannXi (1 / 2)‖) ≤
      L₀ + xiBudget pointC (1 / 2) R := by
  have hx := norm_xi_half_pos
  have hj : 0 < jensenCeiling pointC (1 / 2) R := lt_of_lt_of_le one_pos (one_le_jensenCeiling _ _ _)
  rw [Real.log_div hj.ne' hx.ne']
  have hX := xiBudget_pos pointC (1 / 2 : ℂ) R
  have hlogj : Real.log (jensenCeiling pointC (1 / 2) R) ≤
      max 0 (Real.log ‖riemannXi (1 / 2)‖ + xiBudget pointC (1 / 2) R) := by
    unfold jensenCeiling
    by_cases h : 1 ≤ ‖riemannXi (1 / 2)‖ * Real.exp (xiBudget pointC (1 / 2) R)
    · rw [max_eq_right h, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
      exact le_max_right _ _
    · push_neg at h
      rw [max_eq_left h.le, Real.log_one]
      exact le_max_left _ _
  have hL1 := L₀_nonneg
  have hL2 := neg_log_le_L₀
  have hmax : max 0 (Real.log ‖riemannXi (1 / 2)‖ + xiBudget pointC (1 / 2) R) ≤
      L₀ + xiBudget pointC (1 / 2) R + Real.log ‖riemannXi (1 / 2)‖ :=
    max_le (by linarith) (by linarith)
  linarith

/-- **Landau's remainder is logarithmic in the radius.** -/
theorem landau_le {R : ℝ} (hR : 1 ≤ R) : landau R ≤ landauA + landauB * Real.log R := by
  unfold landau
  have hX := xiBudget_le_log hR
  have hXpos := xiBudget_pos pointC (1 / 2 : ℂ) R
  have hJ := log_jensen_le (R := R)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := L₀_nonneg
  have hpc := pointC_pos
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hcq := cq_pos
  set X := xiBudget pointC (1 / 2) R with hXdef
  set J := Real.log (jensenCeiling pointC (1 / 2) R / ‖riemannXi (1 / 2)‖) with hJdef
  have hJ' : J / Real.log (3 / 2) * Real.log 2 ≤ (L₀ + X) * cq := by
    unfold cq
    rw [div_mul_eq_mul_div, mul_div_assoc]
    apply mul_le_mul_of_nonneg_right hJ (by positivity)
  have hnum : 16 * (X + J / Real.log (3 / 2) * Real.log 2) ≤ 16 * ((1 + cq) * X + cq * L₀) := by
    nlinarith
  have hX' : (1 + cq) * X + cq * L₀ ≤
      ((1 + cq) * (1 + L₀) + cq * L₀) + (1 + cq) * 5 * pointC * R * (Real.log 5 + Real.log R) := by
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 1 + cq)
    nlinarith
  have hR0 : 0 < R := by linarith
  have hc0 : 0 ≤ (1 + cq) * (1 + L₀) + cq * L₀ := by positivity
  calc 16 * (X + J / Real.log (3 / 2) * Real.log 2) / R
      ≤ 16 * ((1 + cq) * X + cq * L₀) / R := by gcongr
    _ ≤ 16 * (((1 + cq) * (1 + L₀) + cq * L₀) +
          (1 + cq) * 5 * pointC * R * (Real.log 5 + Real.log R)) / R := by gcongr
    _ = 16 * ((1 + cq) * (1 + L₀) + cq * L₀) / R +
          16 * (1 + cq) * 5 * pointC * (Real.log 5 + Real.log R) := by
        field_simp
    _ ≤ 16 * ((1 + cq) * (1 + L₀) + cq * L₀) +
          16 * (1 + cq) * 5 * pointC * (Real.log 5 + Real.log R) :=
        add_le_add_left
          (div_le_self (by positivity : (0 : ℝ) ≤ 16 * ((1 + cq) * (1 + L₀) + cq * L₀)) hR) _
    _ = landauA + landauB * Real.log R := by
        unfold landauA landauB
        ring

/-! ## The global defect and Cauchy's estimate -/

/-- The global defect `2 ξ′/ξ − P′/P`. -/
def G (z : ℂ) : ℂ := 2 * logDeriv riemannXi z - logDeriv P z

/-- The nonzero set of `ξ`. -/
def U : Set ℂ := {z | riemannXi z ≠ 0}

theorem isOpen_U : IsOpen U := isOpen_ne_fun differentiable_riemannXi.continuous continuous_const

theorem half_mem_U : (1 / 2 : ℂ) ∈ U := XiCentre.riemannXi_one_half_ne_zero

theorem one_sub_mem_U {z : ℂ} (hz : z ∈ U) : 1 - z ∈ U := by
  show riemannXi (1 - z) ≠ 0
  rw [riemannXi_one_sub]
  exact hz

theorem G_differentiableOn : DifferentiableOn ℂ G U := by
  unfold G
  exact ((logDeriv_differentiableOn isOpen_U differentiable_riemannXi.differentiableOn
    (fun z hz => hz)).const_mul 2).sub
    (logDeriv_differentiableOn isOpen_U differentiable_P.differentiableOn
      (fun z hz => P_ne_zero (mult_eq_zero_of_ne_zero hz)))

/-- Cauchy's estimate at scale `r`. -/
theorem norm_deriv_G_le {w : ℂ} (hw : w ∈ U) {r : ℝ} (hr : 0 < r) :
    ‖deriv G w‖ ≤ bound (8 * (‖w - 1 / 2‖ + r) + 8) / r := by
  have hR0 : 0 < 8 * (‖w - 1 / 2‖ + r) + 8 := by positivity
  have hw8 : ‖w - 1 / 2‖ < (8 * (‖w - 1 / 2‖ + r) + 8) / 8 := by linarith
  have hev : G =ᶠ[𝓝 w] F hR0 := by
    have hwU : ∀ᶠ z in 𝓝 w, z ∈ U := isOpen_U.mem_nhds hw
    have hwb : ∀ᶠ z in 𝓝 w, z ∈ ball (1 / 2 : ℂ) ((8 * (‖w - 1 / 2‖ + r) + 8) / 2) :=
      isOpen_ball.mem_nhds (by
        rw [mem_ball, Complex.dist_eq]
        linarith)
    filter_upwards [hwU, hwb] with z hz hzb
    exact (F_eq hR0 hzb hz).symm
  rw [hev.deriv_eq]
  have hsub : closedBall w r ⊆ ball (1 / 2 : ℂ) ((8 * (‖w - 1 / 2‖ + r) + 8) / 8) := by
    intro z hz
    rw [mem_closedBall, Complex.dist_eq] at hz
    rw [mem_ball, Complex.dist_eq]
    calc ‖z - 1 / 2‖ = ‖(z - w) + (w - 1 / 2)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖w - 1 / 2‖ := norm_add_le _ _
      _ < (8 * (‖w - 1 / 2‖ + r) + 8) / 8 := by linarith
  have hd : DiffContOnCl ℂ (F hR0) (ball w r) :=
    (F_differentiableOn hR0).diffContOnCl_ball (hsub.trans (ball_subset_ball (by linarith)))
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd
  intro z hz
  exact norm_F_le hR0 (hsub (sphere_subset_closedBall hz))

/-! ## The estimate vanishes at infinity -/

theorem tendsto_log_lin_div {a : ℝ} :
    Tendsto (fun r : ℝ => Real.log (8 * (a + r) + 8) / r) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop (1 / 8) (-(a + 1)) 1 (by norm_num)
  have hlin : Tendsto (fun r : ℝ => 8 * (a + r) + 8) atTop atTop := by
    apply tendsto_atTop_add_const_right
    apply Tendsto.const_mul_atTop (by norm_num)
    exact tendsto_atTop_add_const_left _ _ tendsto_id
  have := h.comp hlin
  refine this.congr ?_
  intro r
  simp only [Function.comp, pow_one]
  congr 1
  ring

theorem tendsto_bound_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun r : ℝ => 2 * (landauA + landauB * Real.log (8 * (a + r) + 8)) / r +
      (4 + (4 * a + 4) / r) * tailInvSq (8 * (a + r) + 8)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun r : ℝ => 8 * (a + r) + 8) atTop atTop := by
    apply tendsto_atTop_add_const_right
    apply Tendsto.const_mul_atTop (by norm_num)
    exact tendsto_atTop_add_const_left _ _ tendsto_id
  have h1 : Tendsto (fun r : ℝ => 2 * (landauA + landauB * Real.log (8 * (a + r) + 8)) / r)
      atTop (𝓝 0) := by
    have hA : Tendsto (fun r : ℝ => 2 * landauA / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hB : Tendsto (fun r : ℝ => 2 * landauB * (Real.log (8 * (a + r) + 8) / r)) atTop
        (𝓝 (2 * landauB * 0)) := tendsto_log_lin_div.const_mul _
    rw [mul_zero] at hB
    have := hA.add hB
    rw [add_zero] at this
    refine this.congr ?_
    intro r
    ring
  have h2 : Tendsto (fun r : ℝ => (4 + (4 * a + 4) / r) * tailInvSq (8 * (a + r) + 8)) atTop
      (𝓝 ((4 + 0) * 0)) := by
    apply Tendsto.mul
    · exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    · exact tailInvSq_tendsto.comp hlin
  rw [add_zero, mul_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

theorem deriv_G_eq_zero {w : ℂ} (hw : w ∈ U) : deriv G w = 0 := by
  set a := ‖w - 1 / 2‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hev : ∀ᶠ r in atTop, ‖deriv G w‖ ≤
      2 * (landauA + landauB * Real.log (8 * (a + r) + 8)) / r +
        (4 + (4 * a + 4) / r) * tailInvSq (8 * (a + r) + 8) := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : 0 < r := by linarith
    have hR1 : 1 ≤ 8 * (a + r) + 8 := by linarith
    have hl := landau_le hR1
    have ht := tailInvSq_nonneg (8 * (a + r) + 8)
    calc ‖deriv G w‖ ≤ bound (8 * (a + r) + 8) / r := norm_deriv_G_le hw hr0
      _ = 2 * landau (8 * (a + r) + 8) / r +
          (4 + (4 * a + 4) / r) * tailInvSq (8 * (a + r) + 8) := by
          unfold bound
          field_simp
          ring
      _ ≤ 2 * (landauA + landauB * Real.log (8 * (a + r) + 8)) / r +
          (4 + (4 * a + 4) / r) * tailInvSq (8 * (a + r) + 8) := by
          gcongr
  have := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_bound_div ha0) hev
  exact norm_le_zero_iff.mp this

/-! ## The nonzero set is connected, and the defect is odd -/

theorem mult_ne_zero_of_eq_zero {z : ℂ} (hz : riemannXi z = 0) : mult z ≠ 0 := by
  unfold mult
  have ha := differentiable_riemannXi.analyticAt z
  rw [ha.meromorphicOrderAt_eq]
  have hne0 : analyticOrderAt riemannXi z ≠ 0 := by
    rw [Ne, ha.analyticOrderAt_eq_zero]
    push_neg
    exact hz
  have hnetop : analyticOrderAt riemannXi z ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro h
    have hall : EqOn riemannXi 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun x _ => differentiable_riemannXi.analyticAt x) isPreconnected_univ (mem_univ z) h
    exact XiCentre.riemannXi_one_half_ne_zero (hall (mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.map_coe, WithTop.untop₀_coe, ne_eq, Nat.cast_eq_zero]
  exact_mod_cast hne0

theorem zeroSet_countable : {z : ℂ | riemannXi z = 0}.Countable := by
  have hsub : {z : ℂ | riemannXi z = 0} ⊆
      ⋃ n : ℕ, (fun u : Zero => (u : ℂ)) '' {u : Zero | ‖(u : ℂ) - 1 / 2‖ < n} := by
    intro z hz
    have hm : mult z ≠ 0 := mult_ne_zero_of_eq_zero hz
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z - 1 / 2‖
    exact mem_iUnion.mpr ⟨n, ⟨⟨z, hm⟩, hn, rfl⟩⟩
  exact (Set.countable_iUnion fun n : ℕ => ((finite_zero_ball (n : ℝ)).image _).countable).mono hsub

theorem U_eq_compl : U = {z : ℂ | riemannXi z = 0}ᶜ := by
  ext z
  simp [U]

theorem isPreconnected_U : IsPreconnected U := by
  rw [U_eq_compl]
  exact (Set.Countable.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) zeroSet_countable).isConnected.isPreconnected

theorem G_const {z : ℂ} (hz : z ∈ U) : G z = G (1 / 2) :=
  isOpen_U.is_const_of_deriv_eq_zero isPreconnected_U G_differentiableOn
    (fun w hw => deriv_G_eq_zero hw) hz half_mem_U

theorem deriv_one_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsym : ∀ s, f (1 - s) = f s) (z : ℂ) :
    deriv f (1 - z) = -deriv f z := by
  have h1 : HasDerivAt (fun x => f (1 - x)) (deriv f (1 - z) * (-1)) z :=
    (hf (1 - z)).hasDerivAt.comp z ((hasDerivAt_id z).const_sub 1)
  have h2 : (fun x => f (1 - x)) = f := funext hsym
  rw [h2] at h1
  rw [h1.deriv]
  ring

theorem logDeriv_one_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsym : ∀ s, f (1 - s) = f s)
    (z : ℂ) : logDeriv f (1 - z) = -logDeriv f z := by
  simp only [logDeriv_apply]
  rw [deriv_one_sub hf hsym, hsym, neg_div]

theorem G_one_sub (z : ℂ) : G (1 - z) = -G z := by
  unfold G
  rw [logDeriv_one_sub differentiable_riemannXi riemannXi_one_sub,
    logDeriv_one_sub differentiable_P P_symm]
  ring

theorem G_half : G (1 / 2) = 0 := by
  have h := G_one_sub (1 / 2)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  linear_combination h / 2

/-- **The defect vanishes: `2 ξ′/ξ = P′/P` off the zeros.** -/
theorem G_eq_zero {z : ℂ} (hz : riemannXi z ≠ 0) : G z = 0 := by
  rw [G_const hz, G_half]

/-! ## The Foster form and Hadamard's identity -/

/-- **The full Foster form**: off the zeros,
`ξ′/ξ(z) = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²)` over the zeros of `ξ`. -/
theorem foster_form {z : ℂ} (hz : riemannXi z ≠ 0) :
    logDeriv riemannXi z = ∑' u : Zero, ((mult (u : ℂ)).toNat : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) := by
  have hG := G_eq_zero hz
  unfold G at hG
  rw [logDeriv_P (mult_eq_zero_of_ne_zero hz), tsum_tank_eq] at hG
  have h2 : ∑' u : Zero, ((mult (u : ℂ)).toNat : ℂ) *
      (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) =
      2 * ∑' u : Zero, ((mult (u : ℂ)).toNat : ℂ) *
        ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [h2] at hG
  linear_combination hG / 2

theorem P_half : P (1 / 2) = 1 := by
  unfold P
  have h : ∀ i : Idx, 1 + a i (1 / 2) = 1 := by
    intro i
    simp [a]
  simp only [h]
  exact tprod_one

/-- **Hadamard's identity: `ξ(z)² = ξ(½)² · P(z)` for every `z`.** -/
theorem sq_eq_centre_mul_P (z : ℂ) : riemannXi z ^ 2 = riemannXi (1 / 2) ^ 2 * P z := by
  by_cases hz : riemannXi z ≠ 0
  · have hPz : P z ≠ 0 := P_ne_zero (mult_eq_zero_of_ne_zero hz)
    have hq_diff : DifferentiableOn ℂ (fun w => riemannXi w ^ 2 / P w) U :=
      (differentiable_riemannXi.pow 2).differentiableOn.div differentiable_P.differentiableOn
        (fun w hw => P_ne_zero (mult_eq_zero_of_ne_zero hw))
    have hq_deriv : ∀ w ∈ U, deriv (fun w => riemannXi w ^ 2 / P w) w = 0 := by
      intro w hw
      have hw' : riemannXi w ≠ 0 := hw
      have hPw := P_ne_zero (mult_eq_zero_of_ne_zero hw')
      have hlog : logDeriv (fun w => riemannXi w ^ 2 / P w) w = G w := by
        rw [logDeriv_div (f := fun w => riemannXi w ^ 2) (g := P) w (pow_ne_zero 2 hw') hPw
          ((differentiable_riemannXi.pow 2) w) (differentiable_P w)]
        have hsq : (fun w => riemannXi w ^ 2) = fun w => riemannXi w * riemannXi w :=
          funext fun w => sq _
        rw [hsq, logDeriv_mul w hw' hw' (differentiable_riemannXi w) (differentiable_riemannXi w)]
        unfold G
        ring
      rw [G_eq_zero hw', logDeriv_apply, div_eq_zero_iff] at hlog
      rcases hlog with h | h
      · exact h
      · exact absurd h (div_ne_zero (pow_ne_zero 2 hw') hPw)
    have hconst := isOpen_U.is_const_of_deriv_eq_zero isPreconnected_U hq_diff hq_deriv hz
      half_mem_U
    simp only [P_half, div_one] at hconst
    rw [div_eq_iff hPz] at hconst
    rw [hconst]
  · push_neg at hz
    have hP : P z = 0 := P_eq_zero ⟨z, mult_ne_zero_of_eq_zero hz⟩
    rw [hz, hP]
    ring

end Soma.Holonics.RH.FosterHadamard
