import Mathlib
import ElementaryHolonics.RH.FosterClassSplit

/-!
# FT3 (ii): Hadamard — `ξ² = ξ(½)² · P`, and the full Foster form

The defect `G f = 2 ξ′/ξ − P′/P` is analytic on the nonzero set `U` of `ξ`. On the disc of radius
`R` about `½` it agrees with the analytic `F_R` of FT3 (i), bounded by `bound f A B σ R`, and Cauchy's
estimate at scale `r` with `R = 8(|w − ½| + r) + 8` gives `‖G′(w)‖ ≤ bound f A B σ R / r`. Landau's
remainder is logarithmic in `R` and the (tail (f := f)) of the inverse squares vanishes, so the right side
tends to zero and `G′ = 0` on `U`. `U` is the complement of a countable set, hence connected, so
`G` is constant on `U`; the reflection `z ↦ 1 − z` makes `G` odd, so the constant is zero. Hence

```text
ξ′/ξ(z) = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²),      ξ(z)² = ξ(½)² · P(z).
```

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassHadamard

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.FosterTanks
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.FosterClassSplit
open scoped Classical

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-! ## Landau's remainder is `O(R^{σ−1})` -/

omit hf in
/-- `log 2 / log (3/2)`. -/
def cq : ℝ := Real.log 2 / Real.log (3 / 2)

omit hf in
theorem cq_pos : 0 < cq := by
  unfold cq
  apply div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

omit hf in
/-- The exponent of the remainder bound, `max (σ − 1) 0 < 1`. -/
def τ (σ : ℝ) : ℝ := max (σ - 1) 0

omit hf in
theorem τ_nonneg (σ : ℝ) : 0 ≤ τ σ := le_max_right _ _

theorem τ_lt_one : τ σ < 1 := by
  unfold τ
  have := hf.σ_lt_two
  apply max_lt <;> linarith

omit hf in
/-- The slope of the bound on Landau's remainder. -/
def landauB (B σ : ℝ) : ℝ := 16 * (1 + cq) * (B * 2 ^ σ)

omit hf in
/-- The intercept of the bound on Landau's remainder. -/
def landauA (f : ℂ → ℂ) (A : ℝ) : ℝ :=
  16 * ((1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f)

/-- **Landau's remainder is `O(R^{τ})`**: for `R ≥ 1`,
`landau f A B σ R ≤ landauA + landauB · R^τ`. -/
theorem landau_le {R : ℝ} (hR : 1 ≤ R) :
    landau f A B σ R ≤ landauA f A + landauB B σ * R ^ τ σ := by
  unfold FosterClassLandau.landau
  have hX := budget_le (f := f) (r := R) (by linarith)
  have hJ := (log_jensenM_le (f := f)) R
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := (L₀_nonneg (f := f))
  have hcq := cq_pos
  have hB := hf.B_nonneg
  have hmax : 0 ≤ max 0 (Real.log A) := le_max_left _ _
  set X := budget f A B σ R with hXdef
  set J := Real.log (jensenM f A B σ R / ‖f (1 / 2 : ℂ)‖) with hJdef
  have hXpos : 0 < X := budget_pos R
  have hJ' : J / Real.log (3 / 2) * Real.log 2 ≤ (L₀ f + X) * cq := by
    unfold cq
    rw [div_mul_eq_mul_div, mul_div_assoc]
    apply mul_le_mul_of_nonneg_right hJ (by positivity)
  have hnum : 16 * (X + J / Real.log (3 / 2) * Real.log 2) ≤ 16 * ((1 + cq) * X + cq * L₀ f) := by
    nlinarith
  have hpow1 : (1 / 2 + R) ^ σ ≤ 2 ^ σ * R ^ σ := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hf.σ_pos.le
  have hpow2 : R ^ σ ≤ R * R ^ τ σ := by
    have h1 : R ^ σ = R ^ (1 : ℝ) * R ^ (σ - 1) := by
      rw [← Real.rpow_add (by linarith)]
      ring_nf
    rw [h1, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact Real.rpow_le_rpow_of_exponent_le hR (le_max_left _ _)
  have hX' : (1 + cq) * X + cq * L₀ f ≤
      ((1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f) +
        (1 + cq) * (B * 2 ^ σ) * (R * R ^ τ σ) := by
    have h2 : B * (1 / 2 + R) ^ σ ≤ B * 2 ^ σ * (R * R ^ τ σ) := by
      calc B * (1 / 2 + R) ^ σ ≤ B * (2 ^ σ * R ^ σ) := mul_le_mul_of_nonneg_left hpow1 hB
        _ ≤ B * (2 ^ σ * (R * R ^ τ σ)) := by
            apply mul_le_mul_of_nonneg_left _ hB
            exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
        _ = B * 2 ^ σ * (R * R ^ τ σ) := by ring
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 1 + cq)
    nlinarith
  have hR0 : 0 < R := by linarith
  have hc0 : 0 ≤ (1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f := by positivity
  have hτ0 : 0 ≤ R ^ τ σ := Real.rpow_nonneg (by linarith) _
  calc 16 * (X + J / Real.log (3 / 2) * Real.log 2) / R
      ≤ 16 * ((1 + cq) * X + cq * L₀ f) / R := by gcongr
    _ ≤ 16 * (((1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f) +
          (1 + cq) * (B * 2 ^ σ) * (R * R ^ τ σ)) / R := by gcongr
    _ = 16 * ((1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f) / R +
          16 * (1 + cq) * (B * 2 ^ σ) * R ^ τ σ := by
        field_simp
    _ ≤ 16 * ((1 + cq) * (1 + max 0 (Real.log A) + L₀ f) + cq * L₀ f) +
          16 * (1 + cq) * (B * 2 ^ σ) * R ^ τ σ :=
        add_le_add_left (div_le_self (by positivity) hR) _
    _ = landauA f A + landauB B σ * R ^ τ σ := by
        unfold landauA landauB
        ring

/-! ## The global defect and Cauchy's estimate -/

omit hf in
/-- The global defect `2 ξ′/ξ − P′/P`. -/
def G (f : ℂ → ℂ) (z : ℂ) : ℂ := 2 * logDeriv f z - logDeriv (P f) z

omit hf in
/-- The nonzero set of `ξ`. -/
def U (f : ℂ → ℂ) : Set ℂ := {z | f z ≠ 0}

theorem isOpen_U : IsOpen (U f) := isOpen_ne_fun hf.diff.continuous continuous_const

theorem half_mem_U : (1 / 2 : ℂ) ∈ U f := hf.centre

theorem one_sub_mem_U {z : ℂ} (hz : z ∈ U f) : 1 - z ∈ U f := by
  show f (1 - z) ≠ 0
  rw [hf.symm]
  exact hz

theorem G_differentiableOn : DifferentiableOn ℂ (G f) (U f) := by
  unfold G
  exact ((logDeriv_differentiableOn (isOpen_U (f := f)) hf.diff.differentiableOn
    (fun z hz => hz)).const_mul 2).sub
    (logDeriv_differentiableOn (isOpen_U (f := f)) (differentiable_P (f := f)).differentiableOn
      (fun z hz => (P_ne_zero (f := f)) (mult_eq_zero_of_ne_zero (f := f) hz)))

/-- Cauchy's estimate at scale `r`. -/
theorem norm_deriv_G_le {w : ℂ} (hw : w ∈ U f) {r : ℝ} (hr : 0 < r) :
    ‖deriv (G f) w‖ ≤ bound f A B σ (8 * (‖w - 1 / 2‖ + r) + 8) / r := by
  have hR0 : 0 < 8 * (‖w - 1 / 2‖ + r) + 8 := by positivity
  have hw8 : ‖w - 1 / 2‖ < (8 * (‖w - 1 / 2‖ + r) + 8) / 8 := by linarith
  have hev : G f =ᶠ[𝓝 w] (F (f := f)) hR0 := by
    have hwU : ∀ᶠ z in 𝓝 w, z ∈ U f := isOpen_U.mem_nhds hw
    have hwb : ∀ᶠ z in 𝓝 w, z ∈ ball (1 / 2 : ℂ) ((8 * (‖w - 1 / 2‖ + r) + 8) / 2) :=
      isOpen_ball.mem_nhds (by
        rw [mem_ball, Complex.dist_eq]
        linarith)
    filter_upwards [hwU, hwb] with z hz hzb
    exact (F_eq (f := f) hR0 hzb hz).symm
  rw [hev.deriv_eq]
  have hsub : closedBall w r ⊆ ball (1 / 2 : ℂ) ((8 * (‖w - 1 / 2‖ + r) + 8) / 8) := by
    intro z hz
    rw [mem_closedBall, Complex.dist_eq] at hz
    rw [mem_ball, Complex.dist_eq]
    calc ‖z - 1 / 2‖ = ‖(z - w) + (w - 1 / 2)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖w - 1 / 2‖ := norm_add_le _ _
      _ < (8 * (‖w - 1 / 2‖ + r) + 8) / 8 := by linarith
  have hd : DiffContOnCl ℂ (F (f := f) hR0) (ball w r) :=
    (F_differentiableOn (f := f) hR0).diffContOnCl_ball (hsub.trans (ball_subset_ball (by linarith)))
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd
  intro z hz
  exact (norm_F_le (f := f)) hR0 (hsub (sphere_subset_closedBall hz))

/-! ## The estimate vanishes at infinity -/

/-- `(8(a + r) + 8)^τ / r → 0`, since `τ < 1`. -/
theorem tendsto_pow_lin_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun r : ℝ => (8 * (a + r) + 8) ^ τ σ / r) atTop (𝓝 0) := by
  have hτ0 := τ_nonneg σ
  have hτ1 := (τ_lt_one (f := f))
  have hlim : Tendsto (fun r : ℝ => (16 * (a + 1)) ^ τ σ * r ^ (τ σ - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - τ σ)).const_mul ((16 * (a + 1)) ^ τ σ)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    congr 1
    congr 1
    ring
  apply squeeze_zero' (g := fun r : ℝ => (16 * (a + 1)) ^ τ σ * r ^ (τ σ - 1))
  · filter_upwards [eventually_gt_atTop 0] with r hr
    positivity
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : 0 < r := by linarith
    have hle : 8 * (a + r) + 8 ≤ 16 * (a + 1) * r := by nlinarith
    have h1 : (8 * (a + r) + 8) ^ τ σ ≤ (16 * (a + 1) * r) ^ τ σ :=
      Real.rpow_le_rpow (by positivity) hle hτ0
    rw [Real.mul_rpow (by positivity) hr0.le] at h1
    rw [div_le_iff₀ hr0]
    calc (8 * (a + r) + 8) ^ τ σ ≤ (16 * (a + 1)) ^ τ σ * r ^ τ σ := h1
      _ = (16 * (a + 1)) ^ τ σ * r ^ (τ σ - 1) * r := by
          rw [mul_assoc, ← Real.rpow_add_one hr0.ne']
          ring_nf
  · exact hlim

theorem tendsto_bound_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun r : ℝ => 2 * (landauA f A + landauB B σ * (8 * (a + r) + 8) ^ τ σ) / r +
      (4 + (4 * a + 4) / r) * tailInvSq f (8 * (a + r) + 8)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun r : ℝ => 8 * (a + r) + 8) atTop atTop := by
    apply tendsto_atTop_add_const_right
    apply Tendsto.const_mul_atTop (by norm_num)
    exact tendsto_atTop_add_const_left _ _ tendsto_id
  have h1 : Tendsto (fun r : ℝ => 2 * (landauA f A + landauB B σ * (8 * (a + r) + 8) ^ τ σ) / r)
      atTop (𝓝 0) := by
    have hA : Tendsto (fun r : ℝ => 2 * landauA f A / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hB : Tendsto (fun r : ℝ => 2 * landauB B σ * ((8 * (a + r) + 8) ^ τ σ / r)) atTop
        (𝓝 (2 * landauB B σ * 0)) := (tendsto_pow_lin_div (f := f) ha).const_mul _
    rw [mul_zero] at hB
    have := hA.add hB
    rw [add_zero] at this
    refine this.congr ?_
    intro r
    ring
  have h2 : Tendsto (fun r : ℝ => (4 + (4 * a + 4) / r) * tailInvSq f (8 * (a + r) + 8)) atTop
      (𝓝 ((4 + 0) * 0)) := by
    apply Tendsto.mul
    · exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    · exact (tailInvSq_tendsto (f := f)).comp hlin
  rw [add_zero, mul_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

theorem deriv_G_eq_zero {w : ℂ} (hw : w ∈ U f) : deriv (G f) w = 0 := by
  set a := ‖w - 1 / 2‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hev : ∀ᶠ r in atTop, ‖deriv (G f) w‖ ≤
      2 * (landauA f A + landauB B σ * (8 * (a + r) + 8) ^ τ σ) / r +
        (4 + (4 * a + 4) / r) * tailInvSq f (8 * (a + r) + 8) := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : 0 < r := by linarith
    have hR1 : 1 ≤ 8 * (a + r) + 8 := by linarith
    have hl := (landau_le (f := f)) hR1
    have ht := (tailInvSq_nonneg (f := f)) (8 * (a + r) + 8)
    calc ‖deriv (G f) w‖ ≤ bound f A B σ (8 * (a + r) + 8) / r := (norm_deriv_G_le (f := f)) hw hr0
      _ = 2 * landau f A B σ (8 * (a + r) + 8) / r +
          (4 + (4 * a + 4) / r) * tailInvSq f (8 * (a + r) + 8) := by
          unfold bound
          field_simp
          ring
      _ ≤ 2 * (landauA f A + landauB B σ * (8 * (a + r) + 8) ^ τ σ) / r +
          (4 + (4 * a + 4) / r) * tailInvSq f (8 * (a + r) + 8) := by
          gcongr
  have := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_bound_div (f := f) ha0) hev
  exact norm_le_zero_iff.mp this

/-! ## The nonzero set is connected, and the defect is odd -/

theorem mult_ne_zero_of_eq_zero {z : ℂ} (hz : f z = 0) : mult f z ≠ 0 := by
  unfold mult
  have ha := hf.diff.analyticAt z
  rw [ha.meromorphicOrderAt_eq]
  have hne0 : analyticOrderAt f z ≠ 0 := by
    rw [Ne, ha.analyticOrderAt_eq_zero]
    push_neg
    exact hz
  have hnetop : analyticOrderAt f z ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro h
    have hall : EqOn f 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun x _ => hf.diff.analyticAt x) isPreconnected_univ (mem_univ z) h
    exact hf.centre (hall (mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.map_coe, WithTop.untop₀_coe, ne_eq, Nat.cast_eq_zero]
  exact_mod_cast hne0

theorem zeroSet_countable : {z : ℂ | f z = 0}.Countable := by
  have hsub : {z : ℂ | f z = 0} ⊆
      ⋃ n : ℕ, (fun u : Zero f => (u : ℂ)) '' {u : Zero f | ‖(u : ℂ) - 1 / 2‖ < n} := by
    intro z hz
    have hm : mult f z ≠ 0 := (mult_ne_zero_of_eq_zero (f := f)) hz
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z - 1 / 2‖
    exact mem_iUnion.mpr ⟨n, ⟨⟨z, hm⟩, hn, rfl⟩⟩
  exact (Set.countable_iUnion fun n : ℕ => ((finite_zero_ball (f := f) (n : ℝ)).image _).countable).mono hsub

theorem U_eq_compl : U f = {z : ℂ | f z = 0}ᶜ := by
  ext z
  simp [U]

theorem isPreconnected_U : IsPreconnected (U f) := by
  rw [U_eq_compl]
  exact (Set.Countable.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (zeroSet_countable (f := f))).isConnected.isPreconnected

theorem G_const {z : ℂ} (hz : z ∈ U f) : G f z = G f (1 / 2) :=
  isOpen_U.is_const_of_deriv_eq_zero (isPreconnected_U (f := f)) (G_differentiableOn (f := f))
    (fun w hw => (deriv_G_eq_zero (f := f)) hw) hz (half_mem_U (f := f))

omit hf in
theorem deriv_one_sub {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hsym : ∀ s, φ (1 - s) = φ s) (z : ℂ) :
    deriv φ (1 - z) = -deriv φ z := by
  have h1 : HasDerivAt (fun x => φ (1 - x)) (deriv φ (1 - z) * (-1)) z :=
    (hφ (1 - z)).hasDerivAt.comp z ((hasDerivAt_id z).const_sub 1)
  have h2 : (fun x => φ (1 - x)) = φ := funext hsym
  rw [h2] at h1
  rw [h1.deriv]
  ring

omit hf in
theorem logDeriv_one_sub {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hsym : ∀ s, φ (1 - s) = φ s)
    (z : ℂ) : logDeriv φ (1 - z) = -logDeriv φ z := by
  simp only [logDeriv_apply]
  rw [deriv_one_sub hφ hsym, hsym, neg_div]

theorem G_one_sub (z : ℂ) : G f (1 - z) = -G f z := by
  unfold G
  rw [logDeriv_one_sub hf.diff hf.symm,
    logDeriv_one_sub (differentiable_P (f := f)) (P_symm (f := f))]
  ring

theorem G_half : G f (1 / 2) = 0 := by
  have h := (G_one_sub (f := f)) (1 / 2)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  linear_combination h / 2

/-- **The defect vanishes: `2 ξ′/ξ = P′/P` off the zeros.** -/
theorem G_eq_zero {z : ℂ} (hz : f z ≠ 0) : G f z = 0 := by
  rw [(G_const (f := f)) hz, G_half]

/-! ## The Foster form and Hadamard's identity -/

/-- **The full Foster form**: off the zeros,
`ξ′/ξ(z) = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²)` over the zeros of `ξ`. -/
theorem foster_form {z : ℂ} (hz : f z ≠ 0) :
    logDeriv f z = ∑' u : Zero f, ((mult f (u : ℂ)).toNat : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) := by
  have hG := (G_eq_zero (f := f)) hz
  unfold G at hG
  rw [(logDeriv_P (f := f)) (mult_eq_zero_of_ne_zero (f := f) hz), tsum_tank_eq] at hG
  have h2 : ∑' u : Zero f, ((mult f (u : ℂ)).toNat : ℂ) *
      (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) =
      2 * ∑' u : Zero f, ((mult f (u : ℂ)).toNat : ℂ) *
        ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [h2] at hG
  linear_combination hG / 2

theorem P_half : P f (1 / 2) = 1 := by
  unfold P
  have h : ∀ i : Idx f, 1 + a i (1 / 2) = 1 := by
    intro i
    simp [a]
  simp only [h]
  exact tprod_one

/-- **Hadamard's identity: `ξ(z)² = ξ(½)² · P(z)` for every `z`.** -/
theorem sq_eq_centre_mul_P (z : ℂ) : f z ^ 2 = f (1 / 2) ^ 2 * P f z := by
  by_cases hz : f z ≠ 0
  · have hPz : P f z ≠ 0 := (P_ne_zero (f := f)) (mult_eq_zero_of_ne_zero (f := f) hz)
    have hq_diff : DifferentiableOn ℂ (fun w => f w ^ 2 / P f w) (U f) :=
      (hf.diff.pow 2).differentiableOn.div (differentiable_P (f := f)).differentiableOn
        (fun w hw => (P_ne_zero (f := f)) (mult_eq_zero_of_ne_zero (f := f) hw))
    have hq_deriv : ∀ w ∈ U f, deriv (fun w => f w ^ 2 / P f w) w = 0 := by
      intro w hw
      have hw' : f w ≠ 0 := hw
      have hPw := (P_ne_zero (f := f)) (mult_eq_zero_of_ne_zero (f := f) hw')
      have hlog : logDeriv (fun w => f w ^ 2 / P f w) w = G f w := by
        rw [logDeriv_div (f := fun w => f w ^ 2) (g := P f) w (pow_ne_zero 2 hw') hPw
          ((hf.diff.pow 2) w) (differentiable_P (f := f) w)]
        have hsq : (fun w => f w ^ 2) = fun w => f w * f w :=
          funext fun w => sq _
        rw [hsq, logDeriv_mul w hw' hw' (hf.diff w) (hf.diff w)]
        unfold G
        ring
      rw [(G_eq_zero (f := f)) hw', logDeriv_apply, div_eq_zero_iff] at hlog
      rcases hlog with h | h
      · exact h
      · exact absurd h (div_ne_zero (pow_ne_zero 2 hw') hPw)
    have hconst := isOpen_U.is_const_of_deriv_eq_zero (isPreconnected_U (f := f)) hq_diff hq_deriv hz
      (half_mem_U (f := f))
    simp only [P_half, div_one] at hconst
    rw [div_eq_iff hPz] at hconst
    rw [hconst]
  · push_neg at hz
    have hP : P f z = 0 := (P_eq_zero (f := f)) ⟨z, (mult_ne_zero_of_eq_zero (f := f)) hz⟩
    rw [hz, hP]
    ring

end Soma.Holonics.RH.FosterClassHadamard
