import ElementaryHolonics.RH.RectangleCountStable
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A simple zero of `H_{t₀}` persists as a unique simple zero of `H_t` for `t` near `t₀`

A simple zero has analytic order one, so the winding of `H_{t₀}` around a small square about it
is `2πi`.  By local constancy of the count, the winding of `H_t` around the same square is `2πi`
for `t` near `t₀`, and a winding of `2πi` means exactly one zero inside, of multiplicity one.
This is the existence and uniqueness half of the implicit function theorem for the zero curve,
obtained from the argument principle rather than from joint differentiability.
-/

open Complex Metric Filter Topology Set Finset
open scoped Interval Classical
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleWindingContinuity
open Soma.Holonics.RH.RectangleCountStable
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.HurwitzPolynomial
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth

namespace Soma.Holonics.RH.SimpleZeroPersists

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- A simple zero has analytic order one. -/
theorem analyticOrderAt_eq_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ} (h0 : F z₀ = 0)
    (h1 : deriv F z₀ ≠ 0) : analyticOrderAt F z₀ = 1 := by
  show analyticOrderAt F z₀ = ((1 : ℕ) : ℕ∞)
  rw [(hF.analyticAt z₀).analyticOrderAt_eq_natCast]
  refine ⟨dslope F z₀, ?_, ?_, ?_⟩
  · have : DifferentiableOn ℂ (dslope F z₀) univ :=
      (differentiableOn_dslope univ_mem).mpr hF.differentiableOn
    exact (this.analyticOnNhd isOpen_univ) z₀ (mem_univ _)
  · rw [dslope_same]
    exact h1
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [pow_one, sub_smul_dslope, h0, sub_zero]

/-- Analytic order one means a simple zero. -/
theorem deriv_ne_zero_of_analyticOrderAt_eq_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ}
    (h : analyticOrderAt F z₀ = 1) : deriv F z₀ ≠ 0 := by
  have h' : analyticOrderAt F z₀ = ((1 : ℕ) : ℕ∞) := h
  rw [(hF.analyticAt z₀).analyticOrderAt_eq_natCast] at h'
  obtain ⟨g, hg, hg0, hev⟩ := h'
  have hev' : F =ᶠ[𝓝 z₀] fun z => (z - z₀) * g z := by
    filter_upwards [hev] with z hz
    rw [hz, pow_one, smul_eq_mul]
  rw [hev'.deriv_eq]
  have hd : HasDerivAt (fun z => (z - z₀) * g z) (1 * g z₀ + (z₀ - z₀) * deriv g z₀) z₀ :=
    ((hasDerivAt_id z₀).sub_const z₀).mul hg.differentiableAt.hasDerivAt
  rw [hd.deriv]
  simpa using hg0

/-- In the half-ball the factorization's zeros are exactly the zeros of `F`. -/
theorem mem_zeros_iff {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (Z : ZeroFactorization F c r) (hr : 0 < r)
    {u : ℂ} (hu : u ∈ ball c (r / 2)) : u ∈ Z.zeros ↔ F u = 0 := by
  constructor
  · exact fun h => eq_zero_of_mem_zeros Z hr h
  · intro h
    have hmem : u ∈ ball c r := ball_subset_ball (by linarith) hu
    rw [Z.factor u hmem] at h
    rcases mul_eq_zero.mp h with h | h
    · obtain ⟨ρ, hρ, hρ0⟩ := Finset.prod_eq_zero_iff.mp h
      have : u - ρ = 0 := (pow_eq_zero_iff (Z.mult_pos ρ hρ).ne').mp hρ0
      rw [sub_eq_zero] at this
      rw [this]
      exact hρ
    · exact absurd h (Z.unit_ne u hu)

/-- The winding integral of an entire function nonvanishing on the boundary, through the
factorization about the corner. -/
theorem exists_factorization_winding {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im) (hne : ∀ ζ ∈ boundaryRect z w, F ζ ≠ 0) :
    ∃ Z : ZeroFactorization F z (cornerRadius z w),
      rectIntegral (logDeriv F) z w =
        2 * Real.pi * I * ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then (Z.mult ρ : ℂ) else 0) := by
  have hr0 := cornerRadius_pos z w
  have hz0 : F z ≠ 0 := hne z (corner_mem_boundaryRect z w)
  obtain ⟨Z⟩ := ZeroFactorizationExists.exists_zeroFactorization hF hr0 hz0
  have hrect := closedRect_subset_ball_corner z w
  have hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w :=
    fun ρ hρ hb => hne ρ hb (eq_zero_of_mem_zeros Z hr0 hρ)
  have hh : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (closedRect z w) := differentiableOn_const _
  have key := RectangleArgumentPrinciple.rectIntegral_mul_logDeriv Z hr0 hzw hrect hh hbd
  have hfun : (fun ζ => (1 : ℂ) * logDeriv F ζ) = logDeriv F := by
    funext ζ
    rw [one_mul]
  rw [hfun] at key
  simp only [mul_one] at key
  exact ⟨Z, key⟩

/-- If the only zero of `F` in the closed rectangle is the simple zero `z₀` in the interior, the
winding is `2πi`. -/
theorem winding_eq_of_unique {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im) (hne : ∀ ζ ∈ boundaryRect z w, F ζ ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ openRect z w) (h0 : F z₀ = 0) (h1 : deriv F z₀ ≠ 0)
    (huniq : ∀ u ∈ closedRect z w, F u = 0 → u = z₀) :
    rectIntegral (logDeriv F) z w = 2 * Real.pi * I := by
  obtain ⟨Z, key⟩ := exists_factorization_winding hF hzw hne
  have hr0 := cornerRadius_pos z w
  have hrect := closedRect_subset_ball_corner z w
  have hz₀ball : z₀ ∈ ball z (cornerRadius z w / 2) :=
    hrect (openRect_subset_closedRect z w hz₀)
  have hz₀mem : z₀ ∈ Z.zeros := (mem_zeros_iff Z hr0 hz₀ball).mpr h0
  have hsum : ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then (Z.mult ρ : ℂ) else 0) = 1 := by
    rw [Finset.sum_eq_single z₀]
    · rw [if_pos hz₀]
      have := FactorizationMultiplicity.analyticOrderAt_eq_mult Z hF.differentiableOn hr0 hz₀mem
        hz₀ball
      rw [analyticOrderAt_eq_one hF h0 h1] at this
      have hm : Z.mult z₀ = 1 := by exact_mod_cast this.symm
      rw [hm]
      simp
    · intro ρ hρ hρne
      rw [if_neg]
      intro hin
      exact hρne (huniq ρ (openRect_subset_closedRect z w hin) (eq_zero_of_mem_zeros Z hr0 hρ))
    · intro h
      exact absurd hz₀mem h
  rw [key, hsum, mul_one]

/-- A winding of `2πi` means exactly one zero in the open rectangle, and it is simple. -/
theorem unique_zero_of_winding {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im) (hne : ∀ ζ ∈ boundaryRect z w, F ζ ≠ 0)
    (hw : rectIntegral (logDeriv F) z w = 2 * Real.pi * I) :
    (∃! ζ, ζ ∈ openRect z w ∧ F ζ = 0) ∧
      ∀ ζ ∈ openRect z w, F ζ = 0 → deriv F ζ ≠ 0 := by
  obtain ⟨Z, key⟩ := exists_factorization_winding hF hzw hne
  have hr0 := cornerRadius_pos z w
  have hrect := closedRect_subset_ball_corner z w
  have h2π : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hsumC : ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then (Z.mult ρ : ℂ) else 0) = 1 := by
    rw [key] at hw
    have := hw
    rw [show (2 * Real.pi * I : ℂ) = 2 * Real.pi * I * 1 by ring] at this
    nth_rewrite 2 [show (2 * Real.pi * I : ℂ) = 2 * Real.pi * I * 1 by ring] at hw
    exact mul_left_cancel₀ h2π hw
  have hsumN : ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then Z.mult ρ else 0) = 1 := by
    have : ((∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then Z.mult ρ else 0) : ℕ) : ℂ) = 1 := by
      push_cast
      exact hsumC
    exact_mod_cast this
  set S := Z.zeros.filter (fun ρ => ρ ∈ openRect z w) with hS
  have hSsum : ∑ ρ ∈ S, Z.mult ρ = 1 := by
    rw [hS, Finset.sum_filter]
    exact hsumN
  have hcard_le : S.card ≤ 1 := by
    have := Finset.card_nsmul_le_sum S Z.mult 1
      (fun ρ hρ => Z.mult_pos ρ (Finset.mem_filter.mp hρ).1)
    rw [hSsum, smul_eq_mul, mul_one] at this
    exact this
  have hcard_ne : S.card ≠ 0 := by
    intro h
    rw [Finset.card_eq_zero] at h
    rw [h, Finset.sum_empty] at hSsum
    exact zero_ne_one hSsum
  have hcard : S.card = 1 := le_antisymm hcard_le (Nat.one_le_iff_ne_zero.mpr hcard_ne)
  obtain ⟨ρ₀, hρ₀⟩ := Finset.card_eq_one.mp hcard
  have hρ₀mem : ρ₀ ∈ S := by
    rw [hρ₀]
    exact Finset.mem_singleton_self _
  have hρ₀zeros : ρ₀ ∈ Z.zeros := (Finset.mem_filter.mp hρ₀mem).1
  have hρ₀in : ρ₀ ∈ openRect z w := (Finset.mem_filter.mp hρ₀mem).2
  have hρ₀ball : ρ₀ ∈ ball z (cornerRadius z w / 2) :=
    hrect (openRect_subset_closedRect z w hρ₀in)
  have hmult : Z.mult ρ₀ = 1 := by
    rw [hρ₀, Finset.sum_singleton] at hSsum
    exact hSsum
  have hzero_mem : ∀ ζ ∈ openRect z w, F ζ = 0 → ζ = ρ₀ := by
    intro ζ hζ hF0
    have hζball : ζ ∈ ball z (cornerRadius z w / 2) := hrect (openRect_subset_closedRect z w hζ)
    have hζS : ζ ∈ S := Finset.mem_filter.mpr ⟨(mem_zeros_iff Z hr0 hζball).mpr hF0, hζ⟩
    rw [hρ₀] at hζS
    exact Finset.mem_singleton.mp hζS
  refine ⟨⟨ρ₀, ⟨hρ₀in, eq_zero_of_mem_zeros Z hr0 hρ₀zeros⟩, fun ζ hζ => hzero_mem ζ hζ.1 hζ.2⟩, ?_⟩
  intro ζ hζ hF0
  rw [hzero_mem ζ hζ hF0]
  apply deriv_ne_zero_of_analyticOrderAt_eq_one hF
  rw [FactorizationMultiplicity.analyticOrderAt_eq_mult Z hF.differentiableOn hr0 hρ₀zeros hρ₀ball,
    hmult]
  rfl

/-- The square of half-side `η` about `z₀`. -/
theorem square_hzw (z₀ : ℂ) {η : ℝ} (hη : 0 < η) :
    (z₀ - (η : ℂ) * (1 + I)).re < (z₀ + (η : ℂ) * (1 + I)).re ∧
      (z₀ - (η : ℂ) * (1 + I)).im < (z₀ + (η : ℂ) * (1 + I)).im := by
  rw [square_corner_re, square_corner_re', square_corner_im, square_corner_im']
  constructor <;> linarith

/-- A simple zero of `H_{t₀}` persists as the unique zero of `H_t` in a small square about it,
and that zero is simple, for all `t` near `t₀`. -/
theorem simple_zero_persists (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {t₀ : ℝ} {z₀ : ℂ} (h0 : heatE t₀ f z₀ = 0)
    (h1 : deriv (heatE t₀ f) z₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t in 𝓝 t₀,
      (∃! ζ, ζ ∈ openRect (z₀ - (η : ℂ) * (1 + I)) (z₀ + (η : ℂ) * (1 + I)) ∧
        heatE t f ζ = 0) ∧
      ∀ ζ ∈ openRect (z₀ - (η : ℂ) * (1 + I)) (z₀ + (η : ℂ) * (1 + I)),
        heatE t f ζ = 0 → deriv (heatE t f) ζ ≠ 0 := by
  set F := heatE t₀ f with hF
  have hFd : Differentiable ℂ F := differentiable_heatE hf hg hA hB hρ0 hρ2 t₀
  -- isolation of the simple zero
  have hev : ∀ᶠ ζ in 𝓝[≠] z₀, F ζ ≠ 0 := (hFd z₀).hasDerivAt.eventually_ne (c := 0) h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set η : ℝ := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  set z := z₀ - (η : ℂ) * (1 + I) with hz
  set w := z₀ + (η : ℂ) * (1 + I) with hw
  have hzw := square_hzw z₀ hη0
  have huniq : ∀ u ∈ closedRect z w, F u = 0 → u = z₀ := by
    intro u hu hu0
    by_contra hne
    have hd : ‖u - z₀‖ ≤ 2 * η := norm_sub_le_of_mem_closedRect_square hη0 hu
    have hmem : u ∈ ball z₀ ε ∩ {z₀}ᶜ := by
      refine ⟨?_, hne⟩
      rw [mem_ball, dist_eq_norm]
      linarith
    exact hball hmem hu0
  have hz₀in : z₀ ∈ openRect z w := mem_openRect_square hη0
  have hne : ∀ ζ ∈ boundaryRect z w, F ζ ≠ 0 := by
    intro ζ hζ hζ0
    have := huniq ζ (boundaryRect_subset_closedRect z w hζ) hζ0
    rw [this] at hζ
    exact hζ.2 hz₀in
  have hwind : rectIntegral (logDeriv F) z w = 2 * Real.pi * I :=
    winding_eq_of_unique hFd hzw hne hz₀in h0 h1 huniq
  obtain ⟨n, hn⟩ := eventually_count_eq hf hg hA hB hρ0 hρ2 hzw hne
  have hn₀ := hn.self_of_nhds
  have hn1 : n = 1 := by
    have h2π : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have := hn₀.2.1
    rw [hwind] at this
    have h' : (2 * Real.pi * I : ℂ) * 1 = 2 * Real.pi * I * n := by rw [mul_one]; exact this
    have := mul_left_cancel₀ h2π h'
    exact_mod_cast this.symm
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hn] with t ht
  have hw' : rectIntegral (logDeriv (heatE t f)) z w = 2 * Real.pi * I := by
    rw [ht.2.1, hn1]
    simp
  exact unique_zero_of_winding (differentiable_heatE hf hg hA hB hρ0 hρ2 t) hzw ht.1 hw'

/-- The same for `H_t = e^{−tD²} Ξ`: a simple pair moves as a unique simple zero. -/
theorem simple_zero_persists_riemannXi {t₀ : ℝ} {z₀ : ℂ} (h0 : heatE t₀ riemannXi z₀ = 0)
    (h1 : deriv (heatE t₀ riemannXi) z₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t in 𝓝 t₀,
      (∃! ζ, ζ ∈ openRect (z₀ - (η : ℂ) * (1 + I)) (z₀ + (η : ℂ) * (1 + I)) ∧
        heatE t riemannXi ζ = 0) ∧
      ∀ ζ ∈ openRect (z₀ - (η : ℂ) * (1 + I)) (z₀ + (η : ℂ) * (1 + I)),
        heatE t riemannXi ζ = 0 → deriv (heatE t riemannXi) ζ ≠ 0 :=
  simple_zero_persists differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) h0 h1

end Soma.Holonics.RH.SimpleZeroPersists
