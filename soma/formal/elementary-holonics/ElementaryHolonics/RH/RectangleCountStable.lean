import ElementaryHolonics.RH.RectangleWindingContinuity
import ElementaryHolonics.RH.FactorizationMultiplicity
import ElementaryHolonics.RH.ZeroFactorizationExists
import ElementaryHolonics.RH.HurwitzPolynomial
import ElementaryHolonics.RH.XiGrowth

/-!
# The interior zero count of `H_t` is locally constant in `t`

For an entire `f` nonvanishing on the boundary of a rectangle, the corpus zero factorization about
a corner and the rectangle argument principle write `∮ f′/f = 2πi · n` with `n` the divisor sum of
`f` over the open rectangle.  For the flow `H_t` the integral is continuous in `t`, so the integer
`n` is locally constant: no zero of `H_t` appears or disappears inside the rectangle while none is
on its boundary.  In particular pairs of `H_t = e^{−tD²} Ξ` inside a rectangle can only leave
through its boundary.
-/

open Complex Metric Filter Topology Set Finset
open scoped Interval Classical
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatEquationEntire
open Soma.Holonics.RH.HeatFlowContinuity
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleWindingContinuity
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth

namespace Soma.Holonics.RH.RectangleCountStable

variable {f : ℂ → ℂ} {A B ρ : ℝ}

theorem corner_mem_boundaryRect (z w : ℂ) : z ∈ boundaryRect z w := by
  have := bottom_mem (z := z) (w := w) (x := z.re) left_mem_uIcc
  rwa [Complex.re_add_im] at this

/-- The radius about the corner `z` whose half-ball contains the closed rectangle. -/
noncomputable def cornerRadius (z w : ℂ) : ℝ := 2 * (2 * (‖z‖ + ‖w‖) + ‖z‖ + 1)

theorem cornerRadius_pos (z w : ℂ) : 0 < cornerRadius z w := by
  unfold cornerRadius
  positivity

theorem closedRect_subset_ball_corner (z w : ℂ) :
    closedRect z w ⊆ ball z (cornerRadius z w / 2) := by
  intro ζ hζ
  rw [mem_ball, dist_eq_norm, cornerRadius,
    show 2 * (2 * (‖z‖ + ‖w‖) + ‖z‖ + 1) / 2 = 2 * (‖z‖ + ‖w‖) + ‖z‖ + 1 by ring]
  have := norm_le_of_mem_closedRect hζ
  calc ‖ζ - z‖ ≤ ‖ζ‖ + ‖z‖ := norm_sub_le _ _
    _ < 2 * (‖z‖ + ‖w‖) + ‖z‖ + 1 := by linarith

/-- The zeros of a factorization are zeros of `f`. -/
theorem eq_zero_of_mem_zeros {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization f z₀ r) (hr : 0 < r)
    {ρ : ℂ} (hρ : ρ ∈ Z.zeros) : f ρ = 0 := by
  have hmem : ρ ∈ ball z₀ r := by
    have := Z.zeros_mem ρ hρ
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith
  rw [Z.factor ρ hmem]
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero hρ
  rw [sub_self]
  exact zero_pow (Z.mult_pos ρ hρ).ne'

/-- The winding integral of an entire function around a rectangle avoiding its zeros is `2πi`
times the divisor sum over the open rectangle, a natural number. -/
theorem exists_count (hf : Differentiable ℂ f) {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hne : ∀ ζ ∈ boundaryRect z w, f ζ ≠ 0) :
    ∃ n : ℕ, rectIntegral (logDeriv f) z w = 2 * Real.pi * I * n ∧
      ∑ᶠ u, ((MeromorphicOn.divisor f (openRect z w)) u : ℂ) = n := by
  have hr0 := cornerRadius_pos z w
  have hz0 : f z ≠ 0 := hne z (corner_mem_boundaryRect z w)
  obtain ⟨Z⟩ := ZeroFactorizationExists.exists_zeroFactorization hf hr0 hz0
  have hrect := closedRect_subset_ball_corner z w
  have hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w :=
    fun ρ hρ hb => hne ρ hb (eq_zero_of_mem_zeros Z hr0 hρ)
  have hh : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (closedRect z w) := differentiableOn_const _
  have key := RectangleArgumentPrinciple.rectIntegral_mul_logDeriv Z hr0 hzw hrect hh hbd
  have hfun : (fun ζ => (1 : ℂ) * logDeriv f ζ) = logDeriv f := by
    funext ζ
    rw [one_mul]
  rw [hfun] at key
  simp only [mul_one] at key
  refine ⟨∑ ρ ∈ Z.zeros, if ρ ∈ openRect z w then Z.mult ρ else 0, ?_, ?_⟩
  · rw [key]
    push_cast
    rfl
  · have hU : openRect z w ⊆ ball z (cornerRadius z w / 2) :=
      (openRect_subset_closedRect z w).trans hrect
    have := FactorizationMultiplicity.finsum_divisor_eq Z hf.differentiableOn hr0 hU (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    push_cast
    rfl

/-- The interior zero count of `H_t` is locally constant in `t` while no zero is on the
boundary. -/
theorem eventually_count_eq (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    {t₀ : ℝ} (hne : ∀ ζ ∈ boundaryRect z w, heatE t₀ f ζ ≠ 0) :
    ∃ n : ℕ, ∀ᶠ t in 𝓝 t₀, (∀ ζ ∈ boundaryRect z w, heatE t f ζ ≠ 0) ∧
      rectIntegral (logDeriv (heatE t f)) z w = 2 * Real.pi * I * n ∧
      ∑ᶠ u, ((MeromorphicOn.divisor (heatE t f) (openRect z w)) u : ℂ) = n := by
  obtain ⟨n₀, hn₀, _⟩ := exists_count (differentiable_heatE hf hg hA hB hρ0 hρ2 t₀) hzw hne
  refine ⟨n₀, ?_⟩
  obtain ⟨m, hm0, hev⟩ := eventually_boundary_ge hf hg hA hB hρ0 hρ2 hne
  have hcont := continuousAt_rectIntegral_logDeriv hf hg hA hB hρ0 hρ2 hne
  have hev2 : ∀ᶠ t in 𝓝 t₀, ‖rectIntegral (logDeriv (heatE t f)) z w -
      rectIntegral (logDeriv (heatE t₀ f)) z w‖ < 1 := by
    have := hcont.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hev, hev2] with t ht ht2
  have hne_t : ∀ ζ ∈ boundaryRect z w, heatE t f ζ ≠ 0 :=
    fun ζ hζ => norm_pos_iff.mp (lt_of_lt_of_le hm0 (ht ζ hζ))
  obtain ⟨n, hn, hdiv⟩ := exists_count (differentiable_heatE hf hg hA hB hρ0 hρ2 t) hzw hne_t
  have hnn : n = n₀ := by
    apply HurwitzPolynomial.nat_eq_of_norm_sub_lt
    rw [hn, hn₀, ← mul_sub, norm_mul] at ht2
    have h2π : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [norm_mul, Real.pi_pos.le]
    rw [h2π] at ht2
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.two_le_pi) (norm_nonneg ((n : ℂ) - (n₀ : ℂ)))]
  subst hnn
  exact ⟨hne_t, hn, hdiv⟩

/-- Pairs of `H_t = e^{−tD²} Ξ` inside a rectangle can only leave through its boundary. -/
theorem eventually_count_eq_riemannXi {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im) {t₀ : ℝ}
    (hne : ∀ ζ ∈ boundaryRect z w, heatE t₀ riemannXi ζ ≠ 0) :
    ∃ n : ℕ, ∀ᶠ t in 𝓝 t₀, (∀ ζ ∈ boundaryRect z w, heatE t riemannXi ζ ≠ 0) ∧
      rectIntegral (logDeriv (heatE t riemannXi)) z w = 2 * Real.pi * I * n ∧
      ∑ᶠ u, ((MeromorphicOn.divisor (heatE t riemannXi) (openRect z w)) u : ℂ) = n :=
  eventually_count_eq differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) hzw hne

end Soma.Holonics.RH.RectangleCountStable
