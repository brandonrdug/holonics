import Mathlib
import ElementaryHolonics.RH.FosterClassHadamard

/-!
# FT3 (iii): the principal-value (comb (f := f)) (flux (f := f)) at a simple zero of `ξ`

At a simple zero `z₀` of `ξ`, the velocity law of `ZeroDynamicsEntire` reads `ż = ξ″(z₀)/ξ′(z₀)`.
This owner expands the right side over the other zeros in principal-value order about `½`:

```text
ξ″(z₀)/ξ′(z₀) = lim_{R → ∞} 2 Σ_{u ∈ D(½, R), u ≠ z₀} m_u / (z₀ − u).
```

The route: `ξ = (z − z₀) g` near `z₀` with `g` analytic and `g(z₀) = ξ′(z₀) ≠ 0`, so
`ξ′/ξ − 1/(z − z₀) = g′/g` is analytic near `z₀` and `ξ″(z₀)/ξ′(z₀) = 2 g′(z₀)/g(z₀)`. The (comb (f := f)) of
the half disc minus its `z₀` term is analytic near `z₀` and, on a small circle about `z₀`, differs
from `g′/g` by the (tail (f := f)) of the Foster series (FT3 (i)); the maximum principle transports the bound
to the centre. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassFlux

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.FosterTanks
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.FosterClassSplit
open Soma.Holonics.RH.FosterClassHadamard
open scoped Classical

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-! ## The (comb (f := f)) of the half disc and its distance to `ξ′/ξ` -/

/-- The (comb (f := f)) of the half disc of radius `R/2`: `Σ_ρ m_ρ/(z − ρ)`. -/
def comb {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) / (z - ρ)

theorem f_eq_zero_of_mem {R : ℝ} (hR : 0 < R) {ρ : ℂ} (hρ : ρ ∈ (Zfac (f := f) hR).zeros) :
    f ρ = 0 := by
  by_contra h
  exact ((mem_zeros_iff (f := f) hR ρ).mp hρ).1 (mult_eq_zero_of_ne_zero (f := f) h)

theorem comb_eq_tankSum {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : f z ≠ 0) :
    (comb (f := f)) hR z = ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) := by
  unfold comb
  apply flux_eq_tankSum (Zfac (f := f) hR).refl_mem (Zfac (f := f) hR).refl_mult
  intro ρ hρ h
  rw [h] at hz
  exact hz (f_eq_zero_of_mem (f := f) hR hρ)

/-- **The (comb (f := f)) approximates `ξ′/ξ` on the disc of radius `R/8`**, to within the (tail (f := f)) of the
inverse squares. -/
theorem norm_logDeriv_sub_comb_le {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ closedBall (1 / 2 : ℂ) (R / 8)) (hξ : f z ≠ 0) :
    ‖logDeriv f z - (comb (f := f)) hR z‖ ≤ 2 * ‖z - 1 / 2‖ * tailInvSq f R := by
  have hz' : z ∈ ball (1 / 2 : ℂ) (R / 2) := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hm : mult f z = 0 := (mult_eq_zero_of_ne_zero (f := f)) hξ
  have hG := (G_eq_zero (f := f)) hξ
  unfold G at hG
  rw [(logDeriv_P (f := f)) hm, (tsum_tank_split (f := f)) hR hz', (sum_tank_T (f := f)) hR z] at hG
  rw [(comb_eq_tankSum (f := f)) hR hξ]
  have hkey : logDeriv f z - ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) = logDeriv (tail (f := f) hR) z / 2 := by
    linear_combination hG / 2
  rw [hkey, norm_div]
  have h1 := (norm_logDeriv_tail_le (f := f)) hR hz
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

/-! ## The local form at a simple zero -/

/-- At a simple zero, `mult f z₀ = 1` and `ξ = (z − z₀) g` near `z₀` with `g` analytic and
`g(z₀) = ξ′(z₀)`. -/
theorem simple_zero_local {z₀ : ℂ} (hz₀ : f z₀ = 0) (hs : deriv f z₀ ≠ 0) :
    mult f z₀ = 1 ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = deriv f z₀ ∧
      (∀ᶠ z in 𝓝 z₀, f z = (z - z₀) * g z) := by
  have ha := hf.diff.analyticAt z₀
  have hnetop : analyticOrderAt f z₀ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro h
    have hall : EqOn f 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun x _ => hf.diff.analyticAt x) isPreconnected_univ (mem_univ z₀) h
    exact hf.centre (hall (mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  obtain ⟨g, hg, hg0, hev⟩ := ha.analyticOrderAt_eq_natCast.mp hn.symm
  have hev' : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n * g z :=
    hev.mono fun z hz => by rw [hz, smul_eq_mul]
  have hd : HasDerivAt f
      ((n : ℂ) * (z₀ - z₀) ^ (n - 1) * 1 * g z₀ + (z₀ - z₀) ^ n * deriv g z₀) z₀ := by
    have h1 : HasDerivAt (fun z => (z - z₀) ^ n) ((n : ℂ) * (z₀ - z₀) ^ (n - 1) * 1) z₀ :=
      ((hasDerivAt_id' z₀).sub_const z₀).pow n
    have h2 : HasDerivAt g (deriv g z₀) z₀ := hg.differentiableAt.hasDerivAt
    exact (h1.mul h2).congr_of_eventuallyEq hev'
  have hd' := hd.deriv
  cases n with
  | zero =>
    exfalso
    have := hev'.self_of_nhds
    simp only [pow_zero, one_mul] at this
    rw [hz₀] at this
    exact hg0 this.symm
  | succ k =>
    cases k with
    | zero =>
      refine ⟨?_, g, hg, ?_, ?_⟩
      · unfold mult
        rw [ha.meromorphicOrderAt_eq, ← hn]
        simp
      · rw [hd']
        simp
      · exact hev'.mono fun z hz => by rw [hz, pow_one]
    | succ k =>
      exfalso
      apply hs
      rw [hd']
      simp

theorem deriv_deriv_eq {z₀ : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g z₀)
    (hev : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) * g z) :
    deriv (deriv f) z₀ = 2 * deriv g z₀ := by
  have hev' : f =ᶠ[𝓝 z₀] fun z => (z - z₀) * g z := hev
  have h1 : deriv f =ᶠ[𝓝 z₀] fun z => g z + (z - z₀) * deriv g z := by
    filter_upwards [hg.eventually_analyticAt, hev'.eventuallyEq_nhds] with z hz hz'
    rw [hz'.deriv_eq]
    exact (((hasDerivAt_id z).sub_const z₀).mul hz.differentiableAt.hasDerivAt).deriv.trans
      (by simp)
  rw [h1.deriv_eq]
  have h2 : HasDerivAt (fun z => g z + (z - z₀) * deriv g z)
      (deriv g z₀ + (1 * deriv g z₀ + (z₀ - z₀) * deriv (deriv g) z₀)) z₀ :=
    hg.differentiableAt.hasDerivAt.add
      (((hasDerivAt_id z₀).sub_const z₀).mul hg.deriv.differentiableAt.hasDerivAt)
  rw [h2.deriv]
  ring

theorem logDeriv_eq_local {z₀ : ℂ} {g : ℂ → ℂ} {δ : ℝ}
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - z₀) * g y)
    {z : ℂ} (hz : dist z z₀ < δ) (hne : z ≠ z₀) :
    logDeriv f z = 1 / (z - z₀) + logDeriv g z := by
  have hev : f =ᶠ[𝓝 z] fun y => (y - z₀) * g y := by
    filter_upwards [Metric.ball_mem_nhds z (show 0 < δ - dist z z₀ by linarith)] with y hy
    rw [mem_ball] at hy
    exact (hball y (by linarith [dist_triangle y z z₀])).2
  rw [logDeriv_congr hev, logDeriv_mul (f := fun y => y - z₀) (g := g) z (sub_ne_zero.mpr hne)
    (hball z hz).1.2 ((differentiable_id.sub_const z₀) z) (hball z hz).1.1.differentiableAt]
  congr 1
  rw [logDeriv_apply, ((hasDerivAt_id' z).sub_const z₀).deriv]

/-! ## The (comb (f := f)) with its `z₀` term removed -/

/-- The (comb (f := f)) of the half disc without the term at `z₀`. -/
def comb' {R : ℝ} (hR : 0 < R) (z₀ z : ℂ) : ℂ :=
  ∑ ρ ∈ (Zfac (f := f) hR).zeros.erase z₀, ((Zfac (f := f) hR).mult ρ : ℂ) / (z - ρ)

theorem comb'_eq {R : ℝ} (hR : 0 < R) {z₀ : ℂ} (hz₀ : z₀ ∈ (Zfac (f := f) hR).zeros)
    (hm : (Zfac (f := f) hR).mult z₀ = 1) (z : ℂ) :
    (comb (f := f)) hR z = 1 / (z - z₀) + (comb' (f := f)) hR z₀ z := by
  unfold comb comb'
  rw [← Finset.add_sum_erase _ _ hz₀, hm]
  simp

/-- **The (comb (f := f)) without its `z₀` term is within the (tail (f := f)) of `g′/g(z₀)`**, by the maximum
principle on a small disc about `z₀`. -/
theorem comb'_sub_le {z₀ : ℂ} {g : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - z₀) * g y)
    {R : ℝ} (hR : 0 < R) (hz₀ : z₀ ∈ (Zfac (f := f) hR).zeros) (hm : (Zfac (f := f) hR).mult z₀ = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8) :
    ‖(comb' (f := f)) hR z₀ z₀ - logDeriv g z₀‖ ≤ 2 * (‖z₀ - 1 / 2‖ + δ / 2) * tailInvSq f R := by
  have hδ' : 0 < δ / 2 := by positivity
  have hcomb : DifferentiableOn ℂ (comb' (f := f) hR z₀) (ball z₀ δ) := by
    unfold comb'
    have hfun : (fun z => ∑ ρ ∈ (Zfac (f := f) hR).zeros.erase z₀, ((Zfac (f := f) hR).mult ρ : ℂ) / (z - ρ)) =
        ∑ ρ ∈ (Zfac (f := f) hR).zeros.erase z₀, (fun z => ((Zfac (f := f) hR).mult ρ : ℂ) / (z - ρ)) := by
      funext z
      rw [Finset.sum_apply]
    rw [hfun]
    apply DifferentiableOn.sum
    intro ρ hρ
    apply DifferentiableOn.div (differentiableOn_const _)
      (differentiableOn_id.sub (differentiableOn_const _))
    intro z hz h
    rw [sub_eq_zero] at h
    subst h
    have hρ' := Finset.mem_erase.mp hρ
    have hξ : f z = 0 := (f_eq_zero_of_mem (f := f)) hR hρ'.2
    rw [(hball z hz).2] at hξ
    exact mul_ne_zero (sub_ne_zero.mpr hρ'.1) (hball z hz).1.2 hξ
  have hlogg : DifferentiableOn ℂ (logDeriv g) (ball z₀ δ) :=
    logDeriv_differentiableOn isOpen_ball
      (fun y hy => (hball y hy).1.1.differentiableAt.differentiableWithinAt)
      (fun y hy => (hball y hy).1.2)
  have hdiff : DifferentiableOn ℂ (fun z => (comb' (f := f)) hR z₀ z - logDeriv g z) (ball z₀ δ) :=
    hcomb.sub hlogg
  have hcl : closedBall z₀ (δ / 2) ⊆ ball z₀ δ := closedBall_subset_ball (by linarith)
  have hd : DiffContOnCl ℂ (fun z => (comb' (f := f)) hR z₀ z - logDeriv g z) (ball z₀ (δ / 2)) :=
    hdiff.diffContOnCl_ball hcl
  have hbd : ∀ z ∈ frontier (ball z₀ (δ / 2)),
      ‖(comb' (f := f)) hR z₀ z - logDeriv g z‖ ≤ 2 * (‖z₀ - 1 / 2‖ + δ / 2) * tailInvSq f R := by
    rw [frontier_ball z₀ hδ'.ne']
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hzne : z ≠ z₀ := by
      intro h
      rw [h, sub_self, norm_zero] at hz
      linarith
    have hzδ : dist z z₀ < δ := by
      rw [Complex.dist_eq, hz]
      linarith
    have hξz : f z ≠ 0 := by
      rw [(hball z hzδ).2]
      exact mul_ne_zero (sub_ne_zero.mpr hzne) (hball z hzδ).1.2
    have hzb : ‖z - 1 / 2‖ ≤ ‖z₀ - 1 / 2‖ + δ / 2 := by
      calc ‖z - 1 / 2‖ = ‖(z - z₀) + (z₀ - 1 / 2)‖ := by congr 1; ring
        _ ≤ ‖z - z₀‖ + ‖z₀ - 1 / 2‖ := norm_add_le _ _
        _ = ‖z₀ - 1 / 2‖ + δ / 2 := by rw [hz]; ring
    have hz8 : z ∈ closedBall (1 / 2 : ℂ) (R / 8) := by
      rw [mem_closedBall, Complex.dist_eq]
      linarith
    have h1 := (norm_logDeriv_sub_comb_le (f := f)) hR hz8 hξz
    have h2 := logDeriv_eq_local hball hzδ hzne
    have h3 := (comb'_eq (f := f)) hR hz₀ hm z
    have h4 : (comb' (f := f)) hR z₀ z - logDeriv g z = -(logDeriv f z - (comb (f := f)) hR z) := by
      rw [h2, h3]
      ring
    rw [h4, norm_neg]
    calc ‖logDeriv f z - (comb (f := f)) hR z‖ ≤ 2 * ‖z - 1 / 2‖ * tailInvSq f R := h1
      _ ≤ 2 * (‖z₀ - 1 / 2‖ + δ / 2) * tailInvSq f R := by
          apply mul_le_mul_of_nonneg_right _ (tailInvSq_nonneg (f := f) R)
          linarith
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hbd
    (subset_closure (mem_ball_self hδ'))

/-! ## The port's (comb (f := f)) is the (comb (f := f)) of the half disc -/

theorem finsum_eq_comb' {R : ℝ} (h2R : 0 < 2 * R) (z₀ : ℂ) :
    ∑ᶠ u, (if u = z₀ then (0 : ℂ) else
        (MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u : ℂ) / (z₀ - u)) =
      (comb' (f := f)) h2R z₀ z₀ := by
  have hhalf : 2 * R / 2 = R := by ring
  unfold comb'
  rw [finsum_eq_sum_of_support_subset (s := (Zfac (f := f) h2R).zeros.erase z₀)]
  · apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_erase.mp hu
    rw [if_neg hu'.1]
    congr 1
    have hmem : u ∈ closedBall (1 / 2 : ℂ) R := by
      have := ((mem_zeros_iff (f := f) h2R u).mp hu'.2).2
      rwa [hhalf] at this
    rw [(mult_eq_divisor (f := f)) hmem, (Zfac_mult_eq (f := f)) h2R hu'.2, ← Int.cast_natCast,
      Int.toNat_of_nonneg (mult_nonneg (f := f) u)]
  · intro u hu
    rw [Function.mem_support] at hu
    by_cases h : u = z₀
    · rw [if_pos h] at hu
      exact absurd rfl hu
    · rw [if_neg h] at hu
      refine Finset.mem_erase.mpr ⟨h, ?_⟩
      have hdiv : MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u ≠ 0 := by
        intro h0
        apply hu
        rw [h0]
        simp
      have hmem : u ∈ closedBall (1 / 2 : ℂ) R :=
        (MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R)).supportWithinDomain
          (Function.mem_support.mpr hdiv)
      rw [(mem_zeros_iff (f := f)) h2R, hhalf]
      refine ⟨?_, hmem⟩
      rwa [← (mult_eq_divisor (f := f)) hmem]

/-! ## The (flux (f := f)) -/

/-- **The principal-value (comb (f := f)) (flux (f := f)) at a simple zero of `ξ`**: the (comb (f := f)) of the disc `D(½, R)`
without its `z₀` term, doubled, tends to `ξ″(z₀)/ξ′(z₀)` as `R → ∞`. -/
theorem flux {z₀ : ℂ} (hz₀ : f z₀ = 0) (hs : deriv f z₀ ≠ 0) :
    Tendsto (fun R : ℝ => 2 * ∑ᶠ u, if u = z₀ then (0 : ℂ) else
        (MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u : ℂ) / (z₀ - u))
      atTop (𝓝 (deriv (deriv f) z₀ / deriv f z₀)) := by
  obtain ⟨hm1, g, hg, hg0, hev⟩ := (simple_zero_local (f := f)) hz₀ hs
  have hg0' : g z₀ ≠ 0 := by rw [hg0]; exact hs
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0')).and hev)
  have hlim : deriv (deriv f) z₀ / deriv f z₀ = 2 * logDeriv g z₀ := by
    rw [deriv_deriv_eq hg hev, logDeriv_apply, ← hg0]
    ring
  rw [hlim]
  set a := ‖z₀ - 1 / 2‖ + δ / 2 with ha
  have ha0 : 0 < a := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tailInvSq_tendsto (f := f)) (ε / (4 * a + 1)) (by positivity)
  refine ⟨max N₁ (8 * a + 1), fun R hR => ?_⟩
  have hRN : N₁ ≤ R := le_trans (le_max_left _ _) hR
  have hRa : 8 * a + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have h2R : 0 < 2 * R := by linarith
  have hτ := hN₁ (2 * R) (by linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tailInvSq_nonneg (f := f) _)] at hτ
  have hz₀mem : z₀ ∈ (Zfac (f := f) h2R).zeros := by
    rw [(mem_zeros_iff (f := f)) h2R]
    refine ⟨by rw [hm1]; exact one_ne_zero, ?_⟩
    rw [mem_closedBall, Complex.dist_eq]
    linarith
  have hm : (Zfac (f := f) h2R).mult z₀ = 1 := by
    rw [(Zfac_mult_eq (f := f)) h2R hz₀mem, hm1]
    rfl
  have hest := (comb'_sub_le (f := f)) hδ hball h2R hz₀mem hm (by linarith)
  rw [(finsum_eq_comb' (f := f)) h2R z₀, dist_eq_norm, ← mul_sub, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hτ' : tailInvSq f (2 * R) * (4 * a + 1) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hτ
  have hτ0 := (tailInvSq_nonneg (f := f)) (2 * R)
  calc 2 * ‖(comb' (f := f)) h2R z₀ z₀ - logDeriv g z₀‖ ≤ 2 * (2 * a * tailInvSq f (2 * R)) := by gcongr
    _ < ε := by nlinarith

end Soma.Holonics.RH.FosterClassFlux
