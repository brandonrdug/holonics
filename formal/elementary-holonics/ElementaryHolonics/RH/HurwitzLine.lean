import Mathlib
import ElementaryHolonics.RH.RectangleCountStable

/-!
# FT4 (iii): Hurwitz on a rectangle — zeros of a locally uniform limit

If entire `F n → G` locally uniformly along a countably generated filter, `G` has no zero on the
boundary of a rectangle, and eventually `F n` has no zero inside it, then `G` has no zero inside:
the winding integrals `rectIntegral (logDeriv (F n))` converge to `rectIntegral (logDeriv G)` by
dominated convergence on the four edges, each is `2πi` times the interior count, and the counts are
eventually zero. Hence a limit of functions whose zeros lie on the seam `Re z = ½` has its zeros on
the seam unless it vanishes identically. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.HurwitzLine

open Complex Metric Filter Topology Set MeasureTheory
open scoped Interval Classical
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleWindingContinuity
open Soma.Holonics.RH.RectangleCountStable

variable {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
variable {F : ι → ℂ → ℂ} {G : ℂ → ℂ}

/-- Uniform convergence on a compact set, with the derivatives. -/
theorem tendstoUniformlyOn_deriv (hF : ∀ᶠ n in l, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F G l) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn F G l K ∧ TendstoUniformlyOn (fun n => deriv (F n)) (deriv G) l K := by
  have h1 : TendstoLocallyUniformlyOn F G l univ := by
    rw [tendstoLocallyUniformlyOn_univ]
    exact hlim
  have h2 : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv G) l univ :=
    h1.deriv (hF.mono fun n hn => hn.differentiableOn) isOpen_univ
  constructor
  · exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp h1 K (subset_univ _) hK
  · exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp h2 K (subset_univ _) hK

/-- On a compact set where `G` does not vanish, `F n` is eventually bounded below. -/
theorem eventually_norm_ge (hlim : TendstoUniformlyOn F G l K) (hK : IsCompact K)
    (hGc : ContinuousOn G K) (hne : ∀ ζ ∈ K, G ζ ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ n in l, ∀ ζ ∈ K, m ≤ ‖F n ζ‖ := by
  rcases K.eq_empty_or_nonempty with h | hKne
  · exact ⟨1, one_pos, Eventually.of_forall fun n ζ hζ => by rw [h] at hζ; exact absurd hζ (notMem_empty ζ)⟩
  obtain ⟨ζ₀, hζ₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hGc)
  have hm : 0 < ‖G ζ₀‖ := norm_pos_iff.mpr (hne ζ₀ hζ₀)
  refine ⟨‖G ζ₀‖ / 2, by positivity, ?_⟩
  have := (Metric.tendstoUniformlyOn_iff.mp hlim) (‖G ζ₀‖ / 2) (by positivity)
  filter_upwards [this] with n hn ζ hζ
  have h1 := hn ζ hζ
  have h2 : ‖G ζ₀‖ ≤ ‖G ζ‖ := hmin hζ
  rw [dist_eq_norm] at h1
  have := norm_sub_norm_le (G ζ) (F n ζ)
  linarith

/-- The edge integrals of the log-derivatives converge. -/
theorem tendsto_edge (hF : ∀ᶠ n in l, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) {K : Set ℂ} (hK : IsCompact K)
    (hne : ∀ ζ ∈ K, G ζ ≠ 0) {e : ℝ → ℂ} (he : Continuous e) {a b : ℝ}
    (hedge : ∀ x ∈ [[a, b]], e x ∈ K) :
    Tendsto (fun n => ∫ x in a..b, logDeriv (F n) (e x)) l (𝓝 (∫ x in a..b, logDeriv G (e x))) := by
  obtain ⟨hu, hu'⟩ := tendstoUniformlyOn_deriv hF hlim hK
  obtain ⟨m, hm, hev⟩ := eventually_norm_ge hu hK hG.continuous.continuousOn hne
  -- a uniform bound on the derivatives
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ζ ∈ K, ‖deriv G ζ‖ ≤ M := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.deriv.continuous.continuousOn
    exact ⟨M, hM⟩
  have hev' : ∀ᶠ n in l, ∀ ζ ∈ K, ‖deriv (F n) ζ‖ ≤ M + 1 := by
    have := (Metric.tendstoUniformlyOn_iff.mp hu') 1 one_pos
    filter_upwards [this] with n hn ζ hζ
    have h1 := hn ζ hζ
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (deriv (F n) ζ) (deriv G ζ)
    linarith [hM ζ hζ, abs_sub_comm ‖deriv (F n) ζ‖ ‖deriv G ζ‖,
      norm_sub_rev (deriv G ζ) (deriv (F n) ζ)]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (M + 1) / m)
  · filter_upwards [hF] with n hn
    have h1 : Measurable (fun x => deriv (F n) (e x)) := (hn.deriv.continuous.comp he).measurable
    have h2 : Measurable (fun x => F n (e x)) := (hn.continuous.comp he).measurable
    exact (h1.div h2).aestronglyMeasurable
  · filter_upwards [hev, hev'] with n hn hn'
    refine Eventually.of_forall fun x hx => ?_
    have hxK := hedge x (uIoc_subset_uIcc hx)
    rw [logDeriv_apply, norm_div]
    have h1 := hn (e x) hxK
    have h2 := hn' (e x) hxK
    rw [div_le_div_iff₀ (lt_of_lt_of_le hm h1) hm]
    nlinarith [norm_nonneg (deriv (F n) (e x))]
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun x hx => ?_
    have hxK := hedge x (uIoc_subset_uIcc hx)
    simp only [logDeriv_apply]
    exact (hu'.tendsto_at hxK).div (hu.tendsto_at hxK) (hne _ hxK)


/-- **The winding integrals converge.** -/
theorem tendsto_rectIntegral (hF : ∀ᶠ n in l, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) {z w : ℂ}
    (hne : ∀ ζ ∈ boundaryRect z w, G ζ ≠ 0) :
    Tendsto (fun n => rectIntegral (logDeriv (F n)) z w) l (𝓝 (rectIntegral (logDeriv G) z w)) := by
  unfold rectIntegral
  have hK := isCompact_boundaryRect z w
  have hb := tendsto_edge hF hG hlim hK hne (e := fun x : ℝ => (x : ℂ) + z.im * I) (by fun_prop)
    (a := z.re) (b := w.re) (fun x hx => bottom_mem hx)
  have ht := tendsto_edge hF hG hlim hK hne (e := fun x : ℝ => (x : ℂ) + w.im * I) (by fun_prop)
    (a := z.re) (b := w.re) (fun x hx => top_mem hx)
  have hr := tendsto_edge hF hG hlim hK hne (e := fun y : ℝ => (w.re : ℂ) + y * I) (by fun_prop)
    (a := z.im) (b := w.im) (fun y hy => right_mem hy)
  have hl := tendsto_edge hF hG hlim hK hne (e := fun y : ℝ => (z.re : ℂ) + y * I) (by fun_prop)
    (a := z.im) (b := w.im) (fun y hy => left_mem hy)
  exact ((hb.sub ht).add (hr.const_smul I)).sub (hl.const_smul I)

theorem divisor_eq_zero_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {U : Set ℂ} {u : ℂ}
    (hu : u ∈ U) (h0 : f u ≠ 0) : MeromorphicOn.divisor f U u = 0 := by
  rw [MeromorphicOn.divisor_apply (fun v _ => (hf.analyticAt v).meromorphicAt) hu]
  have ha := hf.analyticAt u
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr h0]
  simp

theorem divisor_pos_of_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : ∃ x, f x ≠ 0)
    {U : Set ℂ} {u : ℂ} (hu : u ∈ U) (h0 : f u = 0) : 0 < MeromorphicOn.divisor f U u := by
  rw [MeromorphicOn.divisor_apply (fun v _ => (hf.analyticAt v).meromorphicAt) hu]
  have ha := hf.analyticAt u
  rw [ha.meromorphicOrderAt_eq]
  have hne0 : analyticOrderAt f u ≠ 0 := by
    rw [Ne, ha.analyticOrderAt_eq_zero]
    push_neg
    exact h0
  have hnetop : analyticOrderAt f u ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro h
    obtain ⟨x, hx⟩ := hf0
    have hall : EqOn f 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun y _ => hf.analyticAt y) isPreconnected_univ (mem_univ u) h
    exact hx (hall (mem_univ x))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  have : n ≠ 0 := by exact_mod_cast hne0
  omega

/-- **Hurwitz on a rectangle**: if `F n → G` locally uniformly, `G ≠ 0` on the boundary, and
`F n` has eventually no zero inside, then `G` has no zero inside. -/
theorem no_zero_of_eventually (hF : ∀ᶠ n in l, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hne : ∀ ζ ∈ boundaryRect z w, G ζ ≠ 0)
    (hno : ∀ᶠ n in l, ∀ ζ ∈ openRect z w, F n ζ ≠ 0) :
    ∀ ζ ∈ openRect z w, G ζ ≠ 0 := by
  obtain ⟨n₀, hn₀, hcount⟩ := exists_count hG hzw hne
  have hK := isCompact_boundaryRect z w
  obtain ⟨hu, _⟩ := tendstoUniformlyOn_deriv hF hlim hK
  obtain ⟨m, hm, hbd⟩ := eventually_norm_ge hu hK hG.continuous.continuousOn hne
  have hev : ∀ᶠ n in l, rectIntegral (logDeriv (F n)) z w = 0 := by
    filter_upwards [hF, hno, hbd] with n hn hno' hbd'
    have hbd'' : ∀ ζ ∈ boundaryRect z w, F n ζ ≠ 0 := fun ζ hζ =>
      norm_pos_iff.mp (lt_of_lt_of_le hm (hbd' ζ hζ))
    obtain ⟨k, hk, hc⟩ := exists_count hn hzw hbd''
    have hzero : ∀ u, ((MeromorphicOn.divisor (F n) (openRect z w)) u : ℂ) = 0 := by
      intro u
      by_cases hu : u ∈ openRect z w
      · rw [divisor_eq_zero_of_ne_zero hn hu (hno' u hu)]
        simp
      · have : MeromorphicOn.divisor (F n) (openRect z w) u = 0 := by
          by_contra h
          exact hu ((MeromorphicOn.divisor (F n) (openRect z w)).supportWithinDomain
            (Function.mem_support.mpr h))
        rw [this]
        simp
    have hk0 : (k : ℂ) = 0 := by
      rw [← hc]
      simp [hzero]
    rw [hk, hk0, mul_zero]
  have hlimw := tendsto_rectIntegral hF hG hlim hne
  have hw0 : rectIntegral (logDeriv G) z w = 0 :=
    tendsto_nhds_unique hlimw (tendsto_const_nhds.congr' (hev.mono fun n h => h.symm))
  rw [hw0] at hn₀
  have hn0 : (n₀ : ℂ) = 0 := by
    have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) I_ne_zero
    rcases mul_eq_zero.mp hn₀.symm with h | h
    · exact absurd h h2
    · exact h
  rw [hn0] at hcount
  intro ζ hζ hGζ
  have hG0 : ∃ x, G x ≠ 0 := ⟨z, hne z (corner_mem_boundaryRect z w)⟩
  have hpos := divisor_pos_of_eq_zero hG hG0 hζ hGζ
  -- the divisor sum is at least the divisor at ζ
  have hfinC := (MeromorphicOn.divisor G (closedRect z w)).finiteSupport (isCompact_closedRect z w)
  have hsub : Function.support (MeromorphicOn.divisor G (openRect z w)) ⊆
      Function.support (MeromorphicOn.divisor G (closedRect z w)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have huU : u ∈ openRect z w := (MeromorphicOn.divisor G (openRect z w)).supportWithinDomain hu
    have huC : u ∈ closedRect z w := openRect_subset_closedRect z w huU
    rw [MeromorphicOn.divisor_apply (fun v _ => (hG.analyticAt v).meromorphicAt) huU] at hu
    rw [MeromorphicOn.divisor_apply (fun v _ => (hG.analyticAt v).meromorphicAt) huC]
    exact hu
  have hfin := hfinC.subset hsub
  have hnn : ∀ u, 0 ≤ MeromorphicOn.divisor G (openRect z w) u :=
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun v _ => hG.analyticAt v))
  have hsumZ : ((∑ᶠ u, MeromorphicOn.divisor G (openRect z w) u : ℤ) : ℂ) = 0 := by
    have h := map_finsum (Int.castRingHom ℂ) hfin
    simp only [Int.coe_castRingHom] at h
    rw [h]
    exact hcount
  have hsumZ' : ∑ᶠ u, MeromorphicOn.divisor G (openRect z w) u = 0 := by exact_mod_cast hsumZ
  have hge : MeromorphicOn.divisor G (openRect z w) ζ ≤
      ∑ᶠ u, MeromorphicOn.divisor G (openRect z w) u := by
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
    apply Finset.single_le_sum (fun u _ => hnn u)
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    exact hpos.ne'
  omega

/-- **A locally uniform limit of seam-zeroed entire functions has its zeros on the seam**, unless
it vanishes identically. -/
theorem zeros_on_seam (hF : ∀ᶠ n in l, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) (hG0 : ∃ x, G x ≠ 0)
    (hseam : ∀ᶠ n in l, ∀ ζ, F n ζ = 0 → ζ.re = 1 / 2) :
    ∀ ζ, G ζ = 0 → ζ.re = 1 / 2 := by
  intro ζ₀ hζ₀
  by_contra hre
  have hd : 0 < |ζ₀.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hre)
  -- the zero is isolated
  have hiso : ∀ᶠ ζ in 𝓝[≠] ζ₀, G ζ ≠ 0 := by
    rcases (hG.analyticAt ζ₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hG0
      have hall : EqOn G 0 univ :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun y _ => hG.analyticAt y) isPreconnected_univ (mem_univ ζ₀) h
      exact hx (hall (mem_univ x))
    · exact h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hiso
  set δ : ℝ := min (ε / 4) (|ζ₀.re - 1 / 2| / 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδd : δ ≤ |ζ₀.re - 1 / 2| / 2 := min_le_right _ _
  set z : ℂ := ζ₀ - δ - δ * I with hz
  set w : ℂ := ζ₀ + δ + δ * I with hw
  have hzre : z.re = ζ₀.re - δ := by simp [hz]
  have hwre : w.re = ζ₀.re + δ := by simp [hw]
  have hzim : z.im = ζ₀.im - δ := by simp [hz]
  have hwim : w.im = ζ₀.im + δ := by simp [hw]
  have hzw : z.re < w.re ∧ z.im < w.im := by
    rw [hzre, hwre, hzim, hwim]
    constructor <;> linarith
  -- points of the closed rectangle are within `2δ ≤ ε` of `ζ₀`
  have hclose : ∀ ζ ∈ closedRect z w, dist ζ ζ₀ < ε := by
    intro ζ hζ
    have h1 : ζ.re ∈ [[z.re, w.re]] := hζ.1
    have h2 : ζ.im ∈ [[z.im, w.im]] := hζ.2
    rw [hzre, hwre, uIcc_of_le (by linarith)] at h1
    rw [hzim, hwim, uIcc_of_le (by linarith)] at h2
    have hre' : |ζ.re - ζ₀.re| ≤ δ := abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have him' : |ζ.im - ζ₀.im| ≤ δ := abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
    calc dist ζ ζ₀ ≤ |ζ.re - ζ₀.re| + |ζ.im - ζ₀.im| := by
          rw [Complex.dist_eq]
          have := Complex.norm_le_abs_re_add_abs_im (ζ - ζ₀)
          simpa using this
      _ ≤ 2 * δ := by linarith
      _ < ε := by linarith
  have hζ₀mem : ζ₀ ∈ openRect z w := by
    apply mem_openRect_of_bounds hzw
    rw [hzre, hwre, hzim, hwim]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hne : ∀ ζ ∈ boundaryRect z w, G ζ ≠ 0 := by
    intro ζ hζ
    apply hball ⟨Metric.mem_ball.mpr (hclose ζ hζ.1), ?_⟩
    intro h
    apply hζ.2
    rw [h]
    exact hζ₀mem
  have hno : ∀ᶠ n in l, ∀ ζ ∈ openRect z w, F n ζ ≠ 0 := by
    filter_upwards [hseam] with n hn ζ hζ h0
    have hre2 := hn ζ h0
    have hb := openRect_bounds hzw hζ
    rw [hzre, hwre, hre2] at hb
    rcases abs_cases (ζ₀.re - 1 / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hb.1.1, hb.1.2]
  exact no_zero_of_eventually hF hG hlim hzw hne hno ζ₀ hζ₀mem hζ₀

end Soma.Holonics.RH.HurwitzLine
