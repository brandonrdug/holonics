import ElementaryHolonics.RH.SimpleZeroPersists

/-!
# The continuous zero curve through a simple zero of `H_t`

Selecting, for each `t` near `t₀`, the unique zero of `H_t` in the square about a simple zero
`z₀` of `H_{t₀}` gives a function `ζ` with `ζ t₀ = z₀`, `H_t (ζ t) = 0`, `ζ t` simple, and `ζ`
continuous: the persistence statement applied at `(t, ζ t)` on smaller squares pins the selection
within any prescribed distance.
-/

open Complex Metric Filter Topology Set
open scoped Classical
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleCountStable
open Soma.Holonics.RH.HurwitzPolynomial
open Soma.Holonics.RH.SimpleZeroPersists
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth

namespace Soma.Holonics.RH.SimpleZeroCurve

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- The open square of half-side `η` about `z₀`. -/
def Q (z₀ : ℂ) (η : ℝ) : Set ℂ :=
  openRect (z₀ - (η : ℂ) * (1 + I)) (z₀ + (η : ℂ) * (1 + I))

theorem mem_Q_iff {z₀ : ℂ} {η : ℝ} (hη : 0 < η) {u : ℂ} :
    u ∈ Q z₀ η ↔ |u.re - z₀.re| < η ∧ |u.im - z₀.im| < η := by
  unfold Q
  constructor
  · intro h
    have := openRect_bounds (square_hzw z₀ hη) h
    rw [square_corner_re, square_corner_re', square_corner_im, square_corner_im'] at this
    rw [abs_lt, abs_lt]
    exact ⟨⟨by linarith [this.1.1], by linarith [this.1.2]⟩,
      ⟨by linarith [this.2.1], by linarith [this.2.2]⟩⟩
  · intro h
    apply mem_openRect_of_bounds (square_hzw z₀ hη)
    rw [square_corner_re, square_corner_re', square_corner_im, square_corner_im']
    rw [abs_lt, abs_lt] at h
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩

theorem center_mem_Q {z₀ : ℂ} {η : ℝ} (hη : 0 < η) : z₀ ∈ Q z₀ η := mem_openRect_square hη

theorem Q_subset {z₀ z₁ : ℂ} {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') (hz₁ : z₁ ∈ Q z₀ η)
    (h : η' ≤ η - |z₁.re - z₀.re|) (h' : η' ≤ η - |z₁.im - z₀.im|) : Q z₁ η' ⊆ Q z₀ η := by
  intro u hu
  rw [mem_Q_iff hη'] at hu
  rw [mem_Q_iff hη] at hz₁ ⊢
  constructor
  · calc |u.re - z₀.re| = |(u.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
      _ ≤ |u.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
      _ < η := by linarith [hu.1]
  · calc |u.im - z₀.im| = |(u.im - z₁.im) + (z₁.im - z₀.im)| := by ring_nf
      _ ≤ |u.im - z₁.im| + |z₁.im - z₀.im| := abs_add_le _ _
      _ < η := by linarith [hu.2]

/-- Persistence on every sufficiently small square. -/
theorem simple_zero_persists_small (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {t₀ : ℝ} {z₀ : ℂ} (h0 : heatE t₀ f z₀ = 0)
    (h1 : deriv (heatE t₀ f) z₀ ≠ 0) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ᶠ t in 𝓝 t₀,
      (∃! ζ, ζ ∈ Q z₀ η ∧ heatE t f ζ = 0) ∧
      ∀ ζ ∈ Q z₀ η, heatE t f ζ = 0 → deriv (heatE t f) ζ ≠ 0 := by
  set F := heatE t₀ f with hF
  have hFd : Differentiable ℂ F := differentiable_heatE hf hg hA hB hρ0 hρ2 t₀
  have hev : ∀ᶠ ζ in 𝓝[≠] z₀, F ζ ≠ 0 := (hFd z₀).hasDerivAt.eventually_ne (c := 0) h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε / 4, by positivity, ?_⟩
  intro η hη0 hηle
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
    have h' : (2 * Real.pi * I : ℂ) * 1 = 2 * Real.pi * I * n := by
      rw [mul_one]
      exact this
    have := mul_left_cancel₀ h2π h'
    exact_mod_cast this.symm
  filter_upwards [hn] with t ht
  have hw' : rectIntegral (logDeriv (heatE t f)) z w = 2 * Real.pi * I := by
    rw [ht.2.1, hn1]
    simp
  exact unique_zero_of_winding (differentiable_heatE hf hg hA hB hρ0 hρ2 t) hzw ht.1 hw'

/-- The selected zero of `H_t` in a set `S`, defaulting to `z₀`. -/
noncomputable def sel (f : ℂ → ℂ) (S : Set ℂ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  if h : ∃ ζ, ζ ∈ S ∧ heatE t f ζ = 0 then Classical.choose h else z₀

theorem sel_spec {S : Set ℂ} {z₀ : ℂ} {t : ℝ} (h : ∃ ζ, ζ ∈ S ∧ heatE t f ζ = 0) :
    sel f S z₀ t ∈ S ∧ heatE t f (sel f S z₀ t) = 0 := by
  unfold sel
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem sel_eq {S : Set ℂ} {z₀ : ℂ} {t : ℝ} (hu : ∃! ζ, ζ ∈ S ∧ heatE t f ζ = 0) {ζ : ℂ}
    (hζ : ζ ∈ S ∧ heatE t f ζ = 0) : sel f S z₀ t = ζ :=
  hu.unique (sel_spec hu.exists) hζ

/-- The continuous zero curve through a simple zero of `H_{t₀}`. -/
theorem exists_zero_curve (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {t₀ : ℝ} {z₀ : ℂ} (h0 : heatE t₀ f z₀ = 0)
    (h1 : deriv (heatE t₀ f) z₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ ζ : ℝ → ℂ, ζ t₀ = z₀ ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ContinuousAt ζ t) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ζ t ∈ Q z₀ η ∧ heatE t f (ζ t) = 0 ∧
        deriv (heatE t f) (ζ t) ≠ 0 ∧ ∀ u ∈ Q z₀ η, heatE t f u = 0 → u = ζ t := by
  obtain ⟨η₀, hη₀, hpers⟩ := simple_zero_persists_small hf hg hA hB hρ0 hρ2 h0 h1
  have hev := hpers η₀ hη₀ le_rfl
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  have hP : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      (∃! ζ, ζ ∈ Q z₀ η₀ ∧ heatE t f ζ = 0) ∧
      ∀ ζ ∈ Q z₀ η₀, heatE t f ζ = 0 → deriv (heatE t f) ζ ≠ 0 := by
    intro t ht
    apply hεP
    rw [Real.dist_eq, abs_lt]
    rw [mem_Ioo] at ht
    constructor <;> linarith
  refine ⟨η₀, hη₀, ε, hε, sel f (Q z₀ η₀) z₀, ?_, ?_, ?_⟩
  · have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by
      rw [mem_Ioo]
      constructor <;> linarith
    exact sel_eq (hP t₀ ht₀).1 ⟨center_mem_Q hη₀, h0⟩
  · intro t₁ ht₁
    obtain ⟨hu₁, hs₁⟩ := hP t₁ ht₁
    set z₁ := sel f (Q z₀ η₀) z₀ t₁ with hz₁
    have hz₁spec : z₁ ∈ Q z₀ η₀ ∧ heatE t₁ f z₁ = 0 := sel_spec hu₁.exists
    have hz₁simple : deriv (heatE t₁ f) z₁ ≠ 0 := hs₁ z₁ hz₁spec.1 hz₁spec.2
    obtain ⟨η₁, hη₁, hpers₁⟩ :=
      simple_zero_persists_small hf hg hA hB hρ0 hρ2 hz₁spec.2 hz₁simple
    rw [Metric.continuousAt_iff]
    intro δ hδ
    have hb := (mem_Q_iff hη₀).mp hz₁spec.1
    set d₁ := η₀ - |z₁.re - z₀.re| with hd₁
    set d₂ := η₀ - |z₁.im - z₀.im| with hd₂
    have hd₁0 : 0 < d₁ := by linarith [hb.1]
    have hd₂0 : 0 < d₂ := by linarith [hb.2]
    set η' := min η₁ (min (δ / 4) (min d₁ d₂)) with hη'
    have hη'0 : 0 < η' := lt_min hη₁ (lt_min (by positivity) (lt_min hd₁0 hd₂0))
    have hη'1 : η' ≤ η₁ := min_le_left _ _
    have hη'δ : η' ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have hη'd₁ : η' ≤ d₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hη'd₂ : η' ≤ d₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hsub : Q z₁ η' ⊆ Q z₀ η₀ := Q_subset hη₀ hη'0 hz₁spec.1 hη'd₁ hη'd₂
    have hev' := hpers₁ η' hη'0 hη'1
    have hIoo : ∀ᶠ t in 𝓝 t₁, t ∈ Ioo (t₀ - ε) (t₀ + ε) := isOpen_Ioo.eventually_mem ht₁
    obtain ⟨ε', hε', hε'P⟩ := Metric.eventually_nhds_iff.mp (hev'.and hIoo)
    refine ⟨ε', hε', fun t ht => ?_⟩
    obtain ⟨⟨hu', _⟩, ht'⟩ := hε'P ht
    obtain ⟨ζ', hζ', _⟩ := hu'
    have hsel : sel f (Q z₀ η₀) z₀ t = ζ' := sel_eq (hP t ht').1 ⟨hsub hζ'.1, hζ'.2⟩
    rw [dist_eq_norm, hsel]
    have hb' := (mem_Q_iff hη'0).mp hζ'.1
    calc ‖ζ' - z₁‖ ≤ |(ζ' - z₁).re| + |(ζ' - z₁).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < η' + η' := by
          rw [sub_re, sub_im]
          linarith [hb'.1, hb'.2]
      _ ≤ δ := by linarith
  · intro t ht
    obtain ⟨hu, hs⟩ := hP t ht
    have hspec : sel f (Q z₀ η₀) z₀ t ∈ Q z₀ η₀ ∧ heatE t f (sel f (Q z₀ η₀) z₀ t) = 0 :=
      sel_spec hu.exists
    exact ⟨hspec.1, hspec.2, hs _ hspec.1 hspec.2, fun u hu' hu0 => (sel_eq hu ⟨hu', hu0⟩).symm⟩

/-- The continuous zero curve through a simple zero of `H_{t₀} = e^{−t₀D²} Ξ`. -/
theorem exists_zero_curve_riemannXi {t₀ : ℝ} {z₀ : ℂ} (h0 : heatE t₀ riemannXi z₀ = 0)
    (h1 : deriv (heatE t₀ riemannXi) z₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ ζ : ℝ → ℂ, ζ t₀ = z₀ ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ContinuousAt ζ t) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ζ t ∈ Q z₀ η ∧ heatE t riemannXi (ζ t) = 0 ∧
        deriv (heatE t riemannXi) (ζ t) ≠ 0 ∧
        ∀ u ∈ Q z₀ η, heatE t riemannXi u = 0 → u = ζ t :=
  exists_zero_curve differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) h0 h1

end Soma.Holonics.RH.SimpleZeroCurve
