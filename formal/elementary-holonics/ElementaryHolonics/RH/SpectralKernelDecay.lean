import ElementaryHolonics.RH.ExplicitFormulaReceiver
import ElementaryHolonics.RH.ExplicitFormulaLimit

/-!
# The spectral kernel of a Weil test function decays on every strip

The spectral kernel `ĥ(s) = ∫ e^{(s − ½)x} g(x) dx` of a smooth compactly supported kernel `g`
is, on the line `Re s = σ`, the Fourier transform of `e^{(σ − ½)x} g(x)`.  Integrating by parts
`k` times (Mathlib's `fourier_iteratedDeriv`) gives `|ĥ(σ + it)| ≤ ‖∂^k(e^{(σ−½)x} g)‖_{L¹} / |t|^k`,
and the `L¹` norm is bounded uniformly for `σ` in a compact interval through the Leibniz bound
and the compact support.  Hence `‖ĥ(x + it)‖ ≤ K / (1 + |t|)^k` on every strip, which is the
decay hypothesis of the explicit formula in the limit.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ContDiff
open Soma.Holonics.RH.ExplicitFormulaLimit
open Soma.Holonics.RH.ExplicitFormulaReceiver

namespace Soma.Holonics.RH.SpectralKernelDecay

variable (T : WeilTestFunction)

/-! ## The exponential weight -/

/-- The exponential weight `e^{a x}` as a complex-valued function of a real variable. -/
noncomputable def expWeight (a : ℝ) (x : ℝ) : ℂ := Complex.exp ((a : ℂ) * x)

theorem hasDerivAt_expWeight (a x : ℝ) :
    HasDerivAt (expWeight a) ((a : ℂ) * Complex.exp ((a : ℂ) * x)) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp ((a : ℂ) * z)) (Complex.exp ((a : ℂ) * x) * a)
      (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul (a : ℂ)).cexp
  have h2 := h1.comp_ofReal
  unfold expWeight
  exact h2.congr_deriv (by ring)

theorem iteratedDeriv_expWeight (a : ℝ) (n : ℕ) :
    iteratedDeriv n (expWeight a) = fun x : ℝ => (a : ℂ) ^ n * Complex.exp ((a : ℂ) * x) := by
  induction n with
  | zero => funext x; simp [expWeight]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h := ((hasDerivAt_expWeight a x).const_mul ((a : ℂ) ^ n))
    have h' : HasDerivAt (fun x : ℝ => (a : ℂ) ^ n * Complex.exp ((a : ℂ) * x))
        ((a : ℂ) ^ n * ((a : ℂ) * Complex.exp ((a : ℂ) * x))) x := by
      simpa [expWeight] using h
    rw [h'.deriv]
    ring

theorem contDiff_expWeight (a : ℝ) (N : ℕ) : ContDiff ℝ N (expWeight a) := by
  unfold expWeight
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem norm_iteratedDeriv_expWeight (a : ℝ) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (expWeight a) x‖ = |a| ^ n * Real.exp (a * x) := by
  rw [iteratedDeriv_expWeight]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]

/-! ## The weighted kernel and its Fourier transform -/

/-- The weighted kernel `e^{(σ − ½)x} g(x)`. -/
noncomputable def weighted (σ : ℝ) : ℝ → ℂ := expWeight (σ - 1 / 2) * T.arithmeticKernel

theorem weighted_apply (σ x : ℝ) :
    weighted T σ x = Complex.exp (((σ - 1 / 2 : ℝ) : ℂ) * x) * T.arithmeticKernel x := rfl

theorem contDiff_weighted (σ : ℝ) (N : ℕ) : ContDiff ℝ N (weighted T σ) :=
  (contDiff_expWeight _ N).mul (T.smooth.of_le le_top)

theorem hasCompactSupport_weighted (σ : ℝ) : HasCompactSupport (weighted T σ) :=
  T.compactSupport.mul_left

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  have : iteratedDeriv n f =
      (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => (1 : ℝ)) ∘
        iteratedFDeriv ℝ n f :=
    funext fun x => iteratedDeriv_eq_iteratedFDeriv
  rw [this]
  exact (hf.iteratedFDeriv n).comp_left (by simp)

theorem integrable_iteratedDeriv_weighted (σ : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (weighted T σ)) :=
  ((contDiff_weighted T σ n).continuous_iteratedDeriv n le_rfl).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv (hasCompactSupport_weighted T σ) n)

/-- On the line `Re s = σ`, the spectral kernel is the Fourier transform of the weighted
kernel. -/
theorem spectralKernel_eq_fourier (σ t : ℝ) :
    T.spectralKernel (σ + t * I) = 𝓕 (weighted T σ) (-t / (2 * Real.pi)) := by
  rw [T.spectral_eq_bilateralLaplace, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext x
  rw [weighted_apply, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **The `k`-fold decay on a line.** -/
theorem norm_spectralKernel_le_of_ne (σ t : ℝ) (k : ℕ) (ht : t ≠ 0) :
    ‖T.spectralKernel (σ + t * I)‖ ≤
      (∫ x, ‖iteratedDeriv k (weighted T σ) x‖) / |t| ^ k := by
  rw [spectralKernel_eq_fourier]
  have hcd : ContDiff ℝ k (weighted T σ) := contDiff_weighted T σ k
  have hF := Real.fourier_iteratedDeriv (N := k) (n := k) (by exact_mod_cast hcd)
    (fun n _ => integrable_iteratedDeriv_weighted T σ n) le_rfl
  have hw := congrFun hF (-t / (2 * Real.pi))
  have hc : (2 * Real.pi * I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) = -(t : ℂ) * I := by
    push_cast
    field_simp
  have hne : ((2 * Real.pi * I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ k) ≠ 0 := by
    rw [hc]
    exact pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast ht)) I_ne_zero)
  have heq : 𝓕 (weighted T σ) (-t / (2 * Real.pi)) =
      𝓕 (iteratedDeriv k (weighted T σ)) (-t / (2 * Real.pi)) /
        (2 * Real.pi * I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ k := by
    rw [hw, smul_eq_mul, mul_div_cancel_left₀ _ hne]
  rw [heq, norm_div, norm_pow, hc]
  have hn : ‖-(t : ℂ) * I‖ = |t| := by simp
  rw [hn]
  gcongr
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The plain bound, valid on the whole line. -/
theorem norm_spectralKernel_le (σ t : ℝ) :
    ‖T.spectralKernel (σ + t * I)‖ ≤ ∫ x, ‖weighted T σ x‖ := by
  rw [spectralKernel_eq_fourier]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-! ## The uniform constant on a strip -/

/-- The uniform constant: `e^{A R} Σ_i C(k, i) A^i ‖g^{(k−i)}‖_{L¹}`. -/
noncomputable def stripConst (A R : ℝ) (k : ℕ) : ℝ :=
  Real.exp (A * R) * ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * A ^ i * ∫ x, ‖iteratedDeriv (k - i) T.arithmeticKernel x‖

theorem integrable_iteratedDeriv_kernel (n : ℕ) : Integrable (iteratedDeriv n T.arithmeticKernel) :=
  ((T.smooth.of_le le_top : ContDiff ℝ n T.arithmeticKernel).continuous_iteratedDeriv n
    le_rfl).integrable_of_hasCompactSupport (hasCompactSupport_iteratedDeriv T.compactSupport n)

theorem iteratedDeriv_kernel_eq_zero {n : ℕ} {x : ℝ} (hx : x ∉ tsupport T.arithmeticKernel) :
    iteratedDeriv n T.arithmeticKernel x = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have : iteratedFDeriv ℝ n T.arithmeticKernel x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset n h)
  rw [this]
  rfl

/-- The pointwise Leibniz bound with the exponential absorbed into `e^{A R}`. -/
theorem norm_iteratedDeriv_weighted_le {A R σ : ℝ} (hA : 0 ≤ A) (hσ : |σ - 1 / 2| ≤ A)
    (hR : ∀ x ∈ tsupport T.arithmeticKernel, |x| ≤ R) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (weighted T σ) x‖ ≤ ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * A ^ i * (Real.exp (A * R) * ‖iteratedDeriv (k - i) T.arithmeticKernel x‖) := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hL := norm_iteratedFDeriv_mul_le (N := k) (contDiff_expWeight (σ - 1 / 2) k)
    (T.smooth.of_le le_top) x (le_refl (k : ℕ∞ω))
  refine (hL.trans ?_)
  apply Finset.sum_le_sum
  intro i _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    norm_iteratedDeriv_expWeight]
  have hg := norm_nonneg (iteratedDeriv (k - i) T.arithmeticKernel x)
  have hai : |σ - 1 / 2| ^ i ≤ A ^ i := pow_le_pow_left₀ (abs_nonneg _) hσ i
  by_cases hx : x ∈ tsupport T.arithmeticKernel
  · have hexp : Real.exp ((σ - 1 / 2) * x) ≤ Real.exp (A * R) := by
      apply Real.exp_le_exp.mpr
      calc (σ - 1 / 2) * x ≤ |(σ - 1 / 2) * x| := le_abs_self _
        _ = |σ - 1 / 2| * |x| := abs_mul _ _
        _ ≤ A * R := mul_le_mul hσ (hR x hx) (abs_nonneg _) hA
    calc (k.choose i : ℝ) * (|σ - 1 / 2| ^ i * Real.exp ((σ - 1 / 2) * x)) *
          ‖iteratedDeriv (k - i) T.arithmeticKernel x‖
        ≤ (k.choose i : ℝ) * (A ^ i * Real.exp (A * R)) *
          ‖iteratedDeriv (k - i) T.arithmeticKernel x‖ := by gcongr
      _ = (k.choose i : ℝ) * A ^ i * (Real.exp (A * R) * ‖iteratedDeriv (k - i) T.arithmeticKernel x‖) := by
          ring
  · rw [iteratedDeriv_kernel_eq_zero T hx, norm_zero]
    simp

theorem integral_norm_iteratedDeriv_weighted_le {A R σ : ℝ} (hA : 0 ≤ A) (hσ : |σ - 1 / 2| ≤ A)
    (hR : ∀ x ∈ tsupport T.arithmeticKernel, |x| ≤ R) (k : ℕ) :
    ∫ x, ‖iteratedDeriv k (weighted T σ) x‖ ≤ stripConst T A R k := by
  have hint : Integrable fun x => ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * A ^ i * (Real.exp (A * R) * ‖iteratedDeriv (k - i) T.arithmeticKernel x‖) := by
    apply integrable_finsetSum
    intro i _
    exact ((integrable_iteratedDeriv_kernel T (k - i)).norm.const_mul _).const_mul _
  calc ∫ x, ‖iteratedDeriv k (weighted T σ) x‖
      ≤ ∫ x, ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * A ^ i * (Real.exp (A * R) * ‖iteratedDeriv (k - i) T.arithmeticKernel x‖) :=
        integral_mono (integrable_iteratedDeriv_weighted T σ k).norm hint
          (fun x => norm_iteratedDeriv_weighted_le T hA hσ hR k x)
    _ = stripConst T A R k := by
        rw [integral_finsetSum _ (fun i _ => ((integrable_iteratedDeriv_kernel T (k - i)).norm.const_mul _).const_mul _)]
        unfold stripConst
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul, integral_const_mul]
        ring

/-- **The spectral kernel decays on every strip.**  For every `k` and `δ > 0` there is `K` with
`‖ĥ(x + it)‖ ≤ K / (1 + |t|)^k` for `−δ ≤ x ≤ 1 + δ` and all `t`. -/
theorem exists_strip_decay (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ,
      ‖T.spectralKernel (x + t * I)‖ ≤ K / (1 + |t|) ^ k := by
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ tsupport T.arithmeticKernel, |x| ≤ R := by
    obtain ⟨R, hR⟩ := T.compactSupport.isBounded.subset_closedBall 0
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    have := hR hx
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set A : ℝ := 1 / 2 + δ with hA_def
  have hA : 0 ≤ A := by rw [hA_def]; linarith
  set K : ℝ := 2 ^ k * (stripConst T A R 0 + stripConst T A R k) with hK_def
  have hS0 : 0 ≤ stripConst T A R 0 := by
    have := (integral_nonneg fun x => norm_nonneg (weighted T (1 / 2) x)).trans
      (integral_norm_iteratedDeriv_weighted_le T hA (by simp; linarith) hR 0)
    simpa using this
  have hSk : 0 ≤ stripConst T A R k := by
    exact (integral_nonneg fun x => norm_nonneg _).trans
      (integral_norm_iteratedDeriv_weighted_le T hA (σ := 1 / 2) (by simp; linarith) hR k)
  refine ⟨K, by positivity, fun x hx t => ?_⟩
  have hσ : |x - 1 / 2| ≤ A := by
    rw [abs_le, hA_def]
    constructor <;> linarith [hx.1, hx.2]
  have hpos : 0 < (1 + |t|) ^ k := by positivity
  rcases le_or_gt |t| 1 with ht | ht
  · -- the plain bound
    have h0 := (norm_spectralKernel_le T x t).trans
      (by simpa using integral_norm_iteratedDeriv_weighted_le T hA hσ hR 0)
    rw [le_div_iff₀ hpos]
    have h2 : (1 + |t|) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    calc ‖T.spectralKernel (x + t * I)‖ * (1 + |t|) ^ k ≤ stripConst T A R 0 * 2 ^ k := by gcongr
      _ ≤ K := by rw [hK_def]; nlinarith
  · have htne : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at ht
      linarith
    have hk := (norm_spectralKernel_le_of_ne T x t k htne).trans
      (div_le_div_of_nonneg_right (integral_norm_iteratedDeriv_weighted_le T hA hσ hR k)
        (by positivity))
    rw [le_div_iff₀ hpos]
    have h2 : (1 + |t|) ^ k ≤ 2 ^ k * |t| ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have htk : 0 < |t| ^ k := by positivity
    calc ‖T.spectralKernel (x + t * I)‖ * (1 + |t|) ^ k
        ≤ stripConst T A R k / |t| ^ k * (2 ^ k * |t| ^ k) := by gcongr
      _ = stripConst T A R k * 2 ^ k := by field_simp
      _ ≤ K := by rw [hK_def]; nlinarith

/-- **The explicit formula in the limit holds for every Weil test function.** -/
theorem explicit_formula_limit_weil {δ : ℝ} (hδ : 0 < δ) :
    ∃ T' : ℕ → ℝ, (∀ n : ℕ, T' n ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) ∧
      Tendsto (fun n => 2 * Real.pi * I * zeroSide δ T.spectralKernel (T' n) -
        primeSide δ T.spectralKernel (T' n)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hdecay⟩ := exists_strip_decay T 5 hδ
  exact explicit_formula_limit hδ T.spectralAnalytic hK hdecay

end Soma.Holonics.RH.SpectralKernelDecay
