import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import HolonicsResearch.Zeta.Hearing

/-!
# The operator-level ear: `∂_c` on `L²(e^{−2cx}dx)` and the Mellin–Plancherel unitary

[proved-standard; formal-checked] for the weight, the unitary, Plancherel on the line, the
intertwining, the formal adjoint and the averaged shift; [proved-derived; formal-checked] for
Hearing's instance and its join to `Hearing.VerticalZeroFree`.

Sources. Issue #410, the box "the operator-level ear: `∂_c` on `L²(ℝ, e^(−2cx)dx)`, its
normality, and Mellin–Plancherel (`Zeta/Hearing`)". `Zeta/Hearing` proves the ear at the symbol
and truncation levels and leaves open, as its `[open; #62]` item, the unbounded operator `∂_c`,
its normality, the Mellin–Plancherel unitary carrying it to multiplication by `c + iy`, the
identification of its truncations with the coordinate model `truncatedScaleDerivative c T`, and
the Bochner identity `F(∂_c) = ∫ e^{τu²}Φ(u) e^{(∂_c−½)u} du`; `Zeta/HeatKernelPhi` owns that
symbol (`heatE_riemannXi`, `flowLap`) and its decay (`flow_dominant`). Atlas rows (in
`docs/atlas/targets.tsv`): `rh.spectral-operator` (`𝔞_c = ζ(∂_c)` on `L²(ℝ, e^(−2ct)dt)`,
`σ(∂_c) = c + iℝ`, Herichi–Lapidus 2012/2017), `rh.sharpened-hearing-threshold` (whose limits
column holds "the operator ∂_c on L² is owed"), `rh.mellin-half-density` (the half-density chart,
here at the weight `e^{−cx}`); `wave.cone-bank-of-tubes` (`docs/atlas/physics.tsv`: "a stretch of
`x` is a step of `u`, the Mellin transform the Fourier transform on `u`"). Mathlib:
`Lp.fourierTransformₗᵢ` (the `L²` Fourier transform), `Lp.fourier_toTemperedDistribution_eq`,
`ae_eq_of_integral_contDiff_smul_eq`, `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
`mellin_eq_fourier`, `Real.fourier_deriv`, `integral_add_right_eq_self`,
`measurePreserving_add_prod`, `LinearPMap.IsFormalAdjoint.le_adjoint`.

Conventions. `x` is the log-scale coordinate and the scale is `t = e^{−x}`, so a scale shift
`t ↦ e^{−u}t`, a ratio, is the step `x ↦ x + u`. The receiver at abscissa `c` reads with
`μ_c = e^{−2cx} dx` (`lineMeasure c`), and `W_c f = e^{−cx} f` (`weight c x`) carries its frame
to the flat one. Mathlib's transform is `𝓕 g(ξ) = ∫ e^{−2πixξ} g(x) dx`, so
`U_c f(ξ) = ∫ f(x) e^{−(c + 2πiξ)x} dx`: the line transform `∫ f(x) e^{−sx} dx` at
`s = c + iy`, `y = 2πξ` (`scaleSymbol c ξ = c + 2πiξ`), which is Mathlib's `mellin` of
`t ↦ f(−log t)` at `s`. The core is `{e^{cx} g : g ∈ 𝓢(ℝ, ℂ)}` (`core c g`).

What is proved.

1. **The weight is a unitary.** `eLpNorm (W_c f) 2 dx = eLpNorm f 2 μ_c` for every `f`
   (`eLpNorm_weight_mul`), `W_c f ∈ L²(dx) ↔ f ∈ L²(μ_c)` (`memLp_weight_mul_iff`), and
   `W_c : L²(μ_c) ≃ₗᵢ L²(dx)` (`weightEquiv`) with inverse `g ↦ e^{cx} g`
   (`coeFn_weightEquiv`, `coeFn_weightEquiv_symm`).
2. **Mellin–Plancherel.** `U_c = 𝓕 ∘ W_c : L²(μ_c) ≃ₗᵢ L²(dξ)` (`mellinPlancherel`). The Fourier
   integral of `W_{Re s} f` at `Im s/(2π)` is the line transform (`fourier_weight_mul`), which is
   `mellin (t ↦ f(−log t)) s` (`lineTransform_eq_mellin`). On `L¹ ∩ L²` Mathlib's `L²` transform
   is the Fourier integral (`coeFn_fourier_toLp`), so for `f ∈ L²(μ_c)` with `W_c f ∈ L¹`,
   `U_c f(ξ)` is the line transform at `c + 2πiξ` for almost every `ξ`
   (`mellinPlancherel_ae_eq_lineTransform`, `lineTransform_ae_eq_mellinPlancherel`), and
   Plancherel on the line holds in both normalisations: `‖ξ ↦ ∫ f e^{−(c+2πiξ)x}‖₂ = ‖f‖_{μ_c}`
   (`eLpNorm_lineTransform`) and `∫ |∫ f(x) e^{−(c+iy)x} dx|² dy = 2π ∫ |f|² dμ_c`
   (`plancherel_line`). On the core, `U_c(e^{cx}g) = 𝓕 g` (`mellinPlancherel_core`), and its line
   transform at `c + iy` is `𝓕 g (y/2π)` (`lineTransform_core`).
3. **`∂_c` is carried to multiplication by `c + iy`.** `W_c ∘ ∂ = (c + ∂) ∘ W_c` at every point
   of differentiability (`weight_mul_deriv`); on the core `∂(e^{cx}g) = e^{cx}(cg + g′)`
   (`hasDerivAt_core`, `coeFn_scaleDeriv`, `weightEquiv_scaleDeriv`), and
   `U_c(∂f)(ξ) = (c + 2πiξ) U_c f(ξ)` a.e. (`coeFn_mellinPlancherel_scaleDeriv`, from
   `fourier_weightedDeriv`).
4. **Normality on the core.** `U_c((2c − ∂)f) = (c − 2πiξ) U_c f`
   (`coeFn_mellinPlancherel_scaleDerivAdj`), and on the Mellin side a multiplier `m` has adjoint
   `conj m` with `‖m h‖ = ‖(conj m) h‖` (`inner_multiplier`, `norm_multiplier`). Hence
   `⟪∂f, g⟫_{μ_c} = ⟪f, 2cg − ∂g⟫_{μ_c}` (`inner_scaleDeriv`), so `∂ − c` is skew on the core
   (`inner_scaleDeriv_sub`),
   `‖∂f‖ = ‖2cf − ∂f‖` (`norm_scaleDeriv_eq`), and `∂` commutes with `2c − ∂`
   (`scaleDeriv_comm`). As densely defined operators on the dense core (`dense_coreDomain`),
   `2c − ∂` is a formal adjoint of `∂` (`isFormalAdjoint_scaleDerivOp`), so `2c − ∂ ≤ ∂†`
   (`scaleDerivAdjOp_le_adjoint`), and `‖∂x‖ = ‖(2c − ∂)x‖` on the core
   (`norm_scaleDerivOp_eq`).
5. **The shift group and the Bochner identity.** `(T_u f)(x) = f(x + u)` is `e^{u∂}`:
   `𝓕(W_c T_u f) = e^{(c+2πiξ)u} 𝓕(W_c f)` (`fourier_weight_shift`), and on the core in `L²`
   (`coeFn_mellinPlancherel_shiftCore`). For `w` with `w(u)e^{cu} ∈ L¹` and `W_c f ∈ L¹`, the
   averaged shift `∫ w(u) T_u f du` is carried to multiplication by `F(c + 2πiξ)`,
   `F(s) = ∫ w(u) e^{su} du` (`fourier_weight_average`, with `integrable_weight_average`; in `L²`
   for `f ∈ L²(μ_c)` when the average lies in `L²(μ_c)`, `coeFn_mellinPlancherel_average`).
   Hearing's weight `w_τ(u) = e^{τu²}e^{−u/2}Φ(u)` meets the hypothesis at every `c`
   (`integrable_hearingWeight`, through `integrable_flowLap` from `flow_dominant`), its `F` is
   `heatE (−τ) ξ` (`integral_hearingWeight`), so
   `F(∂_c) = ∫ e^{τu²}Φ(u) e^{(∂_c−½)u} du` is multiplication by `heatE (−τ) ξ (c + 2πiξ)`
   (`fourier_weight_hearingAverage`). That multiplier vanishes nowhere exactly when the ear hears
   no zero on `Re s = c` (`verticalZeroFree_iff_multiplier_ne_zero`), and Hearing's coordinate
   `c + iy` is `scaleSymbol c (y/2π)` (`truncatedScaleDerivative_apply`).

What is not claimed. The closure of `∂` on the core, its domain, and the normality of the closed
operator: the statements are the core's, with `2c − ∂ ≤ ∂†`, not that `∂†` is the closure of
`2c − ∂`. Essential self-adjointness on the core of the symmetric operator `i(∂ − c)` (`i∂` itself
is not symmetric in `L²(μ_c)` when `c ≠ 0`), the spectrum `c + iℝ` of the multiplication operator,
and the functional calculus of an unbounded normal operator (Mathlib's `cfc` is for bounded normal
elements). The identification of the spectral truncations, multiplication by `c + iy` on
`|y| ≤ T`, with `truncatedScaleDerivative c T` as a `⋆`-algebra map: only the coordinate is
matched. The `L²` membership of an averaged shift (Young's inequality) is a hypothesis of
`coeFn_mellinPlancherel_average`, not proved. The unitary lands on `L²(dξ)`; read on `L²(dy)`
the line transform multiplies norms by `√(2π)` (`plancherel_line`), and is unitary onto
`L²(dy/2π)`. The zeta side (zero-freeness, the threshold) is `Hearing`'s.

Computational object: the helical pair interaction read on the scale line. The symbol `c + iy`
is the logarithmic rate of a swing, a boost `c` (the weight `e^{−cx}`, the receiver's frame) plus
`i` times a turn `y` (the character `e^{−iyx}`), and `U_c` reads each scale mode at its rate. The
adjoint `2c − ∂ ↔ c − iy` is again an operator of the core because the symbol lies on the fixed
line `Re s = c` of `s ↦ 2c − s̄`, the half-turn about `c` composed with conjugation:
`conj m = 2c − m` (`conj_scaleSymbol`). Of the winding guide's six general objects it touches the
helix (the turn `e^{−2πixξ}`, `ξ` windings per unit of `x`), the tube (the shift group
`T_u = e^{u∂}`, transfer between the sections `x` and `x + u`, read both as a map and as the
pairing `U_c` preserves), and faces and placement (the multiplier `m(ξ)` is the face each mode
reads, and `|m| = |conj m|` is kept by the reflection). The pair, cell holonomy and the tower
thread stay attached and are not used here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Zeta.MellinPlancherel

open MeasureTheory Complex Set Filter
open scoped ENNReal FourierTransform ComplexConjugate SchwartzMap

/-! ## The scale measure and the weight -/

/-- [definition] The density `e^{−2cx}` of the receiver's measure at abscissa `c`. -/
def lineDensity (c x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2 * c * x))

/-- [definition] **The scale measure** `μ_c = e^{−2cx} dx` on the log-scale line. -/
def lineMeasure (c : ℝ) : Measure ℝ := volume.withDensity (lineDensity c)

/-- [proved-standard; formal-checked] The density is measurable. -/
theorem measurable_lineDensity (c : ℝ) : Measurable (lineDensity c) := by
  unfold lineDensity
  fun_prop

/-- [proved-standard; formal-checked] The density vanishes nowhere. -/
theorem lineDensity_ne_zero (c x : ℝ) : lineDensity c x ≠ 0 := by
  unfold lineDensity
  simpa using Real.exp_pos _

/-- [proved-standard; formal-checked] `μ_c ≪ dx`. -/
theorem lineMeasure_ac (c : ℝ) : lineMeasure c ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- [proved-standard; formal-checked] `dx ≪ μ_c`: the two measures have the same null sets. -/
theorem volume_ac (c : ℝ) : (volume : Measure ℝ) ≪ lineMeasure c :=
  withDensity_absolutelyContinuous' (measurable_lineDensity c).aemeasurable
    (ae_of_all _ fun x => lineDensity_ne_zero c x)

/-- [definition] The weight `e^{−cx}`, `W_c f = e^{−cx} f`. -/
def weight (c x : ℝ) : ℂ := (Real.exp (-c * x) : ℂ)

/-- [proved-standard; formal-checked] The weight is continuous. -/
theorem continuous_weight (c : ℝ) : Continuous (weight c) := by
  unfold weight
  fun_prop

/-- [proved-standard; formal-checked] `|e^{−cx}|² = e^{−2cx}`. -/
theorem enorm_weight_rpow (c x : ℝ) : ‖weight c x‖ₑ ^ (2 : ℝ) = lineDensity c x := by
  unfold weight lineDensity
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring

/-- [proved-standard; formal-checked] `e^{−cx} e^{cx} = 1`. -/
theorem weight_mul_weight_neg (c x : ℝ) : weight c x * weight (-c) x = 1 := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

/-- [proved-standard; formal-checked] **The weight is an isometry**: `‖W_c f‖_{L²(dx)} = ‖f‖_{L²(μ_c)}`. -/
theorem eLpNorm_weight_mul (c : ℝ) (f : ℝ → ℂ) :
    eLpNorm (fun x => weight c x * f x) 2 volume = eLpNorm f 2 (lineMeasure c) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, lineMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_lineDensity c)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [enorm_mul, Pi.mul_apply, ENNReal.toReal_ofNat]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_weight_rpow]

/-- [proved-standard; formal-checked] `μ_c` and `dx` have the same a.e.-strongly measurable functions. -/
theorem aestronglyMeasurable_iff (c : ℝ) {f : ℝ → ℂ} :
    AEStronglyMeasurable f (lineMeasure c) ↔ AEStronglyMeasurable f volume :=
  ⟨fun h => h.mono_ac (volume_ac c), fun h => h.mono_ac (lineMeasure_ac c)⟩

/-- [proved-standard; formal-checked] `W_c f ∈ L²(dx) ↔ f ∈ L²(μ_c)`. -/
theorem memLp_weight_mul_iff (c : ℝ) {f : ℝ → ℂ} :
    MemLp (fun x => weight c x * f x) 2 volume ↔ MemLp f 2 (lineMeasure c) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [aestronglyMeasurable_iff]
      have : AEStronglyMeasurable (fun x => weight (-c) x * (weight c x * f x)) volume :=
        (continuous_weight (-c)).aestronglyMeasurable.mul h1
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only
      rw [← mul_assoc, mul_comm (weight (-c) x), weight_mul_weight_neg, one_mul]
    · rwa [← eLpNorm_weight_mul]
  · rintro ⟨h1, h2⟩
    refine ⟨(continuous_weight c).aestronglyMeasurable.mul ((aestronglyMeasurable_iff c).1 h1), ?_⟩
    rwa [eLpNorm_weight_mul]

/-! ## The weight is a unitary -/

/-- [proved-standard; formal-checked] The weighted representative of an `L²(μ_c)` class lies in `L²(dx)`. -/
theorem memLp_weight (c : ℝ) (u : Lp ℂ 2 (lineMeasure c)) :
    MemLp (fun x => weight c x * u x) 2 volume :=
  (memLp_weight_mul_iff c).2 (Lp.memLp u)

/-- [proved-standard; formal-checked] `e^{cx} g ∈ L²(μ_c)` for `g ∈ L²(dx)`. -/
theorem memLp_weight_neg (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun x => weight (-c) x * g x) 2 (lineMeasure c) := by
  rw [← memLp_weight_mul_iff]
  refine (Lp.memLp g).congr_norm ?_ ?_
  · exact (continuous_weight c).aestronglyMeasurable.mul
      ((continuous_weight (-c)).aestronglyMeasurable.mul (Lp.memLp g).1)
  · refine ae_of_all _ fun x => ?_
    rw [← mul_assoc, weight_mul_weight_neg, one_mul]

/-- [definition] The weight as a linear isometry `L²(μ_c) → L²(dx)`. -/
def weightLI (c : ℝ) : Lp ℂ 2 (lineMeasure c) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun u := (memLp_weight c u).toLp _
  map_add' u v := by
    ext1
    filter_upwards [(memLp_weight c u).coeFn_toLp, (memLp_weight c v).coeFn_toLp,
      (memLp_weight c (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memLp_weight c u).toLp _) ((memLp_weight c v).toLp _),
      (volume_ac c).ae_le (Lp.coeFn_add u v)] with x hu hv huv h1 h2
    rw [huv, h1, Pi.add_apply, hu, hv, h2, Pi.add_apply, mul_add]
  map_smul' r u := by
    ext1
    filter_upwards [(memLp_weight c u).coeFn_toLp, (memLp_weight c (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memLp_weight c u).toLp _),
      (volume_ac c).ae_le (Lp.coeFn_smul r u)] with x hu hru h1 h2
    rw [hru, RingHom.id_apply, h1, Pi.smul_apply, hu, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  norm_map' u := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, eLpNorm_weight_mul, Lp.norm_def]

/-- [proved-standard; formal-checked] `W_c u = e^{−cx} u` almost everywhere. -/
theorem coeFn_weightLI (c : ℝ) (u : Lp ℂ 2 (lineMeasure c)) :
    (weightLI c u : ℝ → ℂ) =ᵐ[volume] fun x => weight c x * u x :=
  (memLp_weight c u).coeFn_toLp

/-- [proved-standard; formal-checked] The weight is onto, with preimage `e^{cx} g`. -/
theorem weightLI_surjective (c : ℝ) : Function.Surjective (weightLI c) := by
  intro g
  refine ⟨(memLp_weight_neg c g).toLp _, ?_⟩
  ext1
  filter_upwards [coeFn_weightLI c ((memLp_weight_neg c g).toLp _),
    (volume_ac c).ae_le (memLp_weight_neg c g).coeFn_toLp] with x h1 h2
  rw [h1, h2, ← mul_assoc, weight_mul_weight_neg, one_mul]

/-- [definition] **The weight unitary** `W_c : L²(μ_c) ≃ₗᵢ L²(dx)`, `W_c f = e^{−cx} f`. -/
def weightEquiv (c : ℝ) : Lp ℂ 2 (lineMeasure c) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (weightLI c) (weightLI_surjective c)

/-- [proved-standard; formal-checked] `W_c u = e^{−cx} u` almost everywhere. -/
theorem coeFn_weightEquiv (c : ℝ) (u : Lp ℂ 2 (lineMeasure c)) :
    (weightEquiv c u : ℝ → ℂ) =ᵐ[volume] fun x => weight c x * u x :=
  coeFn_weightLI c u

/-- [proved-standard; formal-checked] **The inverse weight** `W_c⁻¹ g = e^{cx} g`. -/
theorem coeFn_weightEquiv_symm (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((weightEquiv c).symm g : ℝ → ℂ) =ᵐ[lineMeasure c] fun x => weight (-c) x * g x := by
  have : (weightEquiv c).symm g = (memLp_weight_neg c g).toLp _ := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    ext1
    filter_upwards [coeFn_weightEquiv c ((memLp_weight_neg c g).toLp _),
      (volume_ac c).ae_le (memLp_weight_neg c g).coeFn_toLp] with x h1 h2
    rw [h1, h2, ← mul_assoc, weight_mul_weight_neg, one_mul]
  rw [this]
  exact (memLp_weight_neg c g).coeFn_toLp

/-! ## Mellin–Plancherel -/

/-- [definition] **The Mellin–Plancherel unitary** `U_c = 𝓕 ∘ W_c : L²(μ_c) ≃ₗᵢ L²(dξ)`. -/
def mellinPlancherel (c : ℝ) : Lp ℂ 2 (lineMeasure c) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (weightEquiv c).trans (Lp.fourierTransformₗᵢ ℝ ℂ)

/-- [proved-standard; formal-checked] `U_c u = 𝓕 (W_c u)`. -/
theorem mellinPlancherel_apply (c : ℝ) (u : Lp ℂ 2 (lineMeasure c)) :
    mellinPlancherel c u = 𝓕 (weightEquiv c u) := rfl

/-- [definition] The line transform `∫ e^{−sx} f(x) dx`. -/
def lineTransform (f : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, cexp (-s * x) * f x

/-- [definition] The scale symbol `c + 2πiξ`, which is `c + iy` at `y = 2πξ`. -/
def scaleSymbol (c ξ : ℝ) : ℂ := (c : ℂ) + 2 * Real.pi * I * ξ

/-- [proved-standard; formal-checked] The Fourier integral of `W_{Re s} f` at `Im s/(2π)` is the line transform. -/
theorem fourier_weight_mul (f : ℝ → ℂ) (s : ℂ) :
    𝓕 (fun x => weight s.re x * f x) (s.im / (2 * Real.pi)) = lineTransform f s := by
  rw [Real.fourier_real_eq_integral_exp_smul, lineTransform]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, weight]
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_rhs => rw [← re_add_im s]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- [proved-standard; formal-checked] **The line transform is Mellin's**: `∫ f e^{−sx} dx = mellin (f ∘ (−log)) s`. -/
theorem lineTransform_eq_mellin (f : ℝ → ℂ) (s : ℂ) :
    lineTransform f s = mellin (fun t => f (-Real.log t)) s := by
  rw [mellin_eq_fourier, ← fourier_weight_mul]
  refine congrArg (fun h : ℝ → ℂ => 𝓕 h (s.im / (2 * Real.pi))) (funext fun u => ?_)
  rw [Real.log_exp, neg_neg, Complex.real_smul, weight]

/-- [proved-standard; formal-checked] `Re (c + 2πiξ) = c`. -/
theorem re_scaleSymbol (c ξ : ℝ) : (scaleSymbol c ξ).re = c := by simp [scaleSymbol]

/-- [proved-standard; formal-checked] `Im (c + 2πiξ) = 2πξ`. -/
theorem im_scaleSymbol (c ξ : ℝ) : (scaleSymbol c ξ).im = 2 * Real.pi * ξ := by simp [scaleSymbol]

/-- [proved-standard; formal-checked] `c + 2πiξ = c + (2πξ) i`. -/
theorem scaleSymbol_eq (c ξ : ℝ) : scaleSymbol c ξ = (c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
  unfold scaleSymbol
  push_cast
  ring

/-- [proved-standard; formal-checked] The line transform at `c + 2πiξ` is `𝓕 (W_c f) ξ`. -/
theorem lineTransform_scaleSymbol (c ξ : ℝ) (f : ℝ → ℂ) :
    lineTransform f (scaleSymbol c ξ) = 𝓕 (fun x => weight c x * f x) ξ := by
  rw [← fourier_weight_mul, re_scaleSymbol, im_scaleSymbol]
  field_simp

/-- [proved-standard; formal-checked] On `L¹ ∩ L²`, Mathlib's `L²` Fourier transform is the Fourier integral. -/
theorem coeFn_fourier_toLp {h : ℝ → ℂ} (h2 : MemLp h 2) (h1 : Integrable h) :
    ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 h := by
  have hc : Continuous (𝓕 h) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.2 h1)]
    exact (Real.Lp.fourierTransform _).continuous
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hc.locallyIntegrable ?_
  intro g g_smooth g_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp g_smooth
  set φ := hg₁.toSchwartzMap hg₂ with hφ
  have key := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp h))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at key
  have hsa : ∫ x, 𝓕 (φ : ℝ → ℂ) x • h x = ∫ x, φ x • 𝓕 h x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable h1
  have e1 : ∫ x, 𝓕 φ x • (h2.toLp h) x = ∫ x, 𝓕 (φ : ℝ → ℂ) x • h x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourier_coe]
  have e2 : ∀ F : ℝ → ℂ, ∫ x, g x • F x = ∫ x, φ x • F x := fun F => by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [hφ, Complex.real_smul]
  rw [e2, e2, ← key, e1, hsa]

/-- [proved-standard; formal-checked] **`U_c u` is the line transform** where `W_c u` is integrable. -/
theorem mellinPlancherel_ae_eq_lineTransform (c : ℝ) (u : Lp ℂ 2 (lineMeasure c))
    (hu : Integrable (fun x => weight c x * u x)) :
    ∀ᵐ ξ ∂volume, mellinPlancherel c u ξ = lineTransform u (scaleSymbol c ξ) := by
  have h : weightEquiv c u = (memLp_weight c u).toLp _ := rfl
  filter_upwards [coeFn_fourier_toLp (memLp_weight c u) hu] with ξ hξ
  rw [mellinPlancherel_apply, h, hξ, lineTransform_scaleSymbol]

/-- [proved-standard; formal-checked] The line transform of `f ∈ L²(μ_c)`, `W_c f ∈ L¹`, is `U_c f`. -/
theorem lineTransform_ae_eq_mellinPlancherel (c : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 (lineMeasure c))
    (h1 : Integrable (fun x => weight c x * f x)) :
    (fun ξ => lineTransform f (scaleSymbol c ξ)) =ᵐ[volume] (mellinPlancherel c (hf.toLp f) : ℝ → ℂ) := by
  have hae : (fun x => weight c x * hf.toLp f x) =ᵐ[volume] fun x => weight c x * f x := by
    filter_upwards [(volume_ac c).ae_le hf.coeFn_toLp] with x hx
    rw [hx]
  filter_upwards [mellinPlancherel_ae_eq_lineTransform c (hf.toLp f) (h1.congr hae.symm)] with ξ hξ
  rw [hξ, lineTransform_scaleSymbol, lineTransform_scaleSymbol, Real.fourier_congr_ae hae]

/-- [proved-standard; formal-checked] **Plancherel on the line**, `ξ` normalisation: `‖U_c f‖₂ = ‖f‖_{μ_c}`. -/
theorem eLpNorm_lineTransform (c : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 (lineMeasure c))
    (h1 : Integrable (fun x => weight c x * f x)) :
    eLpNorm (fun ξ => lineTransform f (scaleSymbol c ξ)) 2 volume = eLpNorm f 2 (lineMeasure c) := by
  rw [eLpNorm_congr_ae (lineTransform_ae_eq_mellinPlancherel c hf h1), ← Lp.enorm_def,
    ← eLpNorm_congr_ae hf.coeFn_toLp, ← Lp.enorm_def]
  simp only [enorm, LinearIsometryEquiv.nnnorm_map]

/-- [proved-standard; formal-checked] `‖u‖² = ∫ |u|²` in `L²`. -/
theorem norm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have H := congr_arg (RCLike.re (K := ℂ)) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at H
  simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)] at H
  exact H

/-- [proved-standard; formal-checked] **Plancherel on the line**: `∫ |∫ f e^{−(c+iy)x} dx|² dy = 2π ∫ |f|² dμ_c`. -/
theorem plancherel_line (c : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 (lineMeasure c))
    (h1 : Integrable (fun x => weight c x * f x)) :
    ∫ y : ℝ, ‖lineTransform f (c + y * I)‖ ^ 2 = 2 * Real.pi * ∫ x, ‖f x‖ ^ 2 ∂lineMeasure c := by
  have hy : ∀ y : ℝ, (c : ℂ) + y * I = scaleSymbol c (y / (2 * Real.pi)) := fun y => by
    rw [scaleSymbol_eq]
    congr 3
    field_simp
  simp_rw [hy]
  rw [Measure.integral_comp_div (fun ξ => ‖lineTransform f (scaleSymbol c ξ)‖ ^ 2) (2 * Real.pi),
    abs_of_pos Real.two_pi_pos, smul_eq_mul]
  congr 1
  have e1 : ∫ ξ, ‖lineTransform f (scaleSymbol c ξ)‖ ^ 2 = ∫ ξ, ‖mellinPlancherel c (hf.toLp f) ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [lineTransform_ae_eq_mellinPlancherel c hf h1] with ξ hξ
    rw [hξ]
  have e2 : ∫ x, ‖f x‖ ^ 2 ∂lineMeasure c = ∫ x, ‖hf.toLp f x‖ ^ 2 ∂lineMeasure c := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [e1, e2, ← norm_sq_eq_integral, ← norm_sq_eq_integral, LinearIsometryEquiv.norm_map]

/-! ## The core -/

/-- [definition] The core element `e^{cx} g` of `L²(μ_c)`, for a Schwartz function `g`. -/
def core (c : ℝ) (g : 𝓢(ℝ, ℂ)) : Lp ℂ 2 (lineMeasure c) := (weightEquiv c).symm (g.toLp 2)

/-- [proved-standard; formal-checked] `core c g = e^{cx} g` almost everywhere. -/
theorem coeFn_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (core c g : ℝ → ℂ) =ᵐ[lineMeasure c] fun x => weight (-c) x * g x := by
  unfold core
  filter_upwards [coeFn_weightEquiv_symm c (g.toLp 2),
    (lineMeasure_ac c).ae_le (g.coeFn_toLp 2)] with x h1 h2
  rw [h1, h2]

/-- [proved-standard; formal-checked] `W_c (e^{cx} g) = g`. -/
theorem weightEquiv_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) : weightEquiv c (core c g) = g.toLp 2 := by
  simp [core]

/-- [proved-standard; formal-checked] `U_c (e^{cx} g) = 𝓕 g`. -/
theorem mellinPlancherel_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    mellinPlancherel c (core c g) = (𝓕 g).toLp 2 := by
  rw [mellinPlancherel_apply, weightEquiv_core, SchwartzMap.toLp_fourier_eq]

/-- [proved-standard; formal-checked] `U_c (e^{cx} g) = 𝓕 g` almost everywhere. -/
theorem coeFn_mellinPlancherel_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (mellinPlancherel c (core c g) : ℝ → ℂ) =ᵐ[volume] 𝓕 (g : ℝ → ℂ) := by
  rw [mellinPlancherel_core]
  exact (𝓕 g).coeFn_toLp 2

/-- [proved-standard; formal-checked] The core's line transform at `c + iy` is `𝓕 g (y/(2π))`. -/
theorem lineTransform_core (c y : ℝ) (g : 𝓢(ℝ, ℂ)) :
    lineTransform (fun x => weight (-c) x * g x) (c + y * I) = 𝓕 (g : ℝ → ℂ) (y / (2 * Real.pi)) := by
  rw [← fourier_weight_mul]
  have h1 : ((c : ℂ) + y * I).re = c := by simp
  have h2 : ((c : ℂ) + y * I).im = y := by simp
  rw [h1, h2]
  refine congrArg (fun h : ℝ → ℂ => 𝓕 h (y / (2 * Real.pi))) (funext fun x => ?_)
  rw [← mul_assoc, weight_mul_weight_neg, one_mul]

/-- [proved-standard; formal-checked] The core through the linear map `toLpCLM`. -/
theorem core_eq (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    core c g = (weightEquiv c).symm (SchwartzMap.toLpCLM ℂ ℂ 2 volume g) := by
  rw [core, SchwartzMap.toLpCLM_apply]

/-- [proved-standard; formal-checked] The core is additive. -/
theorem core_add (c : ℝ) (g h : 𝓢(ℝ, ℂ)) : core c (g + h) = core c g + core c h := by
  simp only [core_eq, map_add]

/-- [proved-standard; formal-checked] The core respects differences. -/
theorem core_sub (c : ℝ) (g h : 𝓢(ℝ, ℂ)) : core c (g - h) = core c g - core c h := by
  simp only [core_eq, map_sub]

/-- [proved-standard; formal-checked] The core is `ℂ`-homogeneous. -/
theorem core_smul (c : ℝ) (a : ℂ) (g : 𝓢(ℝ, ℂ)) : core c (a • g) = a • core c g := by
  simp only [core_eq, map_smul]

/-! ## The scale derivative on the core -/

/-- [definition] The weighted derivative `c + ∂` on Schwartz space, the conjugate `W_c ∂ W_c⁻¹`. -/
def weightedDeriv (c : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (c : ℂ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) + SchwartzMap.derivCLM ℂ ℂ

/-- [definition] `c − ∂` on Schwartz space, the conjugate `W_c (2c − ∂) W_c⁻¹`. -/
def weightedDerivAdj (c : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (c : ℂ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) - SchwartzMap.derivCLM ℂ ℂ

/-- [proved-standard; formal-checked] `(c + ∂) g = c g + g′`. -/
theorem weightedDeriv_apply (c : ℝ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weightedDeriv c g x = c * g x + deriv g x := by
  simp [weightedDeriv]

/-- [proved-standard; formal-checked] `(c − ∂) g = c g − g′`. -/
theorem weightedDerivAdj_apply (c : ℝ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weightedDerivAdj c g x = c * g x - deriv g x := by
  simp [weightedDerivAdj]

/-- [proved-standard; formal-checked] `c − ∂ = 2c − (c + ∂)`. -/
theorem weightedDerivAdj_eq (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    weightedDerivAdj c g = (2 * c : ℂ) • g - weightedDeriv c g := by
  ext x
  simp [weightedDerivAdj_apply, weightedDeriv_apply]
  ring

/-- [proved-standard; formal-checked] `(e^{−cx})′ = −c e^{−cx}`. -/
theorem hasDerivAt_weight (c x : ℝ) : HasDerivAt (weight c) (-c * weight c x) x := by
  have h := ((Real.hasDerivAt_exp (-c * x)).comp x ((hasDerivAt_id x).const_mul (-c))).ofReal_comp
  refine h.congr_deriv ?_
  simp [weight]
  ring

/-- [proved-standard; formal-checked] **`W_c ∘ ∂ = (c + ∂) ∘ W_c`** at a point of differentiability. -/
theorem weight_mul_deriv (c : ℝ) {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    weight c x * deriv f x = c * (weight c x * f x) + deriv (fun x => weight c x * f x) x := by
  rw [((hasDerivAt_weight c x).fun_mul hf.hasDerivAt).deriv]
  ring

/-- [proved-standard; formal-checked] `∂(e^{cx} g) = e^{cx} (c g + g′)`. -/
theorem hasDerivAt_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun x => weight (-c) x * g x) (weight (-c) x * weightedDeriv c g x) x := by
  refine ((hasDerivAt_weight (-c) x).fun_mul (g.hasDerivAt x)).congr_deriv ?_
  rw [weightedDeriv_apply]
  push_cast
  ring

/-- [definition] The scale derivative on the core, `∂(e^{cx} g) = e^{cx} (c g + g′)`. -/
def scaleDeriv (c : ℝ) (g : 𝓢(ℝ, ℂ)) : Lp ℂ 2 (lineMeasure c) := core c (weightedDeriv c g)

/-- [definition] Its formal adjoint on the core, `(2c − ∂)(e^{cx} g) = e^{cx} (c g − g′)`. -/
def scaleDerivAdj (c : ℝ) (g : 𝓢(ℝ, ℂ)) : Lp ℂ 2 (lineMeasure c) := core c (weightedDerivAdj c g)

/-- [proved-standard; formal-checked] `scaleDeriv c g` is the derivative of the core representative. -/
theorem coeFn_scaleDeriv (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (scaleDeriv c g : ℝ → ℂ) =ᵐ[lineMeasure c] deriv (fun x => weight (-c) x * g x) := by
  filter_upwards [coeFn_core c (weightedDeriv c g)] with x h
  rw [scaleDeriv, h, (hasDerivAt_core c g x).deriv]

/-- [proved-standard; formal-checked] `W_c (∂ f) = (c + ∂) (W_c f)` on the core, in `L²`. -/
theorem weightEquiv_scaleDeriv (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    weightEquiv c (scaleDeriv c g) = (weightedDeriv c g).toLp 2 :=
  weightEquiv_core c _

/-- [proved-standard; formal-checked] `(2c − ∂) f = 2c f − ∂ f` on the core. -/
theorem scaleDerivAdj_eq (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    scaleDerivAdj c g = (2 * c : ℂ) • core c g - scaleDeriv c g := by
  rw [scaleDerivAdj, weightedDerivAdj_eq, core_sub, core_smul, scaleDeriv]

/-- [proved-standard; formal-checked] `conj (c + 2πiξ) = 2c − (c + 2πiξ)`. -/
theorem conj_scaleSymbol (c ξ : ℝ) : conj (scaleSymbol c ξ) = (2 * c : ℂ) - scaleSymbol c ξ := by
  simp only [scaleSymbol, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- [proved-standard; formal-checked] `𝓕 ((c + ∂) g) = (c + 2πiξ) 𝓕 g`. -/
theorem fourier_weightedDeriv (c : ℝ) (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (weightedDeriv c g : ℝ → ℂ) ξ = scaleSymbol c ξ * 𝓕 (g : ℝ → ℂ) ξ := by
  have hsplit : weightedDeriv c g = (c : ℂ) • g + SchwartzMap.derivCLM ℂ ℂ g := by
    simp [weightedDeriv]
  have hd : 𝓕 (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) ξ = (2 * Real.pi * I * ξ) * 𝓕 (g : ℝ → ℂ) ξ := by
    have h := Real.fourier_deriv g.integrable g.differentiable (SchwartzMap.derivCLM ℂ ℂ g).integrable
    exact congrFun h ξ
  rw [← SchwartzMap.fourier_coe, hsplit, FourierTransform.fourier_add, FourierTransform.fourier_smul]
  simp only [add_apply, smul_apply, SchwartzMap.fourier_coe, smul_eq_mul, hd, scaleSymbol]
  ring

/-- [proved-standard; formal-checked] `𝓕 ((c − ∂) g) = (c − 2πiξ) 𝓕 g`. -/
theorem fourier_weightedDerivAdj (c : ℝ) (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (weightedDerivAdj c g : ℝ → ℂ) ξ = conj (scaleSymbol c ξ) * 𝓕 (g : ℝ → ℂ) ξ := by
  rw [← SchwartzMap.fourier_coe, weightedDerivAdj_eq, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, FourierTransform.fourier_smul]
  simp only [add_apply, neg_apply, smul_apply, SchwartzMap.fourier_coe, smul_eq_mul,
    fourier_weightedDeriv, conj_scaleSymbol]
  ring

/-- [proved-standard; formal-checked] **`∂_c` is carried to multiplication by `c + 2πiξ`**: `U_c (∂f) = m · U_c f`. -/
theorem coeFn_mellinPlancherel_scaleDeriv (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (mellinPlancherel c (scaleDeriv c g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => scaleSymbol c ξ * mellinPlancherel c (core c g) ξ := by
  filter_upwards [coeFn_mellinPlancherel_core c (weightedDeriv c g),
    coeFn_mellinPlancherel_core c g] with ξ h1 h2
  rw [scaleDeriv, h1, h2, fourier_weightedDeriv]

/-- [proved-standard; formal-checked] `2c − ∂` is carried to multiplication by `conj (c + 2πiξ)`. -/
theorem coeFn_mellinPlancherel_scaleDerivAdj (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (mellinPlancherel c (scaleDerivAdj c g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => conj (scaleSymbol c ξ) * mellinPlancherel c (core c g) ξ := by
  filter_upwards [coeFn_mellinPlancherel_core c (weightedDerivAdj c g),
    coeFn_mellinPlancherel_core c g] with ξ h1 h2
  rw [scaleDerivAdj, h1, h2, fourier_weightedDerivAdj]

/-! ## Normality on the core -/

/-- [proved-standard; formal-checked] Multiplication by `m` has adjoint multiplication by `conj m` in `L²`. -/
theorem inner_multiplier {α : Type*} [MeasurableSpace α] {μ : Measure α} (m : α → ℂ)
    {a b a' b' : Lp ℂ 2 μ} (ha : (a' : α → ℂ) =ᵐ[μ] fun x => m x * a x)
    (hb : (b' : α → ℂ) =ᵐ[μ] fun x => conj (m x) * b x) :
    inner ℂ a' b = inner ℂ a b' := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha, hb] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  ring

/-- [proved-standard; formal-checked] `‖m h‖ = ‖(conj m) h‖` in `L²`. -/
theorem norm_multiplier {α : Type*} [MeasurableSpace α] {μ : Measure α} (m : α → ℂ)
    {a a' a'' : Lp ℂ 2 μ} (h' : (a' : α → ℂ) =ᵐ[μ] fun x => m x * a x)
    (h'' : (a'' : α → ℂ) =ᵐ[μ] fun x => conj (m x) * a x) :
    ‖a'‖ = ‖a''‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae (g := (a'' : α → ℂ))]
  filter_upwards [h', h''] with x h1 h2
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_conj]

/-- [proved-standard; formal-checked] **The formal adjoint of `∂` in `L²(μ_c)` is `2c − ∂`** on the core. -/
theorem inner_scaleDeriv (c : ℝ) (g h : 𝓢(ℝ, ℂ)) :
    inner ℂ (scaleDeriv c g) (core c h) = inner ℂ (core c g) (scaleDerivAdj c h) := by
  rw [← (mellinPlancherel c).inner_map_map, ← (mellinPlancherel c).inner_map_map (core c g)]
  exact inner_multiplier (scaleSymbol c) (coeFn_mellinPlancherel_scaleDeriv c g)
    (coeFn_mellinPlancherel_scaleDerivAdj c h)

/-- [proved-standard; formal-checked] `∂ − c` is skew on the core: `⟪(∂ − c)f, g⟫ = −⟪f, (∂ − c)g⟫`. -/
theorem inner_scaleDeriv_sub (c : ℝ) (g h : 𝓢(ℝ, ℂ)) :
    inner ℂ (scaleDeriv c g - (c : ℂ) • core c g) (core c h) =
      -inner ℂ (core c g) (scaleDeriv c h - (c : ℂ) • core c h) := by
  rw [inner_sub_left, inner_smul_left, inner_scaleDeriv, scaleDerivAdj_eq, inner_sub_right,
    inner_sub_right, inner_smul_right, inner_smul_right, Complex.conj_ofReal]
  ring

/-- [proved-standard; formal-checked] **Normality on the core**: `‖∂f‖ = ‖2c f − ∂f‖`. -/
theorem norm_scaleDeriv_eq (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    ‖scaleDeriv c g‖ = ‖(2 * c : ℂ) • core c g - scaleDeriv c g‖ := by
  rw [← scaleDerivAdj_eq, ← (mellinPlancherel c).norm_map,
    ← (mellinPlancherel c).norm_map (scaleDerivAdj c g)]
  exact norm_multiplier (scaleSymbol c) (coeFn_mellinPlancherel_scaleDeriv c g)
    (coeFn_mellinPlancherel_scaleDerivAdj c g)

/-- [proved-standard; formal-checked] `(c + ∂)(c − ∂) = (c − ∂)(c + ∂)` on Schwartz space. -/
theorem weightedDeriv_comm (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    weightedDeriv c (weightedDerivAdj c g) = weightedDerivAdj c (weightedDeriv c g) := by
  have : (weightedDeriv c).comp (weightedDerivAdj c) = (weightedDerivAdj c).comp (weightedDeriv c) := by
    simp only [weightedDeriv, weightedDerivAdj, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
    module
  exact congrArg (fun T => T g) this

/-- [proved-standard; formal-checked] **`∂` commutes with `2c − ∂`** on the core. -/
theorem scaleDeriv_comm (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    scaleDeriv c (weightedDerivAdj c g) = scaleDerivAdj c (weightedDeriv c g) := by
  rw [scaleDeriv, scaleDerivAdj, weightedDeriv_comm]

/-! ## The operator on its core -/

/-- [definition] The core map `g ↦ e^{cx} g`, `𝓢(ℝ, ℂ) → L²(μ_c)`. -/
def coreMap (c : ℝ) : 𝓢(ℝ, ℂ) →ₗ[ℂ] Lp ℂ 2 (lineMeasure c) :=
  (weightEquiv c).symm.toLinearEquiv.toLinearMap ∘ₗ
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

/-- [proved-standard; formal-checked] `coreMap c g = core c g`. -/
theorem coreMap_apply (c : ℝ) (g : 𝓢(ℝ, ℂ)) : coreMap c g = core c g := by
  simp [coreMap, core]

/-- [proved-standard; formal-checked] The core map is injective. -/
theorem coreMap_injective (c : ℝ) : Function.Injective (coreMap c) := by
  intro g h hgh
  simp only [coreMap_apply, core] at hgh
  exact SchwartzMap.injective_toLp 2 volume ((weightEquiv c).symm.injective hgh)

/-- [definition] The core `{e^{cx} g : g ∈ 𝓢(ℝ, ℂ)}` as a submodule of `L²(μ_c)`. -/
def coreDomain (c : ℝ) : Submodule ℂ (Lp ℂ 2 (lineMeasure c)) := LinearMap.range (coreMap c)

/-- [proved-standard; formal-checked] **The core is dense in `L²(μ_c)`.** -/
theorem dense_coreDomain (c : ℝ) : Dense (coreDomain c : Set (Lp ℂ 2 (lineMeasure c))) := by
  have h1 : DenseRange (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  have h2 : DenseRange ((weightEquiv c).symm ∘ SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) :=
    (weightEquiv c).symm.surjective.denseRange.comp h1 (weightEquiv c).symm.continuous
  rw [coreDomain, LinearMap.coe_range]
  exact h2

/-- [definition] The core as a copy of Schwartz space. -/
def coreEquiv (c : ℝ) : 𝓢(ℝ, ℂ) ≃ₗ[ℂ] coreDomain c :=
  LinearEquiv.ofInjective (coreMap c) (coreMap_injective c)

/-- [proved-standard; formal-checked] `coreEquiv c g = core c g`. -/
theorem coe_coreEquiv (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (coreEquiv c g : Lp ℂ 2 (lineMeasure c)) = core c g :=
  coreMap_apply c g

/-- [proved-standard; formal-checked] Every core element is `core c g` for its Schwartz `g`. -/
theorem coreDomain_eq (c : ℝ) (x : coreDomain c) :
    (x : Lp ℂ 2 (lineMeasure c)) = core c ((coreEquiv c).symm x) := by
  rw [← coe_coreEquiv, LinearEquiv.apply_symm_apply]

/-- [definition] **The scale derivative `∂` on its core**, a densely defined operator on `L²(μ_c)`. -/
def scaleDerivOp (c : ℝ) : Lp ℂ 2 (lineMeasure c) →ₗ.[ℂ] Lp ℂ 2 (lineMeasure c) where
  domain := coreDomain c
  toFun := coreMap c ∘ₗ (weightedDeriv c).toLinearMap ∘ₗ (coreEquiv c).symm.toLinearMap

/-- [definition] **`2c − ∂` on the same core.** -/
def scaleDerivAdjOp (c : ℝ) : Lp ℂ 2 (lineMeasure c) →ₗ.[ℂ] Lp ℂ 2 (lineMeasure c) where
  domain := coreDomain c
  toFun := coreMap c ∘ₗ (weightedDerivAdj c).toLinearMap ∘ₗ (coreEquiv c).symm.toLinearMap

/-- [proved-standard; formal-checked] The operator `∂` acts on the core as `scaleDeriv`. -/
theorem scaleDerivOp_apply (c : ℝ) (x : coreDomain c) :
    scaleDerivOp c x = scaleDeriv c ((coreEquiv c).symm x) := by
  simp [scaleDerivOp, scaleDeriv, coreMap_apply]

/-- [proved-standard; formal-checked] The operator `2c − ∂` acts on the core as `scaleDerivAdj`. -/
theorem scaleDerivAdjOp_apply (c : ℝ) (x : coreDomain c) :
    scaleDerivAdjOp c x = scaleDerivAdj c ((coreEquiv c).symm x) := by
  simp [scaleDerivAdjOp, scaleDerivAdj, coreMap_apply]

/-- [proved-standard; formal-checked] **`2c − ∂` is a formal adjoint of `∂`** in `L²(μ_c)`. -/
theorem isFormalAdjoint_scaleDerivOp (c : ℝ) :
    (scaleDerivOp c).IsFormalAdjoint (scaleDerivAdjOp c) := by
  intro x y
  have h1 : scaleDerivOp c x = scaleDeriv c ((coreEquiv c).symm x) := scaleDerivOp_apply c x
  have h2 : scaleDerivAdjOp c y = scaleDerivAdj c ((coreEquiv c).symm y) :=
    scaleDerivAdjOp_apply c y
  have h3 : (x : Lp ℂ 2 (lineMeasure c)) = core c ((coreEquiv c).symm x) := coreDomain_eq c x
  have h4 : (y : Lp ℂ 2 (lineMeasure c)) = core c ((coreEquiv c).symm y) := coreDomain_eq c y
  rw [h1, h2, h3, h4]
  exact inner_scaleDeriv c _ _

/-- [proved-standard; formal-checked] **The adjoint of `∂` contains `2c − ∂`.** -/
theorem scaleDerivAdjOp_le_adjoint (c : ℝ) : scaleDerivAdjOp c ≤ (scaleDerivOp c).adjoint :=
  (isFormalAdjoint_scaleDerivOp c).le_adjoint (dense_coreDomain c)

/-- [proved-standard; formal-checked] **Normality on the core**, operator form: `‖∂x‖ = ‖(2c − ∂)x‖`. -/
theorem norm_scaleDerivOp_eq (c : ℝ) (x : coreDomain c) :
    ‖scaleDerivOp c x‖ = ‖scaleDerivAdjOp c x‖ := by
  rw [scaleDerivOp_apply, scaleDerivAdjOp_apply, scaleDerivAdj_eq, ← norm_scaleDeriv_eq]

/-! ## The shift group and the averaged shift -/

/-- [proved-standard; formal-checked] `e^{cu} e^{−c(x+u)} = e^{−cx}`. -/
theorem weight_shift (c x u : ℝ) : weight (-c) u * weight c (x + u) = weight c x := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- [proved-standard; formal-checked] **The shift is `e^{u∂}`**: `𝓕 (W_c T_u f) = e^{(c+2πiξ)u} 𝓕 (W_c f)`. -/
theorem fourier_weight_shift (c u : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => weight c x * f (x + u)) ξ =
      cexp (scaleSymbol c ξ * u) * 𝓕 (fun x => weight c x * f x) ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  conv_rhs => rw [← integral_add_right_eq_self _ u]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [weight, scaleSymbol, Complex.ofReal_exp]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- [definition] The shift `T_u` on the core: `(T_u f)(x) = f(x + u)` for `f = e^{cx} g`. -/
def shiftCore (c u : ℝ) (g : 𝓢(ℝ, ℂ)) : Lp ℂ 2 (lineMeasure c) :=
  core c ((Real.exp (c * u) : ℂ) • SchwartzMap.compSubConstCLM ℂ (-u) g)

/-- [proved-standard; formal-checked] `shiftCore c u g` is `x ↦ f(x + u)` for `f = e^{cx} g`. -/
theorem coeFn_shiftCore (c u : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (shiftCore c u g : ℝ → ℂ) =ᵐ[lineMeasure c] fun x => weight (-c) (x + u) * g (x + u) := by
  filter_upwards [coeFn_core c ((Real.exp (c * u) : ℂ) • SchwartzMap.compSubConstCLM ℂ (-u) g)]
    with x h
  rw [shiftCore, h, smul_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul,
    ← mul_assoc]
  congr 1
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- [proved-standard; formal-checked] **`U_c (T_u f) = e^{(c+2πiξ)u} U_c f`** on the core. -/
theorem coeFn_mellinPlancherel_shiftCore (c u : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (mellinPlancherel c (shiftCore c u g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => cexp (scaleSymbol c ξ * u) * mellinPlancherel c (core c g) ξ := by
  filter_upwards [coeFn_mellinPlancherel_core c
      ((Real.exp (c * u) : ℂ) • SchwartzMap.compSubConstCLM ℂ (-u) g),
    coeFn_mellinPlancherel_core c g] with ξ h1 h2
  rw [shiftCore, h1, h2]
  have hrep : ((((Real.exp (c * u) : ℂ) • SchwartzMap.compSubConstCLM ℂ (-u) g :
      𝓢(ℝ, ℂ)) : ℝ → ℂ)) = fun x => weight c x * (weight (-c) (x + u) * g (x + u)) := by
    funext x
    rw [smul_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, ← mul_assoc]
    congr 1
    unfold weight
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hrep, fourier_weight_shift c u (fun x => weight (-c) x * g x)]
  congr 1
  refine congrArg (fun h : ℝ → ℂ => 𝓕 h ξ) (funext fun x => ?_)
  rw [← mul_assoc, weight_mul_weight_neg, one_mul]

/-- [proved-standard; formal-checked] The averaged-shift kernel `W_c f(x+u) · w(u)e^{cu}` is integrable on `ℝ²`. -/
theorem integrable_average_kernel (c : ℝ) {w f : ℝ → ℂ}
    (hw : Integrable (fun u => w u * weight (-c) u)) (hf : Integrable (fun x => weight c x * f x)) :
    Integrable (fun z : ℝ × ℝ => (weight c (z.1 + z.2) * f (z.1 + z.2)) * (w z.2 * weight (-c) z.2))
      (volume.prod volume) := by
  have h0 := hf.mul_prod hw
  have hmp := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  exact (hmp.integrable_comp h0.aestronglyMeasurable).2 h0

/-- [proved-standard; formal-checked] The averaged shift `∫ w(u) T_u f du` keeps `W_c (·) ∈ L¹`. -/
theorem integrable_weight_average (c : ℝ) {w f : ℝ → ℂ}
    (hw : Integrable (fun u => w u * weight (-c) u)) (hf : Integrable (fun x => weight c x * f x)) :
    Integrable (fun x => weight c x * ∫ u, w u * f (x + u)) := by
  refine (integrable_average_kernel c hw hf).integral_prod_left.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [← weight_shift c x u]
  ring

/-- [proved-standard; formal-checked] **The Bochner identity**: `∫ w(u) T_u f du` is carried to `F(c + 2πiξ)`. -/
theorem fourier_weight_average (c : ℝ) {w f : ℝ → ℂ}
    (hw : Integrable (fun u => w u * weight (-c) u)) (hf : Integrable (fun x => weight c x * f x))
    (ξ : ℝ) :
    𝓕 (fun x => weight c x * ∫ u, w u * f (x + u)) ξ =
      (∫ u, w u * cexp (scaleSymbol c ξ * u)) * 𝓕 (fun x => weight c x * f x) ξ := by
  set e : ℝ → ℂ := fun x => cexp (↑(-2 * Real.pi * x * ξ) * I) with he
  set F : ℝ → ℝ → ℂ := fun x u => e x * (w u * (weight c x * f (x + u))) with hF
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hb : Integrable (fun z : ℝ × ℝ => e z.1 *
        ((weight c (z.1 + z.2) * f (z.1 + z.2)) * (w z.2 * weight (-c) z.2))) (volume.prod volume) :=
      (integrable_average_kernel c hw hf).bdd_mul (c := 1) (by rw [he]; fun_prop)
        (ae_of_all _ fun z => by rw [he, Complex.norm_exp_ofReal_mul_I])
    refine hb.congr (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, hF]
    rw [← weight_shift c z.1 z.2]
    ring
  calc 𝓕 (fun x => weight c x * ∫ u, w u * f (x + u)) ξ
      = ∫ x, ∫ u, F x u := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [smul_eq_mul, hF, he]
        rw [← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        ring
    _ = ∫ u, ∫ x, F x u := integral_integral_swap hFint
    _ = ∫ u, w u * cexp (scaleSymbol c ξ * u) * 𝓕 (fun x => weight c x * f x) ξ := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [hF, he]
        rw [mul_assoc, ← fourier_weight_shift, Real.fourier_real_eq_integral_exp_smul,
          ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [smul_eq_mul]
        ring
    _ = (∫ u, w u * cexp (scaleSymbol c ξ * u)) * 𝓕 (fun x => weight c x * f x) ξ :=
        integral_mul_const _ _

/-- [proved-standard; formal-checked] **The Bochner identity in `L²`**: `U_c (∫ w T_u f du) = F(c + 2πiξ) U_c f`. -/
theorem coeFn_mellinPlancherel_average (c : ℝ) {w f : ℝ → ℂ}
    (hw : Integrable (fun u => w u * weight (-c) u)) (hf2 : MemLp f 2 (lineMeasure c))
    (hf : Integrable (fun x => weight c x * f x))
    (hA : MemLp (fun x => ∫ u, w u * f (x + u)) 2 (lineMeasure c)) :
    (mellinPlancherel c (hA.toLp _) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (∫ u, w u * cexp (scaleSymbol c ξ * u)) * mellinPlancherel c (hf2.toLp f) ξ := by
  filter_upwards [lineTransform_ae_eq_mellinPlancherel c hA (integrable_weight_average c hw hf),
    lineTransform_ae_eq_mellinPlancherel c hf2 hf] with ξ h1 h2
  rw [← h1, ← h2, lineTransform_scaleSymbol, lineTransform_scaleSymbol,
    fourier_weight_average c hw hf]

/-! ## Hearing's instance -/

open Holonics.Zeta.HeatKernelPhi (flowLap lap Φ flow_dominant continuous_lap heatE_riemannXi)
open Holonics.Zeta.HeatFlowEntire (heatE)
open Holonics.Zeta.RiemannXi (riemannXi)

/-- [definition] Hearing's weight `w_τ(u) = e^{τu²} e^{−u/2} Φ(u)`. -/
def hearingWeight (τ u : ℝ) : ℂ := cexp ((τ : ℂ) * (u : ℂ) ^ 2) * (cexp (-(1 / 2) * u) * (Φ u : ℂ))

/-- [proved-derived; formal-checked] `w_τ(u) e^{su} = flowLap (−τ) s u`. -/
theorem hearingWeight_mul_exp (τ u : ℝ) (s : ℂ) :
    hearingWeight τ u * cexp (s * u) = flowLap (-τ) s u := by
  unfold hearingWeight flowLap lap
  have h : cexp ((s - 1 / 2) * u) = cexp (-(1 / 2) * u) * cexp (s * u) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [h]
  push_cast
  ring_nf

/-- [proved-derived; formal-checked] The flowed integrand is integrable at every time and abscissa. -/
theorem integrable_flowLap (t : ℝ) (z : ℂ) : Integrable (flowLap t z) := by
  obtain ⟨K, -, hbound, hdom⟩ := flow_dominant t z
  refine hbound.mono' ?_ (ae_of_all _ fun u => ?_)
  · unfold flowLap
    exact ((by fun_prop : Continuous fun u : ℝ => cexp (-(t : ℂ) * (u : ℂ) ^ 2)).mul
      (continuous_lap z)).aestronglyMeasurable
  · unfold flowLap
    rw [norm_mul, Complex.norm_exp]
    refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (hdom u)
    have hre : (-(t : ℂ) * (u : ℂ) ^ 2).re = -t * u ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    have := neg_abs_le t
    nlinarith [sq_nonneg u]

/-- [proved-derived; formal-checked] Hearing's weight meets the Bochner hypothesis at every abscissa. -/
theorem integrable_hearingWeight (τ c : ℝ) :
    Integrable (fun u => hearingWeight τ u * weight (-c) u) := by
  refine (integrable_flowLap (-τ) c).congr (ae_of_all _ fun u => ?_)
  rw [← hearingWeight_mul_exp]
  simp only [weight, Complex.ofReal_exp, Complex.ofReal_mul, neg_neg]

/-- [proved-derived; formal-checked] **Hearing's symbol is the Bochner multiplier**: `∫ w_τ e^{su} = heatE (−τ) ξ s`. -/
theorem integral_hearingWeight (τ : ℝ) (s : ℂ) :
    ∫ u, hearingWeight τ u * cexp (s * u) = heatE (-τ) riemannXi s := by
  rw [heatE_riemannXi]
  exact integral_congr_ae (ae_of_all _ fun u => hearingWeight_mul_exp τ u s)

/-- [proved-derived; formal-checked] **`F(∂_c)` is multiplication by `heatE (−τ) ξ (c + 2πiξ)`.** -/
theorem fourier_weight_hearingAverage (τ c : ℝ) {f : ℝ → ℂ}
    (hf : Integrable (fun x => weight c x * f x)) (ξ : ℝ) :
    𝓕 (fun x => weight c x * ∫ u, hearingWeight τ u * f (x + u)) ξ =
      heatE (-τ) riemannXi (scaleSymbol c ξ) * 𝓕 (fun x => weight c x * f x) ξ := by
  rw [fourier_weight_average c (integrable_hearingWeight τ c) hf, integral_hearingWeight]

/-- [proved-derived; formal-checked] **The multiplier vanishes nowhere iff the ear hears no zero on `Re s = c`.** -/
theorem verticalZeroFree_iff_multiplier_ne_zero (τ c : ℝ) :
    Holonics.Zeta.Hearing.VerticalZeroFree τ c ↔
      ∀ ξ : ℝ, heatE (-τ) riemannXi (scaleSymbol c ξ) ≠ 0 := by
  unfold Holonics.Zeta.Hearing.VerticalZeroFree
  constructor
  · intro h ξ
    rw [scaleSymbol_eq]
    exact h _
  · intro h y
    have := h (y / (2 * Real.pi))
    rw [scaleSymbol_eq] at this
    have hy : 2 * Real.pi * (y / (2 * Real.pi)) = y := by
      field_simp
    rwa [hy] at this

/-- [proved-derived; formal-checked] Hearing's truncation coordinate `c + iy` is `scaleSymbol c (y/(2π))`. -/
theorem truncatedScaleDerivative_apply (c T : ℝ) (y : Set.Icc (-T) T) :
    Holonics.Zeta.Hearing.truncatedScaleDerivative c T y = scaleSymbol c ((y : ℝ) / (2 * Real.pi)) := by
  rw [scaleSymbol_eq]
  have hy : 2 * Real.pi * ((y : ℝ) / (2 * Real.pi)) = y := by
    field_simp
  rw [hy]
  rfl

end Holonics.Zeta.MellinPlancherel
