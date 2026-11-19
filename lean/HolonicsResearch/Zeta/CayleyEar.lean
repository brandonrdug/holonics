import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import HolonicsResearch.Zeta.MellinPlancherel

/-!
# The whole-line ear is a bounded normal operator, never invertible, the `cfc` of a Cayley unitary

On `L²(μ_c)`, `μ_c = e^{−2cx}dx`, the whole-line ear `F(∂_c)`, `F = heatE (−τ) ξ`, is the bounded
normal operator `earOp τ c` that the Mellin–Plancherel unitary carries to multiplication by
`ξ ↦ heatE (−τ) ξ (c + 2πiξ)`. It is the continuous functional calculus of the Cayley unitary
`cayleyEar c` of `A = ∂_c − c` (`earOp_eq_cfc`), it is Hearing's averaged shift where that
average lies in `L²(μ_c)` (`earOp_eq_average`), and at every `τ` and `c` it is not invertible
(`not_isUnit_earOp`), because its symbol tends to `0` at infinity (Riemann–Lebesgue).

[proved-standard; formal-checked] for the multiplication operators, their spectrum and their
functional calculus, the Cayley symbol and the conjugation; [proved-derived; formal-checked] for
the Cayley unitary on the core and its uniqueness there, the ear, its spectrum and its
non-invertibility.

Sources. Issue #410, the box "the operator-level ear: `∂_c` on `L²(ℝ, e^(−2cx)dx)`, its
normality, and Mellin–Plancherel (`Zeta/Hearing`)". Atlas rows `rh.spectral-operator`,
`rh.sharpened-hearing-threshold` and `rh.mellin-plancherel-ear` (`docs/atlas/targets.tsv`).
`Zeta/Hearing` (the symbol and truncation levels) and `Zeta/MellinPlancherel` (the unitary
`mellinPlancherel c : L²(μ_c) ≃ₗᵢ L²(dξ)`, the core, `scaleDeriv`, the averaged shift,
`integral_hearingWeight`); both leave open the operator on all of `L²(μ_c)` and its normality,
because Mathlib's functional calculus is for bounded normal elements. The route here is an
outside reader's proposal (November 19): conjugate by the proved unitary and work with bounded
multiplication operators, the Cayley unitary and the ear itself. Mathlib:
`LinearIsometryEquiv.conjStarAlgEquiv`, `ContinuousLinearMap.eq_adjoint_iff`, `L2.inner_def`,
`Real.zero_at_infty_fourier`, `spectrum.subset_circle_of_unitary`,
`cfcHom_eq_of_continuous_of_map_id`, `StarAlgHomClass.map_cfc`, `MemLp.exist_eLpNorm_sub_le`,
`HasCompactSupport.toSchwartzMap`, `FourierTransform.fourier_fourierInv_eq`.

What is proved.

1. **The multiplication operator of a bounded continuous symbol.** For `m : ℝ →ᵇ ℂ`,
   `mulOp m : L²(dξ) →L[ℂ] L²(dξ)` is `f ↦ m f` (`memLp_mul`, `mulOpₗ`, `mulOp`, `coeFn_mulOp`),
   with `‖mulOp m‖ ≤ ‖m‖` (`norm_mulOp_le`) and in fact `‖mulOp m‖ = ‖m‖` (`norm_mulOp`). The
   map `m ↦ mulOp m` is a `⋆`-algebra map: `mulOp_mul`, `mulOp_one`, `mulOp_add`, `mulOp_smul`,
   `mulOp_zero`, `mulOp_sub`, and the adjoint is the conjugate symbol (`mulOp_star`).
2. **Normal and unitary.** Every `mulOp m` is normal (`instIsStarNormalMulOp`); a symbol of
   modulus one gives a unitary (`mulOp_mem_unitary`).
3. **Invertibility and spectrum.** `mulOp m` is invertible if and only if `|m|` is bounded away
   from zero (`isUnit_mulOp_iff`; necessity is `not_isUnit_mulOp_of_small`, by the indicator of
   an interval where `|m| ≤ ε`). A symbol that tends to `0` at infinity gives an
   operator that is not invertible (`not_isUnit_mulOp_of_tendsto_zero`). The values of the
   symbol lie in the spectrum (`mem_spectrum_mulOp`, with `algebraMap_sub_mulOp`), and the
   spectrum is the closure of the range of the symbol (`spectrum_mulOp`).
4. **The functional calculus of a multiplication operator.** `g ↦ mulOp (g ∘ m)` is a continuous
   `⋆`-algebra map from `C(spectrum, ℂ)` (`specSymbol`, `norm_specSymbol_le`, `specHom`,
   `continuous_specHom`), so by the uniqueness of the functional calculus
   `cfc f (mulOp m) = mulOp (f ∘ m)` for `f` continuous on the spectrum (`cfc_mulOp`).
5. **The Cayley symbol** `V(ξ) = (2πiξ − 1)/(2πiξ + 1)` (`cayleySymbol`, with
   `cayleyDen_ne_zero`, `norm_cayleyNum`) has modulus one (`norm_cayleySymbol`), never takes the
   value `1` (`cayleySymbol_ne_one`), and `V(ξ)(2πiξ + 1) = 2πiξ − 1` (`cayleySymbol_mul`). Every
   `w ≠ 1` of the unit circle is the value at `cayleyCoord w`, where
   `2πi · cayleyCoord w = (1 + w)/(1 − w)` (`two_pi_I_mul_cayleyCoord`,
   `cayleySymbol_cayleyCoord`), and `1` is a limit of values
   (`one_mem_closure_range_cayleySymbol`), so the spectrum of `mulOp V` is the whole circle
   (`spectrum_mulOp_cayleySymbol`).
6. **Conjugation to `L²(μ_c)`.** `pull c T = U_c⁻¹ T U_c` is Mathlib's `conjStarAlgEquiv` of the
   Mellin–Plancherel unitary (`pull`, `mellinPlancherel_pull`); `pull_mul`, `pull_one` and
   `pull_star` restate that it is a `⋆`-homomorphism. It keeps normality
   (`instIsStarNormalPull`), unitaries (`pull_mem_unitary`), invertibility (`isUnit_pull_iff`)
   and the spectrum (`spectrum_pull`), and is continuous (`norm_pull_le`, `continuous_pull`).
7. **The Cayley unitary of `A = ∂_c − c`.** `cayleyEar c = pull c (mulOp V)` is unitary
   (`cayleyEar_mem_unitary`) and on the core it is the Cayley transform of `A`:
   `V (A + 1) f = (A − 1) f` (`cayleyEar_core`, from `coeFn_mellinPlancherel_shifted`). Its
   spectrum is the whole unit circle (`spectrum_cayleyEar`), and `1`, which lies in the spectrum,
   is not an eigenvalue (`cayleyEar_apply_eq_self_iff`).
8. **The ear on the whole line.** The symbol `ξ ↦ heatE (−τ) ξ (c + 2πiξ)` is continuous and
   bounded by `∫ |w_τ(u)| e^{cu} du` (`continuous_scaleSymbol`, `norm_heatE_scaleSymbol_le`,
   `earSymbol`). `earOp τ c = pull c (mulOp (earSymbol τ c))` is normal
   (`instIsStarNormalEarOp`), commutes with the Cayley unitary (`earOp_comm_cayleyEar`), is
   carried by `U_c` to multiplication by the flowed function on the line
   (`coeFn_mellinPlancherel_earOp`), and for `f ∈ L²(μ_c)` with `W_c f ∈ L¹` whose averaged shift
   `∫ w_τ(u) f(· + u) du` lies in `L²(μ_c)` it is that averaged shift (`earOp_eq_average`).
9. **The whole-line ear is never invertible.** The symbol is the Fourier transform of
   `w_τ(u) e^{cu}` at `−ξ` (`earSymbol_eq_fourier`), so it tends to `0` at infinity
   (`tendsto_earSymbol`), and `earOp τ c` is not a unit, at every `τ` and `c`
   (`not_isUnit_earOp`); `0` lies in its spectrum (`zero_mem_spectrum_earOp`), which is the
   closure of the values of the flowed function on the line (`spectrum_earOp`). The Cayley
   unitary, in the same algebra, is a unit (`isUnit_cayleyEar`): non-invertibility is a property
   of the ear's symbol and not of every operator here.
10. **Side by side with the truncations.** At every `τ` and `c` the whole-line ear is not a unit,
    while `Hearing.QuasiInvertible (heatE (−τ) ξ) c ↔ Hearing.VerticalZeroFree τ c`, and that
    holds if and only if the whole-line symbol vanishes nowhere
    (`wholeLine_not_isUnit_and_truncations_criterion`).
11. **The ear is the functional calculus of the Cayley unitary.** With
    `earCircle τ c w = heatE (−τ) ξ (c + (1 + w)/(1 − w))` for `w ≠ 1` and `0` at `w = 1`
    (`earCircle`), `earCircle ∘ V` is the ear's symbol (`earCircle_cayleySymbol`,
    `earCircle_eq_earSymbol`), `earCircle` is continuous on the unit circle, its value `0` at `1`
    being the Riemann–Lebesgue limit (`continuousOn_earCircle`), and
    `earOp τ c = cfc (earCircle τ c) (cayleyEar c)` (`earOp_eq_cfc`).
12. **The core determines the Cayley unitary.** For `a` off the imaginary axis, `A + a` has dense
    range on the core (`denseRange_scaleDeriv_sub_add`; on the Mellin side the range holds every
    smooth compactly supported `ψ`, as `(2πiξ + a) · ψ/(2πiξ + a)`:
    `two_pi_I_mul_add_ne_zero`, `exists_schwartz_fourier_mul_eq`,
    `denseRange_mellinPlancherel_scaleDeriv_sub_add`). So the domain `(A + 1)(core)` and the range
    `(A − 1)(core)` of the Cayley transform are dense (`denseRange_cayleyDomain`,
    `denseRange_cayleyRange`), and a bounded operator `W` with `W (A + 1) f = (A − 1) f` on the
    core is `cayleyEar c` (`eq_cayleyEar_of_core`). This is what lets item 7 call `cayleyEar c`
    the Cayley unitary of `A`, and not only a conjugate of the Cayley multiplier.

The unfolding lemmas `pull_apply`, `cayleySymbol_apply`, `earSymbol_apply` and `earCircle_one`
hold by definition and are not content.

Limits. The closed operator is still not constructed as an object. `A = ∂_c − c` stands on its
Schwartz core; what is proved there is that `A ± 1` have dense range and that `cayleyEar c` is
the one bounded operator with `V (A + 1) f = (A − 1) f`. The closure of `A` as a `LinearPMap`,
its skew-adjointness and its spectrum `iℝ` stated for that closure (the inverse Cayley transform
of `cayleyEar c`), and a functional calculus of the closed operator are not stated;
`earOp_eq_cfc` is a statement about the bounded unitary. `earOp_eq_average` keeps as hypotheses
that `W_c f ∈ L¹` and that the averaged shift lies in `L²(μ_c)` (Young's inequality is not
proved), so the equality of `earOp` with the averaged shift on all of `L²(μ_c)` is not claimed.
Item 10 places two statements side by side: `Hearing.QuasiInvertible` is still the coordinate
model `C([−T, T], ℂ)`, and the band-limited compressions of `earOp τ c` are not constructed or
identified with that model. Symbols are bounded continuous functions on `ℝ` with Lebesgue
measure; `L^∞` symbols and other measures are not treated. Nothing here bears on where the
flowed function vanishes.

Computational object: the helical pair interaction read on the scale line. The symbol `c + iy`
is a boost `c` plus `i` times a turn `y`, and the Cayley map sends the turn's line to the circle,
the point at infinity to `1`. Of the winding guide's six general objects it touches the helix
(the turn `2πξ`), the tube (the shift group, whose average the ear is) and faces and placement
(the multiplier each mode reads); the pair, cell holonomy and the tower thread stay attached and
are not used here.

Consumers. Issue #410's box and the atlas rows `rh.spectral-operator`,
`rh.sharpened-hearing-threshold` and `rh.mellin-plancherel-ear`; the reading that the whole-line
ear is a bounded normal operator that is never invertible, so only its band-limited compressions
(`Hearing.QuasiInvertible`) can be a criterion.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Zeta.CayleyEar

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate BoundedContinuousFunction SchwartzMap
open Holonics.Zeta.MellinPlancherel
open Holonics.Zeta.HeatFlowEntire (heatE)
open Holonics.Zeta.RiemannXi (riemannXi)

/-! ## The multiplication operator of a bounded continuous symbol -/

/-- [proved-standard; formal-checked] `m f ∈ L²(dξ)` for a bounded continuous `m` and
`f ∈ L²(dξ)`. -/
theorem memLp_mul (m : ℝ →ᵇ ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ => m ξ * f ξ) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := ‖m‖)
    (m.continuous.aestronglyMeasurable.mul (Lp.memLp f).1) (ae_of_all _ fun ξ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm ξ) (norm_nonneg _)

/-- [definition] Multiplication by a bounded continuous symbol as a linear map of `L²(dξ)`. -/
def mulOpₗ (m : ℝ →ᵇ ℂ) : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (memLp_mul m f).toLp _
  map_add' f g := by
    ext1
    filter_upwards [(memLp_mul m (f + g)).coeFn_toLp, (memLp_mul m f).coeFn_toLp,
      (memLp_mul m g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_mul m f).toLp _) ((memLp_mul m g).toLp _)] with ξ h1 h2 h3 h4 h5
    rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, mul_add]
  map_smul' r f := by
    ext1
    filter_upwards [(memLp_mul m (r • f)).coeFn_toLp, (memLp_mul m f).coeFn_toLp,
      Lp.coeFn_smul r f, Lp.coeFn_smul r ((memLp_mul m f).toLp _)] with ξ h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- [definition] **The multiplication operator** `f ↦ m f` of a bounded continuous symbol `m` on
`L²(dξ)`, a bounded operator of norm at most `‖m‖`. -/
def mulOp (m : ℝ →ᵇ ℂ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (mulOpₗ m).mkContinuous ‖m‖ fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_mul m f).coeFn_toLp] with ξ h
    change ‖(memLp_mul m f).toLp _ ξ‖ ≤ _
    rw [h, norm_mul]
    exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm ξ) (norm_nonneg _)

/-- [proved-standard; formal-checked] `mulOp m f = m f` almost everywhere. -/
theorem coeFn_mulOp (m : ℝ →ᵇ ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mulOp m f : ℝ → ℂ) =ᵐ[volume] fun ξ => m ξ * f ξ :=
  (memLp_mul m f).coeFn_toLp

/-- [proved-standard; formal-checked] `‖mulOp m‖ ≤ ‖m‖`. -/
theorem norm_mulOp_le (m : ℝ →ᵇ ℂ) : ‖mulOp m‖ ≤ ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg m) _

/-- [proved-standard; formal-checked] The product of symbols is the composition of operators. -/
theorem mulOp_mul (m₁ m₂ : ℝ →ᵇ ℂ) : mulOp (m₁ * m₂) = mulOp m₁ * mulOp m₂ := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext1
  filter_upwards [coeFn_mulOp (m₁ * m₂) f, coeFn_mulOp m₁ (mulOp m₂ f), coeFn_mulOp m₂ f]
    with ξ h1 h2 h3
  have e : (mulOp m₁ * mulOp m₂) f = mulOp m₁ (mulOp m₂ f) := rfl
  rw [h1, e, h2, h3, BoundedContinuousFunction.mul_apply, mul_assoc]

/-- [proved-standard; formal-checked] The symbol `1` gives the identity. -/
theorem mulOp_one : mulOp 1 = 1 := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext1
  filter_upwards [coeFn_mulOp 1 f] with ξ h
  have e : (1 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) f = f := rfl
  rw [h, e, BoundedContinuousFunction.coe_one, Pi.one_apply, one_mul]

/-- [proved-standard; formal-checked] `mulOp` is additive in the symbol. -/
theorem mulOp_add (m₁ m₂ : ℝ →ᵇ ℂ) : mulOp (m₁ + m₂) = mulOp m₁ + mulOp m₂ := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext1
  filter_upwards [coeFn_mulOp (m₁ + m₂) f, coeFn_mulOp m₁ f, coeFn_mulOp m₂ f,
    Lp.coeFn_add (mulOp m₁ f) (mulOp m₂ f)] with ξ h1 h2 h3 h4
  have e : (mulOp m₁ + mulOp m₂) f = mulOp m₁ f + mulOp m₂ f := rfl
  rw [h1, e, h4, Pi.add_apply, h2, h3, BoundedContinuousFunction.add_apply, add_mul]

/-- [proved-standard; formal-checked] `mulOp` is `ℂ`-homogeneous in the symbol. -/
theorem mulOp_smul (a : ℂ) (m : ℝ →ᵇ ℂ) : mulOp (a • m) = a • mulOp m := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext1
  filter_upwards [coeFn_mulOp (a • m) f, coeFn_mulOp m f, Lp.coeFn_smul a (mulOp m f)]
    with ξ h1 h2 h3
  have e : (a • mulOp m) f = a • mulOp m f := rfl
  rw [h1, e, h3, Pi.smul_apply, h2, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_assoc]

/-- [proved-standard; formal-checked] **The adjoint is multiplication by the conjugate symbol.** -/
theorem mulOp_star (m : ℝ →ᵇ ℂ) : mulOp (star m) = star (mulOp m) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp (star m) f, coeFn_mulOp m g] with ξ h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul,
    BoundedContinuousFunction.star_apply, RCLike.star_def, Complex.conj_conj]
  ring

/-! ## Normal and unitary -/

/-- [proved-standard; formal-checked] **Every multiplication operator is normal.** -/
instance instIsStarNormalMulOp (m : ℝ →ᵇ ℂ) : IsStarNormal (mulOp m) :=
  ⟨by rw [commute_iff_eq, ← mulOp_star, ← mulOp_mul, ← mulOp_mul, mul_comm]⟩

/-- [proved-standard; formal-checked] **A symbol of modulus one gives a unitary.** -/
theorem mulOp_mem_unitary (m : ℝ →ᵇ ℂ) (hm : ∀ ξ, ‖m ξ‖ = 1) :
    mulOp m ∈ unitary (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  have h : star m * m = 1 := by
    ext ξ
    rw [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply,
      BoundedContinuousFunction.coe_one, Pi.one_apply, RCLike.star_def, Complex.conj_mul', hm ξ]
    norm_num
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [← mulOp_star, ← mulOp_mul, h, mulOp_one]
  · rw [← mulOp_star, ← mulOp_mul, mul_comm, h, mulOp_one]

/-! ## Invertibility is a lower bound of the symbol -/

/-- [proved-standard; formal-checked] If the symbol is at most `ε` on some interval of positive
length, for every `ε > 0`, the multiplication operator is not invertible: the indicator of that
interval is a nonzero `h` with `‖m h‖ ≤ ε ‖h‖`, and a unit is bounded below. -/
theorem not_isUnit_mulOp_of_small (m : ℝ →ᵇ ℂ)
    (hm : ∀ ε > 0, ∃ a b : ℝ, a < b ∧ ∀ ξ ∈ Icc a b, ‖m ξ‖ ≤ ε) : ¬ IsUnit (mulOp m) := by
  rintro ⟨u, hu⟩
  set B : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := ↑u⁻¹
  have hBm : B * mulOp m = 1 := by rw [← hu]; exact u.inv_mul
  have hε : 0 < 1 / (‖B‖ + 1) := by positivity
  obtain ⟨a, b, hab, hsmall⟩ := hm _ hε
  have hfin : volume (Icc a b) ≠ ⊤ := by simp
  set h : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 measurableSet_Icc hfin (1 : ℂ) with hh
  have hnorm : 0 < ‖h‖ := by
    rw [hh, norm_indicatorConstLp (by norm_num) (by norm_num), Real.volume_real_Icc_of_le hab.le]
    rw [norm_one, one_mul]
    exact Real.rpow_pos_of_pos (sub_pos.2 hab) _
  have h1 : ‖mulOp m h‖ ≤ 1 / (‖B‖ + 1) * ‖h‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_mulOp m h, indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc)
      (hμs := hfin) (c := (1 : ℂ))] with ξ e1 e2
    rw [e1, norm_mul, e2]
    by_cases hξ : ξ ∈ Icc a b
    · rw [indicator_of_mem hξ]
      simpa using hsmall ξ hξ
    · rw [indicator_of_notMem hξ]
      simp
  have h2 : ‖h‖ ≤ ‖B‖ * ‖mulOp m h‖ := by
    have e : B (mulOp m h) = h := by
      have := congrArg (fun T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) =>
        T h) hBm
      simpa using this
    calc ‖h‖ = ‖B (mulOp m h)‖ := by rw [e]
      _ ≤ ‖B‖ * ‖mulOp m h‖ := B.le_opNorm _
  have h3 : ‖B‖ * (1 / (‖B‖ + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have h4 : ‖h‖ ≤ ‖B‖ * (1 / (‖B‖ + 1)) * ‖h‖ := by
    calc ‖h‖ ≤ ‖B‖ * ‖mulOp m h‖ := h2
      _ ≤ ‖B‖ * (1 / (‖B‖ + 1) * ‖h‖) := by gcongr
      _ = ‖B‖ * (1 / (‖B‖ + 1)) * ‖h‖ := by ring
  have h5 : ‖B‖ * (1 / (‖B‖ + 1)) * ‖h‖ < 1 * ‖h‖ := mul_lt_mul_of_pos_right h3 hnorm
  linarith

/-- [proved-standard; formal-checked] **The multiplication operator is invertible if and only
if its symbol is bounded away from zero.** -/
theorem isUnit_mulOp_iff (m : ℝ →ᵇ ℂ) : IsUnit (mulOp m) ↔ ∃ δ > 0, ∀ ξ, δ ≤ ‖m ξ‖ := by
  constructor
  · intro hU
    by_contra hne
    push Not at hne
    refine not_isUnit_mulOp_of_small m (fun ε hε => ?_) hU
    obtain ⟨ξ₀, hξ₀⟩ := hne ε hε
    have hopen : IsOpen {ξ | ‖m ξ‖ < ε} := isOpen_lt m.continuous.norm continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen ξ₀ hξ₀
    refine ⟨ξ₀, ξ₀ + r / 2, by linarith, fun ξ hξ => le_of_lt (hball ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hξ.1, hξ.2]
  · rintro ⟨δ, hδ, hm⟩
    have hne : ∀ ξ, m ξ ≠ 0 := fun ξ h0 => by
      have := hm ξ
      rw [h0, norm_zero] at this
      linarith
    set mi : ℝ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (fun ξ => (m ξ)⁻¹)
      (m.continuous.inv₀ hne) δ⁻¹ (fun ξ => by
        rw [norm_inv]
        exact inv_anti₀ hδ (hm ξ)) with hmi
    have h : m * mi = 1 := by
      ext ξ
      rw [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.coe_one, Pi.one_apply,
        hmi, BoundedContinuousFunction.coe_ofNormedAddCommGroup, mul_inv_cancel₀ (hne ξ)]
    exact ⟨⟨mulOp m, mulOp mi, by rw [← mulOp_mul, h, mulOp_one],
      by rw [← mulOp_mul, mul_comm, h, mulOp_one]⟩, rfl⟩

/-- [proved-standard; formal-checked] A symbol that tends to `0` at infinity gives an operator
that is not invertible. -/
theorem not_isUnit_mulOp_of_tendsto_zero (m : ℝ →ᵇ ℂ) (hm : Tendsto m (cocompact ℝ) (𝓝 0)) :
    ¬ IsUnit (mulOp m) := by
  refine not_isUnit_mulOp_of_small m fun ε hε => ?_
  have h1 : ∀ᶠ ξ in cocompact ℝ, ‖m ξ‖ < ε := by
    have := hm.eventually (Metric.ball_mem_nhds 0 hε)
    simpa using this
  rw [cocompact_eq_atBot_atTop, eventually_sup] at h1
  obtain ⟨R, hR⟩ := eventually_atTop.1 h1.2
  exact ⟨R, R + 1, by linarith, fun ξ hξ => (hR ξ hξ.1).le⟩

/-! ## The Cayley symbol -/

/-- [proved-standard; formal-checked] `2πiξ + 1 ≠ 0`: its real part is `1`. -/
theorem cayleyDen_ne_zero (ξ : ℝ) : (2 * Real.pi * I * ξ + 1 : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- [proved-standard; formal-checked] `|2πiξ − 1| = |2πiξ + 1|`: the two are mirror images in
the imaginary axis. -/
theorem norm_cayleyNum (ξ : ℝ) :
    ‖(2 * Real.pi * I * ξ - 1 : ℂ)‖ = ‖(2 * Real.pi * I * ξ + 1 : ℂ)‖ := by
  have h : (2 * Real.pi * I * ξ - 1 : ℂ) = -conj (2 * Real.pi * I * ξ + 1 : ℂ) := by
    simp only [map_add, map_mul, map_one, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h, norm_neg, Complex.norm_conj]

/-- [definition] **The Cayley symbol** `ξ ↦ (2πiξ − 1)/(2πiξ + 1)`, the Cayley transform of the
turn `2πiξ`, as a bounded continuous function. -/
def cayleySymbol : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : ℝ => (2 * Real.pi * I * ξ - 1) / (2 * Real.pi * I * ξ + 1))
    (Continuous.div (by fun_prop) (by fun_prop) cayleyDen_ne_zero) 1
    (fun ξ => by
      rw [norm_div, norm_cayleyNum, div_self (norm_ne_zero_iff.2 (cayleyDen_ne_zero ξ))])

/-- [proved-standard; formal-checked] The Cayley symbol at `ξ`. -/
theorem cayleySymbol_apply (ξ : ℝ) :
    cayleySymbol ξ = (2 * Real.pi * I * ξ - 1) / (2 * Real.pi * I * ξ + 1) := rfl

/-- [proved-standard; formal-checked] **The Cayley symbol lies on the unit circle.** -/
theorem norm_cayleySymbol (ξ : ℝ) : ‖cayleySymbol ξ‖ = 1 := by
  rw [cayleySymbol_apply, norm_div, norm_cayleyNum,
    div_self (norm_ne_zero_iff.2 (cayleyDen_ne_zero ξ))]

/-- [proved-standard; formal-checked] **The Cayley symbol never takes the value `1`.** -/
theorem cayleySymbol_ne_one (ξ : ℝ) : cayleySymbol ξ ≠ 1 := by
  rw [cayleySymbol_apply, Ne, div_eq_one_iff_eq (cayleyDen_ne_zero ξ)]
  intro h
  have := congrArg Complex.re h
  simp at this
  norm_num at this

/-- [proved-standard; formal-checked] `V(ξ) (2πiξ + 1) = 2πiξ − 1`. -/
theorem cayleySymbol_mul (ξ : ℝ) :
    cayleySymbol ξ * (2 * Real.pi * I * ξ + 1) = 2 * Real.pi * I * ξ - 1 := by
  rw [cayleySymbol_apply, div_mul_cancel₀ _ (cayleyDen_ne_zero ξ)]

/-! ## Conjugation to `L²(μ_c)` and the Cayley unitary of `∂_c − c` -/

/-- [definition] **Conjugation by the Mellin–Plancherel unitary**: an operator `T` on the Mellin
side `L²(dξ)` is carried to `U_c⁻¹ T U_c` on `L²(μ_c)`. It is Mathlib's
`LinearIsometryEquiv.conjStarAlgEquiv`, so it is a `⋆`-algebra equivalence. -/
def pull (c : ℝ) : (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) ≃⋆ₐ[ℂ]
    (Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c)) :=
  (mellinPlancherel c).symm.conjStarAlgEquiv

/-- [proved-standard; formal-checked] `pull c T f = U_c⁻¹ (T (U_c f))`. -/
theorem pull_apply (c : ℝ) (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (f : Lp ℂ 2 (lineMeasure c)) :
    pull c T f = (mellinPlancherel c).symm (T (mellinPlancherel c f)) := rfl

/-- [proved-standard; formal-checked] `U_c (pull c T f) = T (U_c f)`: the unitary intertwines. -/
theorem mellinPlancherel_pull (c : ℝ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (f : Lp ℂ 2 (lineMeasure c)) :
    mellinPlancherel c (pull c T f) = T (mellinPlancherel c f) := by
  rw [pull_apply, LinearIsometryEquiv.apply_symm_apply]

/-- [proved-standard; formal-checked] `pull` respects composition. -/
theorem pull_mul (c : ℝ) (S T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    pull c (S * T) = pull c S * pull c T := map_mul _ _ _

/-- [proved-standard; formal-checked] `pull` carries the identity to the identity. -/
theorem pull_one (c : ℝ) : pull c 1 = 1 := map_one _

/-- [proved-standard; formal-checked] `pull` respects adjoints. -/
theorem pull_star (c : ℝ) (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    pull c (star T) = star (pull c T) := map_star _ _

/-- [proved-standard; formal-checked] `pull` keeps normality. -/
instance instIsStarNormalPull (c : ℝ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) [hT : IsStarNormal T] :
    IsStarNormal (pull c T) :=
  ⟨by rw [commute_iff_eq, ← pull_star, ← pull_mul, ← pull_mul, hT.star_comm_self.eq]⟩

/-- [proved-standard; formal-checked] `pull` keeps unitaries. -/
theorem pull_mem_unitary (c : ℝ)
    {T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)}
    (hT : T ∈ unitary (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) :
    pull c T ∈ unitary (Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c)) := by
  rw [Unitary.mem_iff] at hT ⊢
  rw [← pull_star, ← pull_mul, ← pull_mul, hT.1, hT.2, pull_one]
  exact ⟨rfl, rfl⟩

/-- [proved-standard; formal-checked] `pull c T` is invertible if and only if `T` is. -/
theorem isUnit_pull_iff (c : ℝ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    IsUnit (pull c T) ↔ IsUnit T :=
  isUnit_map_iff (pull c) T

/-- [proved-standard; formal-checked] `pull c` does not increase the operator norm. -/
theorem norm_pull_le (c : ℝ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) : ‖pull c T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun f => ?_
  rw [pull_apply, LinearIsometryEquiv.norm_map]
  exact (T.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

/-- [proved-standard; formal-checked] `pull c` is continuous in the operator norm. -/
theorem continuous_pull (c : ℝ) : Continuous (pull c) :=
  AddMonoidHomClass.continuous_of_bound (pull c) 1 fun T => by
    rw [one_mul]
    exact norm_pull_le c T

/-- [definition] **The Cayley unitary of `A = ∂_c − c`** on `L²(μ_c)`: the conjugate of
multiplication by `(2πiξ − 1)/(2πiξ + 1)`. -/
def cayleyEar (c : ℝ) : Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c) :=
  pull c (mulOp cayleySymbol)

/-- [proved-standard; formal-checked] **The Cayley operator is unitary.** -/
theorem cayleyEar_mem_unitary (c : ℝ) :
    cayleyEar c ∈ unitary (Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c)) :=
  pull_mem_unitary c (mulOp_mem_unitary cayleySymbol norm_cayleySymbol)

/-- [proved-standard; formal-checked] On the core, `U_c ((∂ − c + a) f) = (2πiξ + a) U_c f`. -/
theorem coeFn_mellinPlancherel_shifted (c : ℝ) (g : 𝓢(ℝ, ℂ)) (a : ℂ) :
    (mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g) : ℝ → ℂ)
      =ᵐ[volume] fun ξ => (2 * Real.pi * I * ξ + a) * mellinPlancherel c (core c g) ξ := by
  rw [map_add, map_sub, map_smul, map_smul]
  filter_upwards [coeFn_mellinPlancherel_scaleDeriv c g,
    Lp.coeFn_add (mellinPlancherel c (scaleDeriv c g) - (c : ℂ) • mellinPlancherel c (core c g))
      (a • mellinPlancherel c (core c g)),
    Lp.coeFn_sub (mellinPlancherel c (scaleDeriv c g)) ((c : ℂ) • mellinPlancherel c (core c g)),
    Lp.coeFn_smul (c : ℂ) (mellinPlancherel c (core c g)),
    Lp.coeFn_smul a (mellinPlancherel c (core c g))] with ξ h1 h2 h3 h4 h5
  rw [h2, Pi.add_apply, h3, Pi.sub_apply, h4, h5, Pi.smul_apply, Pi.smul_apply, h1, scaleSymbol,
    smul_eq_mul, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **On the core the Cayley operator is the Cayley transform
of `A = ∂ − c`**: `V (A + 1) f = (A − 1) f`. -/
theorem cayleyEar_core (c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    cayleyEar c (scaleDeriv c g - (c : ℂ) • core c g + core c g) =
      scaleDeriv c g - (c : ℂ) • core c g - core c g := by
  have e1 : scaleDeriv c g - (c : ℂ) • core c g + core c g =
      scaleDeriv c g - (c : ℂ) • core c g + (1 : ℂ) • core c g := by rw [one_smul]
  have e2 : scaleDeriv c g - (c : ℂ) • core c g - core c g =
      scaleDeriv c g - (c : ℂ) • core c g + (-1 : ℂ) • core c g := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [e1, e2]
  apply (mellinPlancherel c).injective
  rw [cayleyEar, mellinPlancherel_pull]
  ext1
  filter_upwards [coeFn_mulOp cayleySymbol
      (mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + (1 : ℂ) • core c g)),
    coeFn_mellinPlancherel_shifted c g 1, coeFn_mellinPlancherel_shifted c g (-1)] with ξ h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, cayleySymbol_mul]
  ring

/-! ## The ear on the whole line -/

/-- [proved-standard; formal-checked] The scale symbol is continuous in `ξ`. -/
theorem continuous_scaleSymbol (c : ℝ) : Continuous (scaleSymbol c) := by
  unfold scaleSymbol
  fun_prop

/-- [proved-derived; formal-checked] On `Re s = c` the flowed function is bounded by the mass of
Hearing's weight: `|heatE (−τ) ξ (c + 2πiξ)| ≤ ∫ |w_τ(u)| e^{cu} du`. -/
theorem norm_heatE_scaleSymbol_le (τ c ξ : ℝ) :
    ‖heatE (-τ) riemannXi (scaleSymbol c ξ)‖ ≤ ∫ u, ‖hearingWeight τ u * weight (-c) u‖ := by
  rw [← integral_hearingWeight]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [norm_mul]
  congr 1
  rw [Complex.norm_exp, weight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  rw [Complex.mul_re, re_scaleSymbol, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    neg_neg]

/-- [definition] **The ear's symbol on the line `Re s = c`**, `ξ ↦ heatE (−τ) ξ (c + 2πiξ)`, as
a bounded continuous function of `ξ`. -/
def earSymbol (τ c : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : ℝ => heatE (-τ) riemannXi (scaleSymbol c ξ))
    ((Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi (-τ)).continuous.comp
      (continuous_scaleSymbol c))
    (∫ u, ‖hearingWeight τ u * weight (-c) u‖) (norm_heatE_scaleSymbol_le τ c)

/-- [proved-standard; formal-checked] The ear's symbol at `ξ`. -/
theorem earSymbol_apply (τ c ξ : ℝ) :
    earSymbol τ c ξ = heatE (-τ) riemannXi (scaleSymbol c ξ) := rfl

/-- [definition] **The ear on the whole line**: the bounded operator on `L²(μ_c)` that the
Mellin–Plancherel unitary carries to multiplication by `heatE (−τ) ξ (c + 2πiξ)`. -/
def earOp (τ c : ℝ) : Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c) :=
  pull c (mulOp (earSymbol τ c))

/-- [proved-derived; formal-checked] **The whole-line ear is a normal operator.** -/
instance instIsStarNormalEarOp (τ c : ℝ) : IsStarNormal (earOp τ c) :=
  instIsStarNormalPull c (mulOp (earSymbol τ c))

/-- [proved-derived; formal-checked] The ear commutes with the Cayley unitary. -/
theorem earOp_comm_cayleyEar (τ c : ℝ) : earOp τ c * cayleyEar c = cayleyEar c * earOp τ c := by
  rw [earOp, cayleyEar, ← pull_mul, ← pull_mul, ← mulOp_mul, ← mulOp_mul, mul_comm]

/-- [proved-derived; formal-checked] `U_c (earOp f) = heatE (−τ) ξ (c + 2πiξ) · U_c f`. -/
theorem coeFn_mellinPlancherel_earOp (τ c : ℝ) (f : Lp ℂ 2 (lineMeasure c)) :
    (mellinPlancherel c (earOp τ c f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => heatE (-τ) riemannXi (scaleSymbol c ξ) * mellinPlancherel c f ξ := by
  rw [earOp, mellinPlancherel_pull]
  exact coeFn_mulOp (earSymbol τ c) (mellinPlancherel c f)

/-- [proved-derived; formal-checked] **The whole-line ear is Hearing's averaged shift** wherever
that average lies in `L²(μ_c)`: for `f ∈ L²(μ_c)` with `W_c f ∈ L¹`,
`earOp f = ∫ w_τ(u) f(· + u) du`. -/
theorem earOp_eq_average (τ c : ℝ) {f : ℝ → ℂ} (hf2 : MemLp f 2 (lineMeasure c))
    (hf : Integrable (fun x => weight c x * f x))
    (hA : MemLp (fun x => ∫ u, hearingWeight τ u * f (x + u)) 2 (lineMeasure c)) :
    earOp τ c (hf2.toLp f) = hA.toLp _ := by
  apply (mellinPlancherel c).injective
  ext1
  filter_upwards [coeFn_mellinPlancherel_earOp τ c (hf2.toLp f),
    coeFn_mellinPlancherel_average c (integrable_hearingWeight τ c) hf2 hf hA] with ξ h1 h2
  rw [h1, h2, integral_hearingWeight]

/-! ## The whole-line ear is never invertible -/

/-- [proved-derived; formal-checked] The ear's symbol is a Fourier transform:
`heatE (−τ) ξ (c + 2πiξ) = 𝓕 (w_τ(u) e^{cu}) (−ξ)`. -/
theorem earSymbol_eq_fourier (τ c ξ : ℝ) :
    earSymbol τ c ξ = 𝓕 (fun u => hearingWeight τ u * weight (-c) u) (-ξ) := by
  rw [earSymbol_apply, ← integral_hearingWeight, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [smul_eq_mul, weight, scaleSymbol, Complex.ofReal_exp]
  have h : cexp (((c : ℂ) + 2 * Real.pi * I * ξ) * u) =
      cexp (((-2 * Real.pi * u * -ξ : ℝ) : ℂ) * I) * cexp ((-(-c) * u : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  ring

/-- [proved-derived; formal-checked] **Riemann–Lebesgue for the ear**: its symbol tends to `0`
as `|ξ| → ∞` on every line `Re s = c`. -/
theorem tendsto_earSymbol (τ c : ℝ) : Tendsto (earSymbol τ c) (cocompact ℝ) (𝓝 0) := by
  have h := Real.zero_at_infty_fourier (fun u => hearingWeight τ u * weight (-c) u)
  have hneg : Tendsto (fun ξ : ℝ => -ξ) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.neg ℝ).map_cocompact.le
  refine (h.comp hneg).congr fun ξ => ?_
  exact (earSymbol_eq_fourier τ c ξ).symm

/-- [proved-derived; formal-checked] **The whole-line ear is never invertible**, at any time `τ`
and any abscissa `c`, whether or not the flowed function has a zero on the line. -/
theorem not_isUnit_earOp (τ c : ℝ) : ¬ IsUnit (earOp τ c) := by
  rw [earOp, isUnit_pull_iff]
  exact not_isUnit_mulOp_of_tendsto_zero _ (tendsto_earSymbol τ c)

/-- [proved-standard; formal-checked] The Cayley unitary is invertible, so `not_isUnit_earOp`
is a property of the ear's symbol and not of every operator of this algebra. -/
theorem isUnit_cayleyEar (c : ℝ) : IsUnit (cayleyEar c) := by
  rw [cayleyEar, isUnit_pull_iff, isUnit_mulOp_iff]
  exact ⟨1, one_pos, fun ξ => (norm_cayleySymbol ξ).ge⟩

/-! ## Side by side with the truncations -/

/-- [proved-derived; formal-checked] **Side by side**: at every `τ` and `c` the whole-line ear
is not a unit, while the truncations of `Hearing` are all invertible if and only if the flowed
function has no zero on `Re s = c`, which holds if and only if the whole-line symbol vanishes
nowhere. The truncations are Hearing's coordinate model; they are not derived from `earOp`. -/
theorem wholeLine_not_isUnit_and_truncations_criterion (τ c : ℝ) :
    ¬ IsUnit (earOp τ c) ∧
      (Holonics.Zeta.Hearing.QuasiInvertible (heatE (-τ) riemannXi) c ↔
        Holonics.Zeta.Hearing.VerticalZeroFree τ c) ∧
      (Holonics.Zeta.Hearing.VerticalZeroFree τ c ↔ ∀ ξ : ℝ, earSymbol τ c ξ ≠ 0) :=
  ⟨not_isUnit_earOp τ c,
    Holonics.Zeta.Hearing.quasiInvertible_iff_verticalZeroFree
      (Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi (-τ)).continuous c,
    verticalZeroFree_iff_multiplier_ne_zero τ c⟩

/-! ## The spectrum and the functional calculus of a multiplication operator -/

/-- [proved-standard; formal-checked] The symbol `0` gives the operator `0`. -/
theorem mulOp_zero : mulOp 0 = 0 := by
  have h := mulOp_smul 0 (0 : ℝ →ᵇ ℂ)
  simpa using h

/-- [proved-standard; formal-checked] `mulOp` respects differences of symbols. -/
theorem mulOp_sub (m₁ m₂ : ℝ →ᵇ ℂ) : mulOp (m₁ - m₂) = mulOp m₁ - mulOp m₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ m₂, mulOp_add, mulOp_smul, neg_one_smul, ← sub_eq_add_neg]

/-- [proved-standard; formal-checked] `r − mulOp m` is multiplication by `r − m`. -/
theorem algebraMap_sub_mulOp (m : ℝ →ᵇ ℂ) (r : ℂ) :
    algebraMap ℂ (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) r - mulOp m =
      mulOp (r • (1 : ℝ →ᵇ ℂ) - m) := by
  rw [mulOp_sub, mulOp_smul, mulOp_one, Algebra.algebraMap_eq_smul_one]

/-- [proved-standard; formal-checked] Every value of the symbol lies in the spectrum. -/
theorem mem_spectrum_mulOp (m : ℝ →ᵇ ℂ) (ξ₀ : ℝ) : m ξ₀ ∈ spectrum ℂ (mulOp m) := by
  rw [spectrum.mem_iff, algebraMap_sub_mulOp, isUnit_mulOp_iff]
  rintro ⟨δ, hδ, h⟩
  have := h ξ₀
  simp at this
  linarith

/-- [proved-standard; formal-checked] **The symbol map is isometric**: `‖mulOp m‖ = ‖m‖`, since
every value of the symbol is a spectral value. -/
theorem norm_mulOp (m : ℝ →ᵇ ℂ) : ‖mulOp m‖ = ‖m‖ := by
  refine le_antisymm (norm_mulOp_le m) ?_
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun ξ => ?_
  have h := spectrum.norm_le_norm_mul_of_mem (mem_spectrum_mulOp m ξ)
  have h1 : ‖(1 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  calc ‖m ξ‖
      ≤ ‖mulOp m‖ * ‖(1 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))‖ := h
    _ ≤ ‖mulOp m‖ * 1 := by gcongr
    _ = ‖mulOp m‖ := mul_one _

/-- [proved-standard; formal-checked] **The spectrum of a multiplication operator is the closure
of the range of its symbol.** -/
theorem spectrum_mulOp (m : ℝ →ᵇ ℂ) : spectrum ℂ (mulOp m) = closure (range m) := by
  apply Subset.antisymm
  · intro r hr
    by_contra hcl
    rw [Metric.mem_closure_iff] at hcl
    push Not at hcl
    obtain ⟨δ, hδ, hfar⟩ := hcl
    rw [spectrum.mem_iff, algebraMap_sub_mulOp, isUnit_mulOp_iff] at hr
    refine hr ⟨δ, hδ, fun ξ => ?_⟩
    have := hfar (m ξ) (mem_range_self ξ)
    simpa [dist_eq_norm] using this
  · exact closure_minimal (range_subset_iff.2 (mem_spectrum_mulOp m)) (spectrum.isClosed _)

/-- [definition] The composite symbol `g ∘ m`, for `g` continuous on the spectrum of `mulOp m`. -/
def specSymbol (m : ℝ →ᵇ ℂ) (g : C(spectrum ℂ (mulOp m), ℂ)) : ℝ →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact g).compContinuous
    ⟨fun ξ => ⟨m ξ, mem_spectrum_mulOp m ξ⟩, m.continuous.subtype_mk _⟩

/-- [proved-standard; formal-checked] `‖g ∘ m‖ ≤ ‖g‖`. -/
theorem norm_specSymbol_le (m : ℝ →ᵇ ℂ) (g : C(spectrum ℂ (mulOp m), ℂ)) :
    ‖specSymbol m g‖ ≤ ‖g‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun _ => g.norm_coe_le_norm _

/-- [definition] The `⋆`-algebra map `g ↦ mulOp (g ∘ m)` from the continuous functions on the
spectrum of `mulOp m` to the operators on `L²(dξ)`. -/
def specHom (m : ℝ →ᵇ ℂ) : C(spectrum ℂ (mulOp m), ℂ) →⋆ₐ[ℂ]
    (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) where
  toFun g := mulOp (specSymbol m g)
  map_one' := by
    rw [show specSymbol m 1 = 1 from BoundedContinuousFunction.ext fun _ => rfl, mulOp_one]
  map_mul' g₁ g₂ := by
    rw [show specSymbol m (g₁ * g₂) = specSymbol m g₁ * specSymbol m g₂ from
      BoundedContinuousFunction.ext fun _ => rfl, mulOp_mul]
  map_zero' := by
    rw [show specSymbol m 0 = 0 from BoundedContinuousFunction.ext fun _ => rfl, mulOp_zero]
  map_add' g₁ g₂ := by
    rw [show specSymbol m (g₁ + g₂) = specSymbol m g₁ + specSymbol m g₂ from
      BoundedContinuousFunction.ext fun _ => rfl, mulOp_add]
  commutes' r := by
    rw [show specSymbol m (algebraMap ℂ _ r) = r • (1 : ℝ →ᵇ ℂ) from
      BoundedContinuousFunction.ext fun _ => by simp [specSymbol], mulOp_smul, mulOp_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    rw [show specSymbol m (star g) = star (specSymbol m g) from
      BoundedContinuousFunction.ext fun _ => rfl, mulOp_star]

/-- [proved-standard; formal-checked] `specHom m` is continuous. -/
theorem continuous_specHom (m : ℝ →ᵇ ℂ) : Continuous (specHom m) :=
  AddMonoidHomClass.continuous_of_bound (specHom m) 1 fun g => by
    rw [one_mul]
    exact (norm_mulOp_le _).trans (norm_specSymbol_le m g)

/-- [proved-standard; formal-checked] **The continuous functional calculus of a multiplication
operator is multiplication by the composite symbol**: for `f` continuous on the spectrum of
`mulOp m` and `n = f ∘ m`, `cfc f (mulOp m) = mulOp n`. -/
theorem cfc_mulOp (m n : ℝ →ᵇ ℂ) (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (mulOp m)))
    (hn : ∀ ξ, n ξ = f (m ξ)) : cfc f (mulOp m) = mulOp n := by
  have hid : specHom m (.restrict (spectrum ℂ (mulOp m)) (.id ℂ)) = mulOp m := by
    change mulOp (specSymbol m _) = mulOp m
    congr 1
  have key := cfcHom_eq_of_continuous_of_map_id (instIsStarNormalMulOp m) (specHom m)
    (continuous_specHom m) hid
  rw [cfc_apply f (mulOp m), key]
  change mulOp (specSymbol m _) = mulOp n
  congr 1
  ext ξ
  exact (hn ξ).symm

/-! ## The ear is the functional calculus of the Cayley unitary -/

/-- [definition] The ear's symbol read on the unit circle through the inverse Cayley map
`w ↦ (1 + w)/(1 − w)`, with the value `0` at `w = 1`, the image of `ξ = ∞`. -/
def earCircle (τ c : ℝ) (w : ℂ) : ℂ :=
  if w = 1 then 0 else heatE (-τ) riemannXi (c + (1 + w) / (1 - w))

/-- [proved-standard; formal-checked] `earCircle` at `w = 1`. -/
theorem earCircle_one (τ c : ℝ) : earCircle τ c 1 = 0 := if_pos rfl

/-- [definition] The inverse Cayley coordinate of a point of the circle: the real `ξ` with
`2πiξ = (1 + w)/(1 − w)`. -/
def cayleyCoord (w : ℂ) : ℝ := ((1 + w) / (1 - w)).im / (2 * Real.pi)

/-- [proved-standard; formal-checked] On the unit circle `(1 + w)/(1 − w)` is purely imaginary,
equal to `2πi · cayleyCoord w`. -/
theorem two_pi_I_mul_cayleyCoord {w : ℂ} (hw : ‖w‖ = 1) :
    2 * Real.pi * I * (cayleyCoord w : ℂ) = (1 + w) / (1 - w) := by
  have hre : ((1 + w) / (1 - w)).re = 0 := by
    rw [Complex.div_re, ← add_div]
    have hn : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hw, one_pow]
    have h0 : (1 + w).re * (1 - w).re + (1 + w).im * (1 - w).im = 0 := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im, Complex.sub_im,
        Complex.one_im, zero_add, zero_sub]
      nlinarith
    rw [h0, zero_div]
  have hz : (1 + w) / (1 - w) = ((((1 + w) / (1 - w)).im : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im ((1 + w) / (1 - w)), hre]
    simp
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [cayleyCoord]
  conv_rhs => rw [hz]
  push_cast
  field_simp

/-- [proved-standard; formal-checked] The Cayley symbol at the inverse coordinate of `w` is `w`,
for `w ≠ 1` on the circle. -/
theorem cayleySymbol_cayleyCoord {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) :
    cayleySymbol (cayleyCoord w) = w := by
  have h1' : (1 - w) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hden := cayleyDen_ne_zero (cayleyCoord w)
  rw [two_pi_I_mul_cayleyCoord hw] at hden
  rw [cayleySymbol_apply, two_pi_I_mul_cayleyCoord hw, div_eq_iff hden]
  field_simp
  ring

/-- [proved-derived; formal-checked] On the circle away from `1`, `earCircle` is the ear's symbol
at the inverse Cayley coordinate. -/
theorem earCircle_eq_earSymbol (τ c : ℝ) {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) :
    earCircle τ c w = earSymbol τ c (cayleyCoord w) := by
  rw [earCircle, if_neg h1, earSymbol_apply, scaleSymbol, two_pi_I_mul_cayleyCoord hw]

/-- [proved-derived; formal-checked] `earCircle` composed with the Cayley symbol is the ear's
symbol. -/
theorem earCircle_cayleySymbol (τ c ξ : ℝ) :
    earCircle τ c (cayleySymbol ξ) = earSymbol τ c ξ := by
  rw [earCircle, if_neg (cayleySymbol_ne_one ξ), earSymbol_apply, scaleSymbol]
  congr 2
  have hden := cayleyDen_ne_zero ξ
  rw [div_eq_iff (sub_ne_zero.2 (Ne.symm (cayleySymbol_ne_one ξ))), cayleySymbol_apply]
  field_simp
  ring

/-- [proved-derived; formal-checked] **`earCircle` is continuous on the unit circle.** Away from
`1` it is a composite of continuous maps; at `1` its limit `0` is Riemann–Lebesgue
(`tendsto_earSymbol`), because the points of the circle near `1` have inverse Cayley coordinate
outside any compact set. -/
theorem continuousOn_earCircle (τ c : ℝ) :
    ContinuousOn (earCircle τ c) (Metric.sphere (0 : ℂ) 1) := by
  intro w hw
  by_cases h1 : w = 1
  · subst h1
    rw [ContinuousWithinAt, earCircle_one, Metric.tendsto_nhds]
    intro ε hε
    have hev : ∀ᶠ ξ in cocompact ℝ, dist (earSymbol τ c ξ) 0 < ε :=
      Metric.tendsto_nhds.1 (tendsto_earSymbol τ c) ε hε
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hev
    have hclosed : IsClosed (cayleySymbol '' K) := (hK.image cayleySymbol.continuous).isClosed
    have h1notin : (1 : ℂ) ∉ cayleySymbol '' K := by
      rintro ⟨ξ, -, hξ⟩
      exact cayleySymbol_ne_one ξ hξ
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hclosed.isOpen_compl.mem_nhds h1notin),
      self_mem_nhdsWithin] with v hvK hvS
    by_cases hv1 : v = 1
    · rw [hv1, earCircle_one, dist_self]
      exact hε
    · have hvn : ‖v‖ = 1 := by simpa using hvS
      rw [earCircle_eq_earSymbol τ c hvn hv1]
      exact hKs fun hmem => hvK ⟨_, hmem, cayleySymbol_cayleyCoord hvn hv1⟩
  · refine ContinuousAt.continuousWithinAt ?_
    have hev : (fun v : ℂ => heatE (-τ) riemannXi (c + (1 + v) / (1 - v))) =ᶠ[𝓝 w]
        earCircle τ c := by
      filter_upwards [isOpen_ne.mem_nhds h1] with v hv
      rw [earCircle, if_neg hv]
    have hinner : ContinuousAt (fun v : ℂ => (c : ℂ) + (1 + v) / (1 - v)) w :=
      continuousAt_const.add ((continuousAt_const.add continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm h1)))
    exact (((Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi
      (-τ)).continuous.continuousAt).comp hinner).congr hev

/-- [proved-derived; formal-checked] **The whole-line ear is the continuous functional calculus
of the Cayley unitary**: `earOp τ c = cfc (earCircle τ c) (cayleyEar c)`. -/
theorem earOp_eq_cfc (τ c : ℝ) : earOp τ c = cfc (earCircle τ c) (cayleyEar c) := by
  have hsub : spectrum ℂ (mulOp cayleySymbol) ⊆ Metric.sphere (0 : ℂ) 1 :=
    spectrum.subset_circle_of_unitary (mulOp_mem_unitary cayleySymbol norm_cayleySymbol)
  have hf : ContinuousOn (earCircle τ c) (spectrum ℂ (mulOp cayleySymbol)) :=
    (continuousOn_earCircle τ c).mono hsub
  have h1 : cfc (earCircle τ c) (mulOp cayleySymbol) = mulOp (earSymbol τ c) :=
    cfc_mulOp cayleySymbol (earSymbol τ c) (earCircle τ c) hf
      fun ξ => (earCircle_cayleySymbol τ c ξ).symm
  rw [earOp, cayleyEar, ← h1]
  exact StarAlgHomClass.map_cfc (pull c) (earCircle τ c) (mulOp cayleySymbol) hf (continuous_pull c)

/-! ## The spectra of the Cayley unitary and of the ear -/

/-- [proved-standard; formal-checked] Conjugation by the unitary keeps the spectrum. -/
theorem spectrum_pull (c : ℝ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    spectrum ℂ (pull c T) = spectrum ℂ T :=
  AlgEquiv.spectrum_eq (pull c) T

/-- [proved-standard; formal-checked] `1` is a limit of values of the Cayley symbol: at
`ξ = 1/ε`, `|1 − V(ξ)| = 2/|2πiξ + 1| ≤ ε/π`. -/
theorem one_mem_closure_range_cayleySymbol : (1 : ℂ) ∈ closure (range cayleySymbol) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨cayleySymbol (1 / ε), mem_range_self _, ?_⟩
  have hden := cayleyDen_ne_zero (1 / ε)
  have e : (1 : ℂ) - cayleySymbol (1 / ε) = 2 / (2 * Real.pi * I * ((1 / ε : ℝ) : ℂ) + 1) := by
    rw [cayleySymbol_apply]
    field_simp
    ring
  have him : 2 * Real.pi * (1 / ε) ≤ ‖(2 * Real.pi * I * ((1 / ε : ℝ) : ℂ) + 1 : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (2 * Real.pi * I * ((1 / ε : ℝ) : ℂ) + 1 : ℂ)
    have him' : (2 * Real.pi * I * ((1 / ε : ℝ) : ℂ) + 1 : ℂ).im = 2 * Real.pi * (1 / ε) := by
      simp
    rw [him'] at h
    exact (le_abs_self _).trans h
  have hpos : 0 < 2 * Real.pi * (1 / ε) := by positivity
  rw [dist_eq_norm, e, norm_div, Complex.norm_ofNat]
  calc 2 / ‖(2 * Real.pi * I * ((1 / ε : ℝ) : ℂ) + 1 : ℂ)‖
      ≤ 2 / (2 * Real.pi * (1 / ε)) := div_le_div_of_nonneg_left (by norm_num) hpos him
    _ = ε / Real.pi := by field_simp
    _ < ε := div_lt_self hε (by linarith [Real.pi_gt_three])

/-- [proved-standard; formal-checked] **The spectrum of the Cayley multiplier is the whole unit
circle**: every `w ≠ 1` of the circle is a value of the symbol, and `1` is a limit of values. -/
theorem spectrum_mulOp_cayleySymbol :
    spectrum ℂ (mulOp cayleySymbol) = Metric.sphere (0 : ℂ) 1 := by
  apply Subset.antisymm
    (spectrum.subset_circle_of_unitary (mulOp_mem_unitary cayleySymbol norm_cayleySymbol))
  intro w hw
  rw [spectrum_mulOp]
  by_cases h1 : w = 1
  · rw [h1]
    exact one_mem_closure_range_cayleySymbol
  · exact subset_closure ⟨cayleyCoord w, cayleySymbol_cayleyCoord (by simpa using hw) h1⟩

/-- [proved-derived; formal-checked] **The spectrum of the Cayley unitary of `∂_c − c` is the
whole unit circle**, the Cayley image of the line `c + iℝ` together with the point `1`. -/
theorem spectrum_cayleyEar (c : ℝ) : spectrum ℂ (cayleyEar c) = Metric.sphere (0 : ℂ) 1 := by
  rw [cayleyEar, spectrum_pull, spectrum_mulOp_cayleySymbol]

/-- [proved-derived; formal-checked] **`1` is not an eigenvalue of the Cayley unitary**: its only
fixed vector is `0`, although `1` lies in its spectrum (`spectrum_cayleyEar`). -/
theorem cayleyEar_apply_eq_self_iff (c : ℝ) (f : Lp ℂ 2 (lineMeasure c)) :
    cayleyEar c f = f ↔ f = 0 := by
  constructor
  · intro hf
    have hg : mulOp cayleySymbol (mellinPlancherel c f) = mellinPlancherel c f := by
      rw [← mellinPlancherel_pull, ← cayleyEar, hf]
    have h0 : mellinPlancherel c f = 0 := by
      ext1
      filter_upwards [coeFn_mulOp cayleySymbol (mellinPlancherel c f),
        Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with ξ h1 h2
      rw [hg] at h1
      have h3 : (cayleySymbol ξ - 1) * mellinPlancherel c f ξ = 0 := by
        rw [sub_mul, one_mul, ← h1, sub_self]
      rw [h2, Pi.zero_apply]
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (cayleySymbol_ne_one ξ))
    exact (map_eq_zero_iff _ (mellinPlancherel c).injective).1 h0
  · rintro rfl
    rw [map_zero]

/-- [proved-derived; formal-checked] **The spectrum of the whole-line ear** is the closure of the
values of the flowed function on the line `Re s = c`. -/
theorem spectrum_earOp (τ c : ℝ) :
    spectrum ℂ (earOp τ c) = closure (range (earSymbol τ c)) := by
  rw [earOp, spectrum_pull, spectrum_mulOp]

/-- [proved-derived; formal-checked] `0` lies in the spectrum of the whole-line ear at every
`τ` and `c`. -/
theorem zero_mem_spectrum_earOp (τ c : ℝ) : (0 : ℂ) ∈ spectrum ℂ (earOp τ c) := by
  rw [spectrum.zero_mem_iff]
  exact not_isUnit_earOp τ c

/-! ## The core determines the Cayley unitary -/

/-- [proved-standard; formal-checked] `2πiξ + a ≠ 0` for `a` off the imaginary axis. -/
theorem two_pi_I_mul_add_ne_zero {a : ℂ} (ha : a.re ≠ 0) (ξ : ℝ) :
    (2 * Real.pi * I * ξ + a : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  exact ha h'

/-- [proved-standard; formal-checked] For a smooth compactly supported `ψ` and `a` off the
imaginary axis there is a Schwartz `g` with `(2πiξ + a) 𝓕 g = ψ`: `g` is the inverse Fourier
transform of `ψ/(2πiξ + a)`, which is again smooth and compactly supported. -/
theorem exists_schwartz_fourier_mul_eq {ψ : ℝ → ℂ} (hψ₁ : HasCompactSupport ψ)
    (hψ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {a : ℂ} (ha : a.re ≠ 0) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ ξ : ℝ, (2 * Real.pi * I * ξ + a) * 𝓕 (g : ℝ → ℂ) ξ = ψ ξ := by
  have hφ₁ : HasCompactSupport (fun ξ : ℝ => ψ ξ * (2 * Real.pi * I * ξ + a : ℂ)⁻¹) :=
    hψ₁.mono fun ξ hξ => left_ne_zero_of_mul hξ
  have hofReal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => (ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => (2 * Real.pi * I * ξ + a : ℂ)) :=
    (contDiff_const.mul hofReal).add contDiff_const
  have hφ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : ℝ => ψ ξ * (2 * Real.pi * I * ξ + a : ℂ)⁻¹) :=
    hψ₂.mul (hden.inv (two_pi_I_mul_add_ne_zero ha))
  refine ⟨𝓕⁻ (hφ₁.toSchwartzMap hφ₂), fun ξ => ?_⟩
  have hcoe : (hφ₁.toSchwartzMap hφ₂) ξ = ψ ξ * (2 * Real.pi * I * ξ + a : ℂ)⁻¹ := rfl
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq, hcoe, mul_left_comm,
    mul_inv_cancel₀ (two_pi_I_mul_add_ne_zero ha ξ), mul_one]

/-- [proved-derived; formal-checked] On the Mellin side the range of `A + a` on the core is
dense, `A = ∂ − c` and `a` off the imaginary axis: it holds every smooth compactly supported
function. -/
theorem denseRange_mellinPlancherel_scaleDeriv_sub_add (c : ℝ) {a : ℂ} (ha : a.re ≠ 0) :
    DenseRange (fun g : 𝓢(ℝ, ℂ) =>
      mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g)) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨ψ, hψ₁, hψ₂, hψ₃⟩ := MemLp.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top
    one_le_two (Lp.memLp f) hε
  obtain ⟨g, hg⟩ := exists_schwartz_fourier_mul_eq hψ₁ hψ₂ ha
  have hae : (mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g) : ℝ → ℂ)
      =ᵐ[volume] ψ := by
    filter_upwards [coeFn_mellinPlancherel_shifted c g a, coeFn_mellinPlancherel_core c g]
      with ξ h1 h2
    rw [h1, h2, hg]
  have hsub : (f : ℝ → ℂ) -
      (mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g) : ℝ → ℂ)
        =ᵐ[volume] (f : ℝ → ℂ) - ψ := by
    filter_upwards [hae] with ξ hξ
    rw [Pi.sub_apply, Pi.sub_apply, hξ]
  refine ⟨mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g), ⟨g, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall', Lp.dist_def, eLpNorm_congr_ae hsub]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hψ₃

/-- [proved-derived; formal-checked] **`A + a` has dense range on the core** for every `a` off
the imaginary axis, `A = ∂ − c`. -/
theorem denseRange_scaleDeriv_sub_add (c : ℝ) {a : ℂ} (ha : a.re ≠ 0) :
    DenseRange (fun g : 𝓢(ℝ, ℂ) => scaleDeriv c g - (c : ℂ) • core c g + a • core c g) := by
  have h := (mellinPlancherel c).symm.surjective.denseRange.comp
    (denseRange_mellinPlancherel_scaleDeriv_sub_add c ha) (mellinPlancherel c).symm.continuous
  have key : ((mellinPlancherel c).symm ∘ fun g : 𝓢(ℝ, ℂ) =>
      mellinPlancherel c (scaleDeriv c g - (c : ℂ) • core c g + a • core c g)) =
      fun g : 𝓢(ℝ, ℂ) => scaleDeriv c g - (c : ℂ) • core c g + a • core c g :=
    funext fun g => by rw [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [key] at h
  exact h

/-- [proved-derived; formal-checked] `A + 1` has dense range on the core: the domain of the
Cayley transform is dense. -/
theorem denseRange_cayleyDomain (c : ℝ) :
    DenseRange (fun g : 𝓢(ℝ, ℂ) => scaleDeriv c g - (c : ℂ) • core c g + core c g) := by
  have h := denseRange_scaleDeriv_sub_add c (a := 1) (by simp)
  simpa only [one_smul] using h

/-- [proved-derived; formal-checked] `A − 1` has dense range on the core: the range of the
Cayley transform is dense. -/
theorem denseRange_cayleyRange (c : ℝ) :
    DenseRange (fun g : 𝓢(ℝ, ℂ) => scaleDeriv c g - (c : ℂ) • core c g - core c g) := by
  have h := denseRange_scaleDeriv_sub_add c (a := -1) (by simp)
  simpa only [neg_one_smul, ← sub_eq_add_neg] using h

/-- [proved-derived; formal-checked] **The core determines the Cayley unitary**: a bounded
operator `W` with `W (A + 1) f = (A − 1) f` on the core is `cayleyEar c`. -/
theorem eq_cayleyEar_of_core (c : ℝ) (W : Lp ℂ 2 (lineMeasure c) →L[ℂ] Lp ℂ 2 (lineMeasure c))
    (hW : ∀ g : 𝓢(ℝ, ℂ), W (scaleDeriv c g - (c : ℂ) • core c g + core c g) =
      scaleDeriv c g - (c : ℂ) • core c g - core c g) :
    W = cayleyEar c := by
  refine DFunLike.coe_injective ((denseRange_cayleyDomain c).equalizer W.continuous
    (cayleyEar c).continuous (funext fun g => ?_))
  simp only [Function.comp_apply]
  rw [hW, cayleyEar_core]

end Holonics.Zeta.CayleyEar

#print axioms Holonics.Zeta.CayleyEar.isUnit_mulOp_iff
#print axioms Holonics.Zeta.CayleyEar.cayleyEar_core
#print axioms Holonics.Zeta.CayleyEar.earOp_eq_average
#print axioms Holonics.Zeta.CayleyEar.not_isUnit_earOp
#print axioms Holonics.Zeta.CayleyEar.wholeLine_not_isUnit_and_truncations_criterion
#print axioms Holonics.Zeta.CayleyEar.earOp_eq_cfc
#print axioms Holonics.Zeta.CayleyEar.spectrum_cayleyEar
#print axioms Holonics.Zeta.CayleyEar.eq_cayleyEar_of_core
