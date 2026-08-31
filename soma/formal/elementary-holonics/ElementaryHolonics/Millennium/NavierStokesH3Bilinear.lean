import ElementaryHolonics.Millennium.NavierStokesMildFourierNonlinearity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The `H³` lattice aperture for the periodic Navier--Stokes bilinear term

This owner begins at the complete integer frequency population.  It proves summability of the
true reciprocal third-order Sobolev weight and uses Fourier Cauchy--Schwarz to return the
absolute coefficient population required by the predecessor's infinite convolution.

The subsequent target is the weighted convolution `H³ × H³ → H²`, expressed in divergence form
so that the output derivative is carried by the receiver frequency.  No finite cutoff,
local-existence premise, or fixed-point conclusion is introduced.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal lp
open Filter

namespace Soma.Holonics.Millennium.NavierStokesH3Bilinear

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity

/-! ## The genuine reciprocal lattice sum -/

/-- [definition] Expose the three integer coordinates without losing their address. -/
def frequencyTripleEquiv : SpatialFrequency ≃ (ℤ × ℤ) × ℤ where
  toFun k := ((k 0, k 1), k 2)
  invFun k := ![k.1.1, k.1.2, k.2]
  left_inv k := by
    funext coordinate
    fin_cases coordinate <;> rfl
  right_inv k := by
    rcases k with ⟨⟨k₀, k₁⟩, k₂⟩
    rfl

/-- [definition] A separable summable receiver dominating the reciprocal `H³` weight. -/
def separableReciprocalWeight (k : SpatialFrequency) : ℝ :=
  (1 + (k 0 : ℝ) ^ 2)⁻¹ *
    (1 + (k 1 : ℝ) ^ 2)⁻¹ *
      (1 + (k 2 : ℝ) ^ 2)⁻¹

/-- [proved-derived] The reciprocal quadratic population is summable on the complete integer
line, with its zero occurrence handled explicitly. -/
theorem summable_one_add_int_sq_inv :
    Summable fun n : ℤ ↦ (1 + (n : ℝ) ^ 2)⁻¹ := by
  have hpSeries : Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ 2 :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  let bound : ℤ → ℝ := fun n ↦ if n = 0 then 1 else 1 / (n : ℝ) ^ 2
  have hbound : Summable bound := by
    apply hpSeries.congr_cofinite
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [bound, hn]
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hbound
  by_cases hn : n = 0
  · subst n
    simp [bound]
  · rw [show bound n = ((n : ℝ) ^ 2)⁻¹ by simp [bound, hn, one_div]]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (le_add_of_nonneg_left zero_le_one)

private theorem summable_pair_separable :
    Summable fun k : ℤ × ℤ ↦
      (1 + (k.1 : ℝ) ^ 2)⁻¹ * (1 + (k.2 : ℝ) ^ 2)⁻¹ := by
  let oneDimensional : ℤ → ℝ := fun n ↦ (1 + (n : ℝ) ^ 2)⁻¹
  have hone : Summable oneDimensional := summable_one_add_int_sq_inv
  refine (summable_prod_of_nonneg (fun _ ↦ mul_nonneg (by positivity) (by positivity))).mpr ?_
  refine ⟨fun first ↦ hone.mul_left (oneDimensional first), ?_⟩
  have houter : Summable fun first ↦
      oneDimensional first * (∑' second, oneDimensional second) :=
    hone.mul_right (∑' second, oneDimensional second)
  simpa only [oneDimensional, hone.tsum_mul_left] using houter

private theorem summable_triple_separable :
    Summable fun k : (ℤ × ℤ) × ℤ ↦
      ((1 + (k.1.1 : ℝ) ^ 2)⁻¹ * (1 + (k.1.2 : ℝ) ^ 2)⁻¹) *
        (1 + (k.2 : ℝ) ^ 2)⁻¹ := by
  let pairWeight : ℤ × ℤ → ℝ := fun k ↦
    (1 + (k.1 : ℝ) ^ 2)⁻¹ * (1 + (k.2 : ℝ) ^ 2)⁻¹
  let oneDimensional : ℤ → ℝ := fun n ↦ (1 + (n : ℝ) ^ 2)⁻¹
  have hpair : Summable pairWeight := summable_pair_separable
  have hone : Summable oneDimensional := summable_one_add_int_sq_inv
  refine (summable_prod_of_nonneg (fun _ ↦ mul_nonneg (by positivity) (by positivity))).mpr ?_
  refine ⟨fun pair ↦ hone.mul_left (pairWeight pair), ?_⟩
  have houter : Summable fun pair ↦
      pairWeight pair * (∑' coordinate, oneDimensional coordinate) :=
    hpair.mul_right (∑' coordinate, oneDimensional coordinate)
  simpa only [pairWeight, oneDimensional, hone.tsum_mul_left] using houter

/-- [proved-derived] The complete separable reciprocal population is summable on `ℤ³`. -/
theorem summable_separableReciprocalWeight :
    Summable separableReciprocalWeight := by
  have htranslated := frequencyTripleEquiv.summable_iff.mpr summable_triple_separable
  refine htranslated.congr ?_
  intro k
  rfl

/-- [proved-derived] The true reciprocal periodic `H³` weight is pointwise dominated by the
separable population. -/
theorem periodicSobolevWeight_three_inv_le_separable
    (k : SpatialFrequency) :
    (periodicSobolevWeight 3 k)⁻¹ ≤ separableReciprocalWeight k := by
  have hfrequency : 0 ≤ frequencySquared k := by
    unfold frequencySquared
    positivity
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hfrequencyEigen : frequencySquared k ≤ torusStokesEigenvalue k := by
    rw [torusStokesEigenvalue]
    exact le_mul_of_one_le_left hfrequency hscale
  have hcoordinate (coordinate : Fin 3) :
      (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ)) (Finset.mem_univ coordinate)
  let total : ℝ := 1 + torusStokesEigenvalue k
  have htotal : 0 < total := by
    dsimp [total]
    linarith [torusStokesEigenvalue_nonneg k]
  have hfactor_le (coordinate : Fin 3) :
      1 + (k coordinate : ℝ) ^ 2 ≤ total := by
    dsimp [total]
    linarith [hcoordinate coordinate, hfrequencyEigen]
  have hproduct :
      (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) * (1 + (k 2 : ℝ) ^ 2) ≤
        total ^ 3 := by
    calc
      (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) * (1 + (k 2 : ℝ) ^ 2) ≤
          total * total * total := by
        gcongr
        · exact hfactor_le 0
        · exact hfactor_le 1
        · exact hfactor_le 2
      _ = total ^ 3 := by ring
  have hproductPos :
      0 < (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) *
        (1 + (k 2 : ℝ) ^ 2) := by positivity
  rw [periodicSobolevWeight]
  change (total ^ 3)⁻¹ ≤ separableReciprocalWeight k
  rw [separableReciprocalWeight, ← mul_inv, ← mul_inv]
  exact (inv_le_inv₀ (pow_pos htotal 3) hproductPos).mpr hproduct

/-- [proved-derived] The exact reciprocal `H³` weight is summable over every integer frequency. -/
theorem summable_periodicSobolevWeight_three_inv :
    Summable fun k : SpatialFrequency ↦ (periodicSobolevWeight 3 k)⁻¹ := by
  refine Summable.of_nonneg_of_le
    (fun k ↦ inv_nonneg.mpr (periodicSobolevWeight_nonneg 3 k))
    (fun k ↦ periodicSobolevWeight_three_inv_le_separable k)
    summable_separableReciprocalWeight

/-! ## Fourier Cauchy--Schwarz and the `H³ → ℓ¹` return -/

private theorem norm_reciprocal_sqrt_weight_sq (k : SpatialFrequency) :
    ‖(((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ)‖ ^ 2 =
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k)]

/-- [definition] The reciprocal square-root Sobolev weight as a genuine Fourier `ℓ²` population. -/
def reciprocalSobolevThreeSqrt : PeriodicFourierL2 :=
  ⟨fun k ↦ (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two, norm_reciprocal_sqrt_weight_sq] using
      summable_periodicSobolevWeight_three_inv⟩

private theorem norm_weighted_sobolev_three_sq
    (coeff : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖(Real.sqrt (periodicSobolevWeight 3 k) : ℂ) * coeff.1 k‖ ^ 2 =
      periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k)]

/-- [definition] Apply the exact square-root `H³` weight and return the resulting `ℓ²` population. -/
def weightedSobolevThreeCoefficient
    (coeff : PeriodicSobolevCoefficients 3) : PeriodicFourierL2 :=
  ⟨fun k ↦ (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) * coeff.1 k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hcoeff := coeff.2
    unfold HasPeriodicSobolevCoefficients at hcoeff
    simpa only [Real.rpow_two, norm_weighted_sobolev_three_sq] using hcoeff⟩

/-- [proved-derived] Every weighted `H³` coefficient population is absolutely summable. -/
theorem summable_norm_periodicSobolevThreeCoefficient
    (coeff : PeriodicSobolevCoefficients 3) :
    Summable fun k ↦ ‖coeff.1 k‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hproduct := lp.summable_mul hholder reciprocalSobolevThreeSqrt
    (weightedSobolevThreeCoefficient coeff)
  apply hproduct.congr
  intro k
  have hweightPos : 0 < periodicSobolevWeight 3 k := by
    unfold periodicSobolevWeight
    exact pow_pos (by linarith [torusStokesEigenvalue_nonneg k]) 3
  have hsqrtPos : 0 < Real.sqrt (periodicSobolevWeight 3 k) :=
    Real.sqrt_pos.2 hweightPos
  simp only [reciprocalSobolevThreeSqrt, weightedSobolevThreeCoefficient,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos hsqrtPos]
  field_simp

/-- [proved-derived] Every vector `H³` carrier supplies the predecessor's absolute-component
aperture; it is no longer an additional hypothesis. -/
theorem periodicVectorSobolevThree_hasAbsolutelySummableComponents
    (state : PeriodicVectorSobolevThree) :
    HasAbsolutelySummableComponents state := by
  intro component
  exact summable_norm_periodicSobolevThreeCoefficient (state component)

/-! ## A real nonnegative Young carrier for weighted envelopes -/

/-- [definition] Real `ℓ²(ℤ³)` is used only as the exact nonnegative norm-envelope carrier. -/
abbrev PeriodicRealFourierL2 := ℓ²(SpatialFrequency, ℝ)

/-- [definition] Translation of a complete real Fourier envelope. -/
def translatePeriodicRealFourierL2
    (p : SpatialFrequency) (coeff : PeriodicRealFourierL2) : PeriodicRealFourierL2 :=
  ⟨fun k ↦ coeff (k - p), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hcoeff : Summable (fun k ↦ ‖coeff k‖ ^ 2) := by
      have h := (lp.memℓp coeff).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using h
    have htranslated := (frequencyTranslation p).summable_iff.mpr hcoeff
    have hfun :
        ((fun k : SpatialFrequency ↦ ‖coeff k‖ ^ 2) ∘ frequencyTranslation p) =
          (fun i ↦ ‖coeff (i - p)‖ ^ 2) := by
      funext i
      simp only [Function.comp_apply, frequencyTranslation_apply]
    simpa only [Real.rpow_two] using (hfun ▸ htranslated)⟩

@[simp]
theorem translatePeriodicRealFourierL2_apply
    (p : SpatialFrequency) (coeff : PeriodicRealFourierL2) (k : SpatialFrequency) :
    translatePeriodicRealFourierL2 p coeff k = coeff (k - p) := rfl

/-- [proved-derived] Translation is isometric on the real envelope carrier. -/
theorem norm_translatePeriodicRealFourierL2
    (p : SpatialFrequency) (coeff : PeriodicRealFourierL2) :
    ‖translatePeriodicRealFourierL2 p coeff‖ = ‖coeff‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (translatePeriodicRealFourierL2 p coeff)
  have hright := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) coeff
  have hsum :
      (∑' k, ‖coeff (k - p)‖ ^ 2) = ∑' k, ‖coeff k‖ ^ 2 := by
    simpa only [frequencyTranslation_apply] using
      (frequencyTranslation p).tsum_eq (fun k ↦ ‖coeff k‖ ^ 2)
  have hsquare : ‖translatePeriodicRealFourierL2 p coeff‖ ^ 2 = ‖coeff‖ ^ 2 := by
    calc
      ‖translatePeriodicRealFourierL2 p coeff‖ ^ 2 =
          ∑' k, ‖translatePeriodicRealFourierL2 p coeff k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleft
      _ = ∑' k, ‖coeff (k - p)‖ ^ 2 := by
        simp only [translatePeriodicRealFourierL2_apply]
      _ = ∑' k, ‖coeff k‖ ^ 2 := hsum
      _ = ‖coeff‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hright.symm
  nlinarith [norm_nonneg (translatePeriodicRealFourierL2 p coeff), norm_nonneg coeff]

/-- [definition] Complete real `ℓ¹ * ℓ²` convolution, formed as a Banach-space sum. -/
def realL1L2FourierConvolution
    (left : SpatialFrequency → ℝ) (right : PeriodicRealFourierL2) :
    PeriodicRealFourierL2 :=
  ∑' p, left p • translatePeriodicRealFourierL2 p right

private theorem summable_realL1L2_passages
    {left : SpatialFrequency → ℝ} (hleft : Summable fun p ↦ ‖left p‖)
    (right : PeriodicRealFourierL2) :
    Summable fun p ↦ left p • translatePeriodicRealFourierL2 p right := by
  apply Summable.of_norm
  have hscaled : Summable fun p ↦ ‖left p‖ * ‖right‖ := hleft.mul_right ‖right‖
  simpa only [norm_smul, Real.norm_eq_abs, norm_translatePeriodicRealFourierL2] using hscaled

private def periodicRealFourierL2Evaluation
    (k : SpatialFrequency) : PeriodicRealFourierL2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun coeff ↦ coeff k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun coeff ↦ by
      change ‖coeff k‖ ≤ 1 * ‖coeff‖
      simpa only [one_mul] using
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) coeff k)

@[simp]
private theorem periodicRealFourierL2Evaluation_apply
    (k : SpatialFrequency) (coeff : PeriodicRealFourierL2) :
    periodicRealFourierL2Evaluation k coeff = coeff k := rfl

/-- [proved-derived] Exact coefficient law for the complete real convolution. -/
theorem realL1L2FourierConvolution_apply
    {left : SpatialFrequency → ℝ} (hleft : Summable fun p ↦ ‖left p‖)
    (right : PeriodicRealFourierL2) (k : SpatialFrequency) :
    realL1L2FourierConvolution left right k =
      ∑' p, left p * right (k - p) := by
  have hsummable := summable_realL1L2_passages hleft right
  change periodicRealFourierL2Evaluation k
      (realL1L2FourierConvolution left right) = _
  rw [realL1L2FourierConvolution,
    (periodicRealFourierL2Evaluation k).map_tsum hsummable]
  simp only [periodicRealFourierL2Evaluation_apply, lp.coeFn_smul, Pi.smul_apply,
    translatePeriodicRealFourierL2_apply, smul_eq_mul]

/-- [proved-derived] Real discrete Young inequality with constant one. -/
theorem norm_realL1L2FourierConvolution_le
    {left : SpatialFrequency → ℝ} (hleft : Summable fun p ↦ ‖left p‖)
    (right : PeriodicRealFourierL2) :
    ‖realL1L2FourierConvolution left right‖ ≤
      (∑' p, ‖left p‖) * ‖right‖ := by
  have hnorm : Summable fun p ↦
      ‖left p • translatePeriodicRealFourierL2 p right‖ := by
    have hscaled : Summable fun p ↦ ‖left p‖ * ‖right‖ :=
      hleft.mul_right ‖right‖
    simpa only [norm_smul, Real.norm_eq_abs, norm_translatePeriodicRealFourierL2] using hscaled
  calc
    ‖realL1L2FourierConvolution left right‖ ≤
        ∑' p, ‖left p • translatePeriodicRealFourierL2 p right‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' p, ‖left p‖ * ‖right‖ := by
      congr 1
      funext p
      rw [norm_smul, norm_translatePeriodicRealFourierL2]
    _ = (∑' p, ‖left p‖) * ‖right‖ := hleft.tsum_mul_right ‖right‖

/-! ## The third-order weight interaction -/

/-- [proved-derived] The order-one inhomogeneous Stokes weight of an output frequency is bounded
by the two input weights. -/
theorem periodicSobolevWeight_one_add_le
    (p q : SpatialFrequency) :
    periodicSobolevWeight 1 (p + q) ≤
      2 * (periodicSobolevWeight 1 p + periodicSobolevWeight 1 q) := by
  have hfrequency : frequencySquared (p + q) ≤
      2 * (frequencySquared p + frequencySquared q) := by
    unfold frequencySquared
    simp only [Pi.add_apply, Int.cast_add]
    calc
      ∑ j : Fin 3, (↑(p j) + ↑(q j)) ^ 2 ≤
          ∑ j : Fin 3, 2 * ((p j : ℝ) ^ 2 + (q j : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro j _hj
        nlinarith [sq_nonneg ((p j : ℝ) - (q j : ℝ))]
      _ = 2 * ((∑ j : Fin 3, (p j : ℝ) ^ 2) +
          ∑ j : Fin 3, (q j : ℝ) ^ 2) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hscale : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have heigen : torusStokesEigenvalue (p + q) ≤
      2 * (torusStokesEigenvalue p + torusStokesEigenvalue q) := by
    simp only [torusStokesEigenvalue]
    nlinarith [mul_le_mul_of_nonneg_left hfrequency hscale]
  simp only [periodicSobolevWeight, pow_one]
  nlinarith [torusStokesEigenvalue_nonneg p, torusStokesEigenvalue_nonneg q]

/-- [definition] The positive square-root of the exact squared `H³` Fourier weight. -/
def sobolevThreeAmplitude (k : SpatialFrequency) : ℝ :=
  Real.sqrt (periodicSobolevWeight 3 k)

/-- [proved-derived] The exact third-order amplitude is nonnegative. -/
theorem sobolevThreeAmplitude_nonneg (k : SpatialFrequency) :
    0 ≤ sobolevThreeAmplitude k :=
  Real.sqrt_nonneg _

/-- [proved-derived] The third-order amplitude at a summed frequency distributes over the two
input amplitudes with an explicit constant eight. -/
theorem sobolevThreeAmplitude_add_le
    (p q : SpatialFrequency) :
    sobolevThreeAmplitude (p + q) ≤
      8 * (sobolevThreeAmplitude p + sobolevThreeAmplitude q) := by
  let a := periodicSobolevWeight 1 p
  let b := periodicSobolevWeight 1 q
  let c := periodicSobolevWeight 1 (p + q)
  have ha : 0 ≤ a := periodicSobolevWeight_nonneg 1 p
  have hb : 0 ≤ b := periodicSobolevWeight_nonneg 1 q
  have hc : 0 ≤ c := periodicSobolevWeight_nonneg 1 (p + q)
  have hc_le : c ≤ 2 * (a + b) := periodicSobolevWeight_one_add_le p q
  have hcube : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
  have hcCube : c ^ 3 ≤ 32 * (a ^ 3 + b ^ 3) := by
    have hpow := pow_le_pow_left₀ hc hc_le 3
    nlinarith
  have haPower : periodicSobolevWeight 3 p = a ^ 3 := by
    simp [a, periodicSobolevWeight]
  have hbPower : periodicSobolevWeight 3 q = b ^ 3 := by
    simp [b, periodicSobolevWeight]
  have hcPower : periodicSobolevWeight 3 (p + q) = c ^ 3 := by
    simp [c, periodicSobolevWeight]
  have hrootA : sobolevThreeAmplitude p ^ 2 = a ^ 3 := by
    rw [sobolevThreeAmplitude,
      Real.sq_sqrt (periodicSobolevWeight_nonneg 3 p), haPower]
  have hrootB : sobolevThreeAmplitude q ^ 2 = b ^ 3 := by
    rw [sobolevThreeAmplitude,
      Real.sq_sqrt (periodicSobolevWeight_nonneg 3 q), hbPower]
  have hrootC : sobolevThreeAmplitude (p + q) ^ 2 = c ^ 3 := by
    rw [sobolevThreeAmplitude,
      Real.sq_sqrt (periodicSobolevWeight_nonneg 3 (p + q)), hcPower]
  have hA0 : 0 ≤ sobolevThreeAmplitude p := Real.sqrt_nonneg _
  have hB0 : 0 ≤ sobolevThreeAmplitude q := Real.sqrt_nonneg _
  have hC0 : 0 ≤ sobolevThreeAmplitude (p + q) := Real.sqrt_nonneg _
  rw [← hrootC, ← hrootA, ← hrootB] at hcCube
  nlinarith [sq_nonneg (8 * (sobolevThreeAmplitude p + sobolevThreeAmplitude q) +
    sobolevThreeAmplitude (p + q))]

/-! ## The complete scalar `H³` convolution algebra -/

/-- [proved-derived] Squaring the amplitude returns the exact order-three Sobolev weight. -/
theorem sobolevThreeAmplitude_sq (k : SpatialFrequency) :
    sobolevThreeAmplitude k ^ 2 = periodicSobolevWeight 3 k := by
  rw [sobolevThreeAmplitude,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k)]

/-- [definition] The nonnegative coefficient-norm population. -/
def absoluteCoefficient
    (coeff : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) : ℝ :=
  ‖coeff.1 k‖

/-- [proved-derived] The absolute coefficient population is genuinely `ℓ¹`. -/
theorem summable_norm_absoluteCoefficient
    (coeff : PeriodicSobolevCoefficients 3) :
    Summable fun k ↦ ‖absoluteCoefficient coeff k‖ := by
  simpa only [absoluteCoefficient, Real.norm_eq_abs, abs_norm] using
    summable_norm_periodicSobolevThreeCoefficient coeff

/-- [definition] The exact `H³` amplitude times coefficient norm, packaged in real `ℓ²`. -/
def weightedAbsoluteCoefficient
    (coeff : PeriodicSobolevCoefficients 3) : PeriodicRealFourierL2 :=
  ⟨fun k ↦ sobolevThreeAmplitude k * ‖coeff.1 k‖, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hnonneg (k : SpatialFrequency) :
        0 ≤ sobolevThreeAmplitude k * ‖coeff.1 k‖ :=
      mul_nonneg (sobolevThreeAmplitude_nonneg k) (norm_nonneg _)
    have hcoeff := coeff.2
    unfold HasPeriodicSobolevCoefficients at hcoeff
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg _), mul_pow, sobolevThreeAmplitude_sq] using hcoeff⟩

/-- [definition] The positive real `ℓ²` envelope for the weighted product convolution. -/
def scalarProductEnvelope
    (left right : PeriodicSobolevCoefficients 3) : PeriodicRealFourierL2 :=
  (8 : ℝ) • (realL1L2FourierConvolution (absoluteCoefficient left)
      (weightedAbsoluteCoefficient right) +
    realL1L2FourierConvolution (absoluteCoefficient right)
      (weightedAbsoluteCoefficient left))

/-- [proved-derived] Every coefficient of the product envelope is nonnegative. -/
theorem scalarProductEnvelope_nonneg
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    0 ≤ scalarProductEnvelope left right k := by
  change 0 ≤ 8 *
    (realL1L2FourierConvolution (absoluteCoefficient left)
        (weightedAbsoluteCoefficient right) k +
      realL1L2FourierConvolution (absoluteCoefficient right)
        (weightedAbsoluteCoefficient left) k)
  rw [realL1L2FourierConvolution_apply (summable_norm_absoluteCoefficient left),
    realL1L2FourierConvolution_apply (summable_norm_absoluteCoefficient right)]
  refine mul_nonneg (by norm_num) (add_nonneg (tsum_nonneg fun p ↦ ?_)
    (tsum_nonneg fun p ↦ ?_))
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- [definition] Complete complex Fourier convolution of two scalar `H³` populations. -/
def scalarH3ProductConvolution
    (left right : PeriodicSobolevCoefficients 3) : PeriodicFourierL2 :=
  l1L2FourierConvolution (fun p ↦ left.1 p) right.1

/-- [proved-derived] Exact coefficient law for the scalar product convolution. -/
theorem scalarH3ProductConvolution_apply
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    scalarH3ProductConvolution left right k =
      ∑' p, left.1 p * right.1 (k - p) := by
  exact l1L2FourierConvolution_apply
    (summable_norm_periodicSobolevThreeCoefficient left) right.1 k

private theorem summable_scalar_product_norm_terms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p ↦ ‖left.1 p * right.1 (k - p)‖ := by
  have hleft := summable_norm_periodicSobolevThreeCoefficient left
  have hbound : Summable fun p ↦ ‖left.1 p‖ * ‖right.1‖ :=
    hleft.mul_right ‖right.1‖
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) right.1 (k - p))
    (norm_nonneg _)

private theorem summable_first_weighted_product_terms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p ↦
      ‖left.1 p‖ * (sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖) := by
  have hleft := summable_norm_periodicSobolevThreeCoefficient left
  have hbound : Summable fun p ↦
      ‖left.1 p‖ * ‖weightedAbsoluteCoefficient right‖ :=
    hleft.mul_right ‖weightedAbsoluteCoefficient right‖
  refine Summable.of_nonneg_of_le
    (fun p ↦ mul_nonneg (norm_nonneg _)
      (mul_nonneg (sobolevThreeAmplitude_nonneg _) (norm_nonneg _)))
    (fun p ↦ ?_) hbound
  have heval := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weightedAbsoluteCoefficient right) (k - p)
  have hweightedNonneg :
      0 ≤ sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖ :=
    mul_nonneg (sobolevThreeAmplitude_nonneg _) (norm_nonneg _)
  have heval' :
      sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖ ≤
        ‖weightedAbsoluteCoefficient right‖ := by
    simpa only [weightedAbsoluteCoefficient, Real.norm_eq_abs,
      abs_of_nonneg hweightedNonneg] using heval
  exact mul_le_mul_of_nonneg_left heval' (norm_nonneg _)

private theorem summable_second_weighted_product_terms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p ↦
      (sobolevThreeAmplitude p * ‖left.1 p‖) * ‖right.1 (k - p)‖ := by
  let reflected : SpatialFrequency ≃ SpatialFrequency := Equiv.subLeft k
  have hright := summable_norm_periodicSobolevThreeCoefficient right
  have hbase : Summable fun q ↦
      ‖right.1 q‖ * ‖weightedAbsoluteCoefficient left‖ :=
    hright.mul_right ‖weightedAbsoluteCoefficient left‖
  have hshiftedBase : Summable fun q ↦
      ‖right.1 q‖ * (sobolevThreeAmplitude (k - q) * ‖left.1 (k - q)‖) := by
    refine Summable.of_nonneg_of_le
      (fun q ↦ mul_nonneg (norm_nonneg _)
        (mul_nonneg (sobolevThreeAmplitude_nonneg _) (norm_nonneg _)))
      (fun q ↦ ?_) hbase
    have heval := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (weightedAbsoluteCoefficient left) (k - q)
    have hweightedNonneg :
        0 ≤ sobolevThreeAmplitude (k - q) * ‖left.1 (k - q)‖ :=
      mul_nonneg (sobolevThreeAmplitude_nonneg _) (norm_nonneg _)
    have heval' :
        sobolevThreeAmplitude (k - q) * ‖left.1 (k - q)‖ ≤
          ‖weightedAbsoluteCoefficient left‖ := by
      simpa only [weightedAbsoluteCoefficient, Real.norm_eq_abs,
        abs_of_nonneg hweightedNonneg] using heval
    exact mul_le_mul_of_nonneg_left heval' (norm_nonneg _)
  have hreindexed := reflected.summable_iff.mpr hshiftedBase
  refine hreindexed.congr ?_
  intro p
  simp only [Function.comp_apply, reflected, Equiv.subLeft_apply]
  ring_nf

/-- [proved-derived] The exact weighted product coefficient is bounded by the real Young
envelope at the same output frequency. -/
theorem norm_sobolevThreeAmplitude_mul_scalarH3ProductConvolution_le_envelope
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖(sobolevThreeAmplitude k : ℂ) * scalarH3ProductConvolution left right k‖ ≤
      scalarProductEnvelope left right k := by
  have hplain := summable_scalar_product_norm_terms left right k
  have hfirst := summable_first_weighted_product_terms left right k
  have hsecond := summable_second_weighted_product_terms left right k
  have hright : Summable fun p ↦ 8 *
      (‖left.1 p‖ * (sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖) +
        (sobolevThreeAmplitude p * ‖left.1 p‖) * ‖right.1 (k - p)‖) :=
    (hfirst.add hsecond).mul_left 8
  have hweightedPlain : Summable fun p ↦
      sobolevThreeAmplitude k * ‖left.1 p * right.1 (k - p)‖ :=
    hplain.mul_left (sobolevThreeAmplitude k)
  have hterm : ∀ p,
      sobolevThreeAmplitude k * ‖left.1 p * right.1 (k - p)‖ ≤
        8 * (‖left.1 p‖ *
            (sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖) +
          (sobolevThreeAmplitude p * ‖left.1 p‖) * ‖right.1 (k - p)‖) := by
    intro p
    have hsum : p + (k - p) = k := by abel
    have hweight := sobolevThreeAmplitude_add_le p (k - p)
    rw [hsum] at hweight
    rw [norm_mul]
    have hmul := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (norm_nonneg (left.1 p)) (norm_nonneg (right.1 (k - p))))
    nlinarith
  calc
    ‖(sobolevThreeAmplitude k : ℂ) * scalarH3ProductConvolution left right k‖ =
        sobolevThreeAmplitude k * ‖scalarH3ProductConvolution left right k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sobolevThreeAmplitude_nonneg k)]
    _ ≤ sobolevThreeAmplitude k *
        (∑' p, ‖left.1 p * right.1 (k - p)‖) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      rw [scalarH3ProductConvolution_apply]
      exact norm_tsum_le_tsum_norm hplain
    _ = ∑' p, sobolevThreeAmplitude k *
        ‖left.1 p * right.1 (k - p)‖ := by
      rw [hplain.tsum_mul_left]
    _ ≤ ∑' p, 8 *
        (‖left.1 p‖ * (sobolevThreeAmplitude (k - p) * ‖right.1 (k - p)‖) +
          (sobolevThreeAmplitude p * ‖left.1 p‖) * ‖right.1 (k - p)‖) :=
      hweightedPlain.tsum_le_tsum hterm hright
    _ = scalarProductEnvelope left right k := by
      change _ = 8 *
        (realL1L2FourierConvolution (absoluteCoefficient left)
            (weightedAbsoluteCoefficient right) k +
          realL1L2FourierConvolution (absoluteCoefficient right)
            (weightedAbsoluteCoefficient left) k)
      rw [tsum_mul_left, hfirst.tsum_add hsecond,
        realL1L2FourierConvolution_apply (summable_norm_absoluteCoefficient left),
        realL1L2FourierConvolution_apply (summable_norm_absoluteCoefficient right)]
      congr 1
      congr 1
      let reflected : SpatialFrequency ≃ SpatialFrequency := Equiv.subLeft k
      let reflectedTerm : SpatialFrequency → ℝ := fun q ↦
        ‖right.1 q‖ *
          (sobolevThreeAmplitude (k - q) * ‖left.1 (k - q)‖)
      calc
        (∑' p, (sobolevThreeAmplitude p * ‖left.1 p‖) *
            ‖right.1 (k - p)‖) =
            ∑' p, reflectedTerm (reflected p) := by
          apply tsum_congr
          intro p
          have hcancel : k - (k - p) = p := by abel
          simp only [reflectedTerm, reflected, Equiv.subLeft_apply, hcancel]
          ring
        _ = ∑' q, reflectedTerm q := reflected.tsum_eq reflectedTerm
        _ = ∑' q, ‖right.1 q‖ *
            (sobolevThreeAmplitude (k - q) * ‖left.1 (k - q)‖) := rfl

/-- [definition] Scalar Fourier multiplication closes on the exact weighted `H³` carrier. -/
def scalarH3Product
    (left right : PeriodicSobolevCoefficients 3) : PeriodicSobolevCoefficients 3 :=
  ⟨scalarH3ProductConvolution left right, by
    let envelope := scalarProductEnvelope left right
    have henvelopeSq : Summable fun k ↦ (envelope k) ^ 2 := by
      have h := (lp.memℓp envelope).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using h
    refine Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg 3 k) (sq_nonneg _))
      (fun k ↦ ?_) henvelopeSq
    have hbound :=
      norm_sobolevThreeAmplitude_mul_scalarH3ProductConvolution_le_envelope left right k
    have henvelopeNonneg := scalarProductEnvelope_nonneg left right k
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    calc
      periodicSobolevWeight 3 k * ‖scalarH3ProductConvolution left right k‖ ^ 2 =
          ‖(sobolevThreeAmplitude k : ℂ) *
            scalarH3ProductConvolution left right k‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sobolevThreeAmplitude_nonneg k), mul_pow,
          sobolevThreeAmplitude_sq]
      _ ≤ envelope k ^ 2 := hsquare⟩

/-- [proved-derived] The scalar product retains its exact convolution coefficients inside `H³`. -/
theorem scalarH3Product_apply
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    (scalarH3Product left right).1 k =
      ∑' p, left.1 p * right.1 (k - p) :=
  scalarH3ProductConvolution_apply left right k

#print axioms summable_one_add_int_sq_inv
#print axioms summable_separableReciprocalWeight
#print axioms summable_periodicSobolevWeight_three_inv
#print axioms summable_norm_periodicSobolevThreeCoefficient
#print axioms periodicVectorSobolevThree_hasAbsolutelySummableComponents
#print axioms norm_translatePeriodicRealFourierL2
#print axioms realL1L2FourierConvolution_apply
#print axioms norm_realL1L2FourierConvolution_le
#print axioms periodicSobolevWeight_one_add_le
#print axioms sobolevThreeAmplitude_add_le
#print axioms scalarProductEnvelope_nonneg
#print axioms scalarH3ProductConvolution_apply
#print axioms norm_sobolevThreeAmplitude_mul_scalarH3ProductConvolution_le_envelope
#print axioms scalarH3Product
#print axioms scalarH3Product_apply

end Soma.Holonics.Millennium.NavierStokesH3Bilinear
