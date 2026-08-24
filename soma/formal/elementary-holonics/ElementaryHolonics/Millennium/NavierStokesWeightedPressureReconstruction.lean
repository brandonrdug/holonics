import ElementaryHolonics.Millennium.NavierStokesWeightedPressureCoefficient
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction

/-!
# Native pressure gain and coefficient-exact reconstruction

**[proved-derived]** The zero-gauge Leray-complement pressure multiplier gains exactly one
Sobolev order.  This owner packages it as a bounded complex-linear passage from the native
three-component `H²` carrier to the native scalar `H³` carrier, with an explicit norm bound.

The existing full-lattice `H³` reconstruction then returns a real `C¹`, one-periodic scalar
pressure whenever the input vector population is Fourier real.  The pressure and its coordinate
gradient retain their exact source coefficients.  No `C²`, smooth, or classical PDE pressure
claim is made.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The native one-order pressure multiplier -/

/-- The contribution of one native `H²` vector component to the native scalar `H³` pressure
coefficient at `k`.  The zero mode is fixed to zero. -/
def nativePressureMultiplier (component : Fin 3) (k : SpatialFrequency) : ℂ :=
  if k = 0 then 0
  else
    (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) *
      (Complex.I * (k component : ℂ) *
        ((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ)) /
        ((2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ)))

private theorem one_le_frequencySquared_of_ne_zero
    {k : SpatialFrequency} (hk : k ≠ 0) :
    1 ≤ frequencySquared k := by
  obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hk
  have habsInt : (1 : ℤ) ≤ |k component| := Int.one_le_abs hcomponent
  have habsReal : (1 : ℝ) ≤ |(k component : ℝ)| := by
    exact_mod_cast habsInt
  have hcoordinate : (k component : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ component)
  nlinarith [sq_abs (k component : ℝ)]

/-- The one-order pressure gain is uniformly bounded at every component and mode. -/
theorem norm_nativePressureMultiplier_le_two
    (component : Fin 3) (k : SpatialFrequency) :
    ‖nativePressureMultiplier component k‖ ≤ 2 := by
  by_cases hk : k = 0
  · subst k
    simp [nativePressureMultiplier]
  · have hsPos : 0 < frequencySquared k := frequencySquared_pos hk
    have hsOne : 1 ≤ frequencySquared k := one_le_frequencySquared_of_ne_zero hk
    have hcoordinate : (k component : ℝ) ^ 2 ≤ frequencySquared k := by
      unfold frequencySquared
      exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
        (Finset.mem_univ component)
    have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hlambdaOne : 1 ≤ torusStokesEigenvalue k := by
      rw [torusStokesEigenvalue]
      nlinarith
    have hweightTwoPos : 0 < periodicSobolevWeight 2 k :=
      periodicSobolevWeight_pos 2 k
    have hsquare :
        ‖nativePressureMultiplier component k‖ ^ 2 =
          (1 + torusStokesEigenvalue k) * (k component : ℝ) ^ 2 /
            ((2 * Real.pi) ^ 2 * frequencySquared k ^ 2) := by
      rw [nativePressureMultiplier, if_neg hk]
      simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, Complex.norm_intCast, one_mul, mul_pow]
      rw [abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
        abs_of_pos Real.pi_pos, abs_of_pos hsPos]
      simp only [Complex.norm_ofNat]
      rw [div_pow, mul_pow, mul_pow, inv_pow, sq_abs,
        Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k),
        Real.sq_sqrt (periodicSobolevWeight_nonneg 2 k)]
      simp only [periodicSobolevWeight]
      field_simp [hweightTwoPos.ne']
    have hdenPos : 0 < (2 * Real.pi) ^ 2 * frequencySquared k ^ 2 := by
      positivity
    have hratio :
        (1 + torusStokesEigenvalue k) * (k component : ℝ) ^ 2 /
            ((2 * Real.pi) ^ 2 * frequencySquared k ^ 2) ≤ 2 := by
      rw [torusStokesEigenvalue]
      apply (div_le_iff₀ hdenPos).2
      have hbase : 0 ≤ 1 + (2 * Real.pi) ^ 2 * frequencySquared k := by
        positivity
      calc
        (1 + (2 * Real.pi) ^ 2 * frequencySquared k) *
            (k component : ℝ) ^ 2 ≤
            (1 + (2 * Real.pi) ^ 2 * frequencySquared k) *
              frequencySquared k :=
          mul_le_mul_of_nonneg_left hcoordinate hbase
        _ ≤ (2 * (2 * Real.pi) ^ 2 * frequencySquared k) *
              frequencySquared k := by
          apply mul_le_mul_of_nonneg_right _ hsPos.le
          nlinarith
        _ = 2 * ((2 * Real.pi) ^ 2 * frequencySquared k ^ 2) := by ring
    nlinarith [norm_nonneg (nativePressureMultiplier component k)]

/-- One component's diagonal pressure passage on the complete native carrier. -/
def nativePressureComponent
    (component : Fin 3) (state : PeriodicWeightedSobolev 2) :
    PeriodicWeightedSobolev 3 :=
  ⟨fun k ↦ nativePressureMultiplier component k * state k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hstate : Summable fun k ↦ ‖state k‖ ^ 2 := by
      have h := (lp.memℓp state).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (hstate.mul_left 4)
    have hmultiplier := norm_nativePressureMultiplier_le_two component k
    simp only [Real.rpow_two, norm_mul]
    have hmultiplierSq : ‖nativePressureMultiplier component k‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (nativePressureMultiplier component k)]
    calc
      (‖nativePressureMultiplier component k‖ * ‖state k‖) ^ 2 =
          ‖nativePressureMultiplier component k‖ ^ 2 * ‖state k‖ ^ 2 := by ring
      _ ≤ 4 * ‖state k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmultiplierSq (sq_nonneg _)⟩

@[simp]
theorem nativePressureComponent_apply
    (component : Fin 3) (state : PeriodicWeightedSobolev 2)
    (k : SpatialFrequency) :
    nativePressureComponent component state k =
      nativePressureMultiplier component k * state k :=
  rfl

/-- Quantitative norm bound for one component contribution. -/
theorem norm_nativePressureComponent_le
    (component : Fin 3) (state : PeriodicWeightedSobolev 2) :
    ‖nativePressureComponent component state‖ ≤ 2 * ‖state‖ := by
  have hleftSummable : Summable fun k ↦
      ‖nativePressureComponent component state k‖ ^ 2 := by
    have h := (lp.memℓp (nativePressureComponent component state)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hrightSummable : Summable fun k ↦ 4 * ‖state k‖ ^ 2 := by
    have h := (lp.memℓp state).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have h' : Summable fun k ↦ ‖state k‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    exact h'.mul_left 4
  have hpoint : ∀ k,
      ‖nativePressureComponent component state k‖ ^ 2 ≤
        4 * ‖state k‖ ^ 2 := by
    intro k
    rw [nativePressureComponent_apply, norm_mul, mul_pow]
    have hmultiplier := norm_nativePressureMultiplier_le_two component k
    have hmultiplierSq : ‖nativePressureMultiplier component k‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (nativePressureMultiplier component k)]
    exact mul_le_mul_of_nonneg_right hmultiplierSq (sq_nonneg _)
  have hsum := hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hleftNorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (nativePressureComponent component state)
  have hrightNorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) state
  have hleftNormNat :
      ‖nativePressureComponent component state‖ ^ 2 =
        ∑' k, ‖nativePressureComponent component state k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleftNorm
  have hrightNormNat :
      ‖state‖ ^ 2 = ∑' k, ‖state k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hrightNorm
  have hsquare :
      ‖nativePressureComponent component state‖ ^ 2 ≤
        4 * ‖state‖ ^ 2 := by
    calc
      ‖nativePressureComponent component state‖ ^ 2 =
          ∑' k, ‖nativePressureComponent component state k‖ ^ 2 := hleftNormNat
      _ ≤ ∑' k, 4 * ‖state k‖ ^ 2 := hsum
      _ = 4 * ∑' k, ‖state k‖ ^ 2 := by rw [tsum_mul_left]
      _ = 4 * ‖state‖ ^ 2 := by rw [← hrightNormNat]
  nlinarith [norm_nonneg (nativePressureComponent component state), norm_nonneg state]

/-- The complete zero-gauge pressure passage from native vector `H²` to native scalar `H³`.
The explicit constant six is the finite-component supremum-norm receipt. -/
def nativePressureFromH2 :
    PeriodicVectorWeightedSobolev 2 →L[ℂ] PeriodicWeightedSobolev 3 :=
  LinearMap.mkContinuous
    { toFun := fun state ↦
        ∑ component : Fin 3, nativePressureComponent component (state component)
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [lp.coeFn_sum, Finset.sum_apply, nativePressureComponent_apply,
          lp.coeFn_add, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro component _
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [lp.coeFn_sum, Finset.sum_apply, nativePressureComponent_apply,
          Pi.smul_apply, lp.coeFn_smul, RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro component _
        ring }
    6 (fun state ↦ by
      calc
        ‖∑ component : Fin 3,
            nativePressureComponent component (state component)‖ ≤
            ∑ component : Fin 3,
              ‖nativePressureComponent component (state component)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ component : Fin 3, 2 * ‖state component‖ := by
          apply Finset.sum_le_sum
          intro component _
          exact norm_nativePressureComponent_le component (state component)
        _ ≤ ∑ _component : Fin 3, 2 * ‖state‖ := by
          apply Finset.sum_le_sum
          intro component _
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (by norm_num)
        _ = 6 * ‖state‖ := by
          simp only [Fin.sum_univ_three]
          ring)

@[simp]
theorem nativePressureFromH2_apply
    (state : PeriodicVectorWeightedSobolev 2) (k : SpatialFrequency) :
    nativePressureFromH2 state k =
      ∑ component : Fin 3,
        nativePressureMultiplier component k * state component k := by
  rfl

theorem norm_nativePressureFromH2_le
    (state : PeriodicVectorWeightedSobolev 2) :
    ‖nativePressureFromH2 state‖ ≤ 6 * ‖state‖ := by
  calc
    ‖nativePressureFromH2 state‖ =
        ‖∑ component : Fin 3,
          nativePressureComponent component (state component)‖ := rfl
    _ ≤ ∑ component : Fin 3,
        ‖nativePressureComponent component (state component)‖ := norm_sum_le _ _
    _ ≤ ∑ component : Fin 3, 2 * ‖state component‖ := by
      apply Finset.sum_le_sum
      intro component _
      exact norm_nativePressureComponent_le component (state component)
    _ ≤ ∑ _component : Fin 3, 2 * ‖state‖ := by
      apply Finset.sum_le_sum
      intro component _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (by norm_num)
    _ = 6 * ‖state‖ := by
      simp only [Fin.sum_univ_three]
      ring

/-! ## Exact physical coefficients and reality -/

/-- Unweight a native vector `H²` face at one addressed mode. -/
def physicalH2Mode
    (state : PeriodicVectorWeightedSobolev 2) (k : SpatialFrequency) :
    ComplexVector :=
  fun component ↦ (weightedSobolevCoefficients 2 (state component)).1 k

private theorem unweight_nativePressureMultiplier_of_ne_zero
    (component : Fin 3) {k : SpatialFrequency} (hk : k ≠ 0) :
    (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
        nativePressureMultiplier component k =
      Complex.I * (k component : ℂ) *
          ((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ)) /
        ((2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ)) := by
  rw [nativePressureMultiplier, if_neg hk, ← mul_assoc]
  have hsqrt : Real.sqrt (periodicSobolevWeight 3 k) ≠ 0 :=
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos 3 k)).ne'
  have hcancel :
      (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
          (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) = 1 := by
    norm_cast
    field_simp
  rw [hcancel, one_mul]

/-- Unweighting the bounded native passage recovers exactly the zero-gauge physical pressure
coefficient selected from the unweighted vector mode. -/
theorem weightedSobolevCoefficients_nativePressureFromH2
    (state : PeriodicVectorWeightedSobolev 2) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3 (nativePressureFromH2 state)).1 k =
      pressureCoefficientOfMode k (physicalH2Mode state k) := by
  by_cases hk : k = 0
  · subst k
    simp [weightedSobolevCoefficients, weightedSobolevRawCoefficients,
      nativePressureFromH2_apply, nativePressureMultiplier,
      pressureCoefficientOfMode]
  · change
      (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
          nativePressureFromH2 state k =
        pressureCoefficientOfMode k (physicalH2Mode state k)
    rw [nativePressureFromH2_apply, Finset.mul_sum,
      pressureCoefficientOfMode, if_neg hk]
    simp only [physicalH2Mode, weightedSobolevCoefficients,
      weightedSobolevRawCoefficients, complexDot, dotProduct,
      complexFrequencyVector]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro component _
    rw [← mul_assoc,
      unweight_nativePressureMultiplier_of_ne_zero component hk]
    ring

/-- Scalar Fourier reality in the native weighted chart. -/
def IsScalarWeightedFourierReal
    (order : ℕ) (state : PeriodicWeightedSobolev order) : Prop :=
  ∀ k,
    (weightedSobolevCoefficients order state).1 (-k) =
      conj ((weightedSobolevCoefficients order state).1 k)

/-- The bounded pressure passage carries every Fourier-real vector `H²` population into a
Fourier-real scalar `H³` population. -/
theorem isScalarWeightedFourierReal_nativePressureFromH2
    {state : PeriodicVectorWeightedSobolev 2}
    (hstate : IsWeightedFourierReal 2 state) :
    IsScalarWeightedFourierReal 3 (nativePressureFromH2 state) := by
  intro k
  rw [weightedSobolevCoefficients_nativePressureFromH2,
    weightedSobolevCoefficients_nativePressureFromH2]
  have hmode : physicalH2Mode state (-k) =
      fun component ↦ conj (physicalH2Mode state k component) := by
    funext component
    exact hstate component k
  rw [hmode]
  exact pressureCoefficientOfMode_neg_conj k _

/-! ## The actual unprojected quadratic source -/

/-- Weight the actual unprojected divergence convolution into the native vector `H²` carrier. -/
def weightedUnprojectedDivergenceState
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    PeriodicVectorWeightedSobolev 2 :=
  fun component ↦ coefficientWeightedRealization 2
    (h3DivergenceConvolution
      (unweightedVectorThree (weightedPathExtension hT path t))
      (unweightedVectorThree (weightedPathExtension hT path t)) component)

/-- The physical mode of the native source is exactly the previously exposed unprojected
quadratic mode. -/
theorem physicalH2Mode_weightedUnprojectedDivergenceState
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) :
    physicalH2Mode (weightedUnprojectedDivergenceState hT path t) k =
      weightedUnprojectedDivergenceMode hT path t k := by
  funext component
  simp only [physicalH2Mode, weightedUnprojectedDivergenceState,
    weightedUnprojectedDivergenceMode]
  rw [weightedSobolevCoefficients_coefficientWeightedRealization]

/-- The actual native scalar `H³` pressure at one weighted path face. -/
def weightedNativePressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    PeriodicWeightedSobolev 3 :=
  nativePressureFromH2 (weightedUnprojectedDivergenceState hT path t)

/-- Every physical coefficient of the actual native pressure is exactly the modal pressure
coefficient returned by the Leray complement owner. -/
theorem weightedSobolevCoefficients_weightedNativePressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3 (weightedNativePressure hT path t)).1 k =
      weightedPressureCoefficient hT path t k := by
  rw [weightedNativePressure,
    weightedSobolevCoefficients_nativePressureFromH2,
    physicalH2Mode_weightedUnprojectedDivergenceState,
    weightedPressureCoefficient]

/-- A Fourier-real path returns a Fourier-real native scalar pressure. -/
theorem isScalarWeightedFourierReal_weightedNativePressure
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (t : ℝ) :
    IsScalarWeightedFourierReal 3 (weightedNativePressure hT path t) := by
  intro k
  rw [weightedSobolevCoefficients_weightedNativePressure,
    weightedSobolevCoefficients_weightedNativePressure]
  exact weightedPressureCoefficient_neg_eq_conj hT hpath t k

/-! ## Real `C¹` scalar reconstruction -/

/-- Present one native scalar `H³` population through the component reconstruction port. -/
def scalarNativeDiagonalVector
    (state : PeriodicWeightedSobolev 3) : PeriodicVectorWeightedSobolev 3 :=
  fun _component ↦ state

@[simp]
theorem nativeUnweightedComponent_scalarNativeDiagonalVector
    (state : PeriodicWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    nativeUnweightedComponent (scalarNativeDiagonalVector state) component k =
      (weightedSobolevCoefficients 3 state).1 k :=
  rfl

/-- Scalar Fourier reality supplies vector reality to the existing reconstruction port. -/
theorem isWeightedFourierReal_scalarNativeDiagonalVector
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state) :
    IsWeightedFourierReal 3 (scalarNativeDiagonalVector state) := by
  intro _component k
  exact hstate k

/-- Uniform complex synthesis of a native scalar `H³` population on the genuine torus. -/
def reconstructedScalarTorusComplex
    (state : PeriodicWeightedSobolev 3) : C(SpatialTorus, ℂ) :=
  reconstructedTorusComplexComponent (scalarNativeDiagonalVector state) 0

/-- The actual real Euclidean pressure face obtained from the complete torus synthesis. -/
def reconstructedRealPressure
    (state : PeriodicWeightedSobolev 3) : Space → ℝ :=
  fun x ↦
    (reconstructedScalarTorusComplex state (euclideanToSpatialTorus x)).re

/-- Native scalar `H³` reconstructs to an actual real `C¹` function. -/
theorem contDiff_one_reconstructedRealPressure
    (state : PeriodicWeightedSobolev 3) :
    ContDiff ℝ 1 (reconstructedRealPressure state) := by
  simpa [reconstructedRealPressure, reconstructedScalarTorusComplex,
    Function.comp_def] using
      Complex.reCLM.contDiff.comp
        (contDiff_one_reconstructedComplexComponent
          (scalarNativeDiagonalVector state) 0)

theorem continuous_reconstructedRealPressure
    (state : PeriodicWeightedSobolev 3) :
    Continuous (reconstructedRealPressure state) :=
  (contDiff_one_reconstructedRealPressure state).continuous

/-- The reconstructed real pressure is one-periodic in every coordinate. -/
theorem isOnePeriodic_reconstructedRealPressure
    (state : PeriodicWeightedSobolev 3) :
    IsOnePeriodic (reconstructedRealPressure state) := by
  intro x coordinate
  unfold reconstructedRealPressure
  rw [euclideanToSpatialTorus_add_single_one]

/-- The complex torus synthesis recovers every physical scalar coefficient exactly. -/
theorem torusSpatialFourierCoeff_reconstructedScalarTorusComplex
    (state : PeriodicWeightedSobolev 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff (reconstructedScalarTorusComplex state) k =
      (weightedSobolevCoefficients 3 state).1 k := by
  exact torusSpatialFourierCoeff_reconstructedTorusComplexComponent
    (scalarNativeDiagonalVector state) 0 k

/-- For a Fourier-real native scalar, complexifying the real pressure recovers the complete
complex synthesis pointwise. -/
theorem ofReal_reconstructedRealPressure
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state) (x : Space) :
    (reconstructedRealPressure state x : ℂ) =
      reconstructedScalarTorusComplex state (euclideanToSpatialTorus x) := by
  change
    ((reconstructedScalarTorusComplex state
      (euclideanToSpatialTorus x)).re : ℂ) = _
  exact Complex.conj_eq_iff_re.mp
    (conj_reconstructedTorusComplexComponent_eq
      (isWeightedFourierReal_scalarNativeDiagonalVector hstate) 0
      (euclideanToSpatialTorus x))

/-- Every Fourier coefficient of the actual real periodic pressure is exactly the source native
physical coefficient. -/
theorem scalarSpatialFourierCoeff_reconstructedRealPressure
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state) (k : SpatialFrequency) :
    scalarSpatialFourierCoeff
        (fun x ↦ (reconstructedRealPressure state x : ℂ))
        (Complex.continuous_ofReal.comp
          (continuous_reconstructedRealPressure state))
        (fun x coordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
          (isOnePeriodic_reconstructedRealPressure state x coordinate)) k =
      (weightedSobolevCoefficients 3 state).1 k := by
  let complexPressure : Space → ℂ :=
    fun x ↦ (reconstructedRealPressure state x : ℂ)
  have hcontinuous : Continuous complexPressure :=
    Complex.continuous_ofReal.comp (continuous_reconstructedRealPressure state)
  have hperiodic : IsOnePeriodic complexPressure := by
    intro x coordinate
    exact congrArg (fun r : ℝ ↦ (r : ℂ))
      (isOnePeriodic_reconstructedRealPressure state x coordinate)
  have hfield :
      periodicTorusLift complexPressure hcontinuous hperiodic =
        reconstructedScalarTorusComplex state := by
    ext q
    change
      (reconstructedRealPressure state (euclideanRepresentative q) : ℂ) =
        reconstructedScalarTorusComplex state q
    rw [ofReal_reconstructedRealPressure hstate,
      euclideanToSpatialTorus_representative]
  change torusSpatialFourierCoeff
      (periodicTorusLift complexPressure hcontinuous hperiodic) k = _
  rw [hfield, torusSpatialFourierCoeff_reconstructedScalarTorusComplex]

/-! ## Exact reconstructed gradient coefficients -/

/-- The addressed Fourier gradient coefficient of a native scalar pressure. -/
def scalarPressureGradientCoefficient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (k : SpatialFrequency) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
    (weightedSobolevCoefficients 3 state).1 k

/-- The gradient character passages are summable in the uniform torus norm. -/
theorem summable_scalarPressureGradientPassages
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      scalarPressureGradientCoefficient state coordinate k •
        UnitAddTorus.mFourier k := by
  have hmoment :=
    summable_coordinate_mul_norm_nativeUnweightedComponent
      (scalarNativeDiagonalVector state) 0 coordinate
  have hscaled := hmoment.mul_left (2 * Real.pi)
  apply Summable.of_norm
  apply hscaled.congr
  intro k
  simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one,
    scalarPressureGradientCoefficient, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, Complex.norm_intCast,
    nativeUnweightedComponent_scalarNativeDiagonalVector]
  ring

/-- Uniform synthesis of one addressed pressure-gradient component on the genuine torus. -/
def reconstructedScalarTorusGradient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    C(SpatialTorus, ℂ) :=
  ∑' k : SpatialFrequency,
    scalarPressureGradientCoefficient state coordinate k •
      UnitAddTorus.mFourier k

/-- Evaluation exposes the full differentiated Fourier population. -/
theorem reconstructedScalarTorusGradient_apply
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (q : SpatialTorus) :
    reconstructedScalarTorusGradient state coordinate q =
      ∑' k : SpatialFrequency,
        scalarPressureGradientCoefficient state coordinate k *
          UnitAddTorus.mFourier k q := by
  change (ContinuousMap.evalCLM ℂ q)
      (reconstructedScalarTorusGradient state coordinate) = _
  rw [reconstructedScalarTorusGradient,
    (ContinuousMap.evalCLM ℂ q).map_tsum
      (summable_scalarPressureGradientPassages state coordinate)]
  apply tsum_congr
  intro k
  rfl

/-- Every Fourier coefficient of the reconstructed complex gradient is its exact multiplier. -/
theorem torusSpatialFourierCoeff_reconstructedScalarTorusGradient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (n : SpatialFrequency) :
    torusSpatialFourierCoeff
        (reconstructedScalarTorusGradient state coordinate) n =
      scalarPressureGradientCoefficient state coordinate n := by
  change torusFourierCoefficientCLM n
      (reconstructedScalarTorusGradient state coordinate) = _
  rw [reconstructedScalarTorusGradient,
    (torusFourierCoefficientCLM n).map_tsum
      (summable_scalarPressureGradientPassages state coordinate)]
  simp only [torusFourierCoefficientCLM_apply,
    torusSpatialFourierCoeff_nativeCharacter]
  simpa only [eq_comm] using
    (tsum_ite_eq n
      (fun k ↦ scalarPressureGradientCoefficient state coordinate k))

/-- Scalar reality gives exact conjugate symmetry to every gradient coefficient. -/
theorem scalarPressureGradientCoefficient_neg_eq_conj
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    scalarPressureGradientCoefficient state coordinate (-k) =
      conj (scalarPressureGradientCoefficient state coordinate k) := by
  rw [scalarPressureGradientCoefficient,
    scalarPressureGradientCoefficient, hstate k,
    derivativeSymbol_neg_eq_conj, map_mul]
  simp only [map_mul]

/-- Consequently the reconstructed complex gradient is pointwise real. -/
theorem conj_reconstructedScalarTorusGradient_eq
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state)
    (coordinate : Fin 3) (q : SpatialTorus) :
    conj (reconstructedScalarTorusGradient state coordinate q) =
      reconstructedScalarTorusGradient state coordinate q := by
  rw [reconstructedScalarTorusGradient_apply, Complex.conj_tsum]
  calc
    (∑' k, conj (scalarPressureGradientCoefficient state coordinate k *
        UnitAddTorus.mFourier k q)) =
        ∑' k, scalarPressureGradientCoefficient state coordinate (-k) *
          UnitAddTorus.mFourier (-k) q := by
      apply tsum_congr
      intro k
      rw [map_mul,
        scalarPressureGradientCoefficient_neg_eq_conj hstate,
        UnitAddTorus.mFourier_neg]
    _ = ∑' k, scalarPressureGradientCoefficient state coordinate k *
          UnitAddTorus.mFourier k q := by
      rw [← (Equiv.neg SpatialFrequency).tsum_eq]
      simp

/-- The complex termwise derivative is exactly the reconstructed torus gradient pulled back to
Euclidean space. -/
theorem reconstructedComplexComponentFDeriv_scalar_apply_single
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) (x : Space) :
    reconstructedComplexComponentFDeriv (scalarNativeDiagonalVector state) 0 x
        (EuclideanSpace.single coordinate 1) =
      reconstructedScalarTorusGradient state coordinate
        (euclideanToSpatialTorus x) := by
  rw [reconstructedComplexComponentFDeriv_apply_single,
    reconstructedScalarTorusGradient_apply]
  apply tsum_congr
  intro k
  rw [euclideanFourierCharacter_eq_mFourier]
  rfl

/-- The real coordinate-gradient face reconstructed from the exact complex multiplier series. -/
def reconstructedRealPressureGradient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) : Space → ℝ :=
  fun x ↦
    (reconstructedScalarTorusGradient state coordinate
      (euclideanToSpatialTorus x)).re

theorem continuous_reconstructedRealPressureGradient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    Continuous (reconstructedRealPressureGradient state coordinate) :=
  Complex.continuous_re.comp
    ((reconstructedScalarTorusGradient state coordinate).continuous.comp
      euclideanToSpatialTorus_isOpenQuotientMap.continuous)

theorem isOnePeriodic_reconstructedRealPressureGradient
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    IsOnePeriodic (reconstructedRealPressureGradient state coordinate) := by
  intro x shiftedCoordinate
  unfold reconstructedRealPressureGradient
  rw [euclideanToSpatialTorus_add_single_one]

/-- The reconstructed gradient is the actual spatial derivative of the reconstructed `C¹`
pressure in the addressed basis direction. -/
theorem fderiv_reconstructedRealPressure_apply_single
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) (x : Space) :
    fderiv ℝ (reconstructedRealPressure state) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedRealPressureGradient state coordinate x := by
  have hcomplex := hasFDerivAt_reconstructedComplexComponent
    (scalarNativeDiagonalVector state) 0 x
  have hreal := Complex.reCLM.hasFDerivAt.comp x hcomplex
  have hreal' : HasFDerivAt (reconstructedRealPressure state)
      (Complex.reCLM.comp
        (reconstructedComplexComponentFDeriv
          (scalarNativeDiagonalVector state) 0 x)) x := by
    simpa [reconstructedRealPressure, reconstructedScalarTorusComplex,
      Function.comp_def] using hreal
  rw [hreal'.fderiv]
  change
    (reconstructedComplexComponentFDeriv
      (scalarNativeDiagonalVector state) 0 x
        (EuclideanSpace.single coordinate 1)).re = _
  rw [reconstructedComplexComponentFDeriv_scalar_apply_single]
  rfl

/-- Every Fourier coefficient of the actual real gradient face is the exact differentiated
native pressure coefficient. -/
theorem scalarSpatialFourierCoeff_reconstructedRealPressureGradient
    {state : PeriodicWeightedSobolev 3}
    (hstate : IsScalarWeightedFourierReal 3 state)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    scalarSpatialFourierCoeff
        (fun x ↦ (reconstructedRealPressureGradient state coordinate x : ℂ))
        (Complex.continuous_ofReal.comp
          (continuous_reconstructedRealPressureGradient state coordinate))
        (fun x shiftedCoordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
          (isOnePeriodic_reconstructedRealPressureGradient
            state coordinate x shiftedCoordinate)) k =
      scalarPressureGradientCoefficient state coordinate k := by
  let complexGradient : Space → ℂ := fun x ↦
    (reconstructedRealPressureGradient state coordinate x : ℂ)
  have hcontinuous : Continuous complexGradient :=
    Complex.continuous_ofReal.comp
      (continuous_reconstructedRealPressureGradient state coordinate)
  have hperiodic : IsOnePeriodic complexGradient := by
    intro x shiftedCoordinate
    exact congrArg (fun r : ℝ ↦ (r : ℂ))
      (isOnePeriodic_reconstructedRealPressureGradient
        state coordinate x shiftedCoordinate)
  have hofReal (x : Space) :
      complexGradient x = reconstructedScalarTorusGradient state coordinate
        (euclideanToSpatialTorus x) := by
    exact Complex.conj_eq_iff_re.mp
      (conj_reconstructedScalarTorusGradient_eq hstate coordinate
        (euclideanToSpatialTorus x))
  have hfield : periodicTorusLift complexGradient hcontinuous hperiodic =
      reconstructedScalarTorusGradient state coordinate := by
    ext q
    change complexGradient (euclideanRepresentative q) =
      reconstructedScalarTorusGradient state coordinate q
    rw [hofReal, euclideanToSpatialTorus_representative]
  change torusSpatialFourierCoeff
      (periodicTorusLift complexGradient hcontinuous hperiodic) k = _
  rw [hfield, torusSpatialFourierCoeff_reconstructedScalarTorusGradient]

/-! ## The actual reconstructed pressure of a weighted path -/

/-- The actual real pressure reconstructed from one weighted path face. -/
def weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    Space → ℝ :=
  reconstructedRealPressure (weightedNativePressure hT path t)

/-- Its addressed coordinate-gradient face. -/
def weightedReconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (coordinate : Fin 3) : Space → ℝ :=
  reconstructedRealPressureGradient
    (weightedNativePressure hT path t) coordinate

theorem norm_weightedNativePressure_le
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    ‖weightedNativePressure hT path t‖ ≤
      6 * ‖weightedUnprojectedDivergenceState hT path t‖ :=
  norm_nativePressureFromH2_le _

/-- The actual pressure is genuinely real `C¹`. -/
theorem contDiff_one_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    ContDiff ℝ 1 (weightedReconstructedPressure hT path t) :=
  contDiff_one_reconstructedRealPressure _

theorem continuous_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    Continuous (weightedReconstructedPressure hT path t) :=
  (contDiff_one_weightedReconstructedPressure hT path t).continuous

/-- The actual pressure is one-periodic in every spatial coordinate. -/
theorem isOnePeriodic_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    IsOnePeriodic (weightedReconstructedPressure hT path t) :=
  isOnePeriodic_reconstructedRealPressure _

theorem continuous_weightedReconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (coordinate : Fin 3) :
    Continuous (weightedReconstructedPressureGradient hT path t coordinate) :=
  continuous_reconstructedRealPressureGradient _ coordinate

theorem isOnePeriodic_weightedReconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (coordinate : Fin 3) :
    IsOnePeriodic (weightedReconstructedPressureGradient hT path t coordinate) :=
  isOnePeriodic_reconstructedRealPressureGradient _ coordinate

/-- The reconstructed gradient face is the actual derivative of the reconstructed pressure. -/
theorem fderiv_weightedReconstructedPressure_apply_single
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (coordinate : Fin 3) (x : Space) :
    fderiv ℝ (weightedReconstructedPressure hT path t) x
        (EuclideanSpace.single coordinate 1) =
      weightedReconstructedPressureGradient hT path t coordinate x :=
  fderiv_reconstructedRealPressure_apply_single _ coordinate x

/-- On a Fourier-real path, every Fourier coefficient of the reconstructed real pressure is
exactly the zero-gauge modal pressure coefficient. -/
theorem scalarSpatialFourierCoeff_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (t : ℝ)
    (k : SpatialFrequency) :
    scalarSpatialFourierCoeff
        (fun x ↦ (weightedReconstructedPressure hT path t x : ℂ))
        (Complex.continuous_ofReal.comp
          (continuous_weightedReconstructedPressure hT path t))
        (fun x coordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
          (isOnePeriodic_weightedReconstructedPressure
            hT path t x coordinate)) k =
      weightedPressureCoefficient hT path t k := by
  have hreal := isScalarWeightedFourierReal_weightedNativePressure hT hpath t
  simpa only [weightedReconstructedPressure,
    weightedSobolevCoefficients_weightedNativePressure] using
      (scalarSpatialFourierCoeff_reconstructedRealPressure hreal k)

/-- **Exact recovered gradient coefficient.**  Every coordinate Fourier coefficient of the
actual gradient face is exactly the corresponding component of the modal Leray complement. -/
theorem scalarSpatialFourierCoeff_weightedReconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (t : ℝ)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    scalarSpatialFourierCoeff
        (fun x ↦
          (weightedReconstructedPressureGradient hT path t coordinate x : ℂ))
        (Complex.continuous_ofReal.comp
          (continuous_weightedReconstructedPressureGradient
            hT path t coordinate))
        (fun x shiftedCoordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
          (isOnePeriodic_weightedReconstructedPressureGradient
            hT path t coordinate x shiftedCoordinate)) k =
      (lerayProjectMode k (weightedUnprojectedDivergenceMode hT path t k) -
        weightedUnprojectedDivergenceMode hT path t k) coordinate := by
  have hreal := isScalarWeightedFourierReal_weightedNativePressure hT hpath t
  have hcoefficient :=
    scalarSpatialFourierCoeff_reconstructedRealPressureGradient
      hreal coordinate k
  have hgradient := congrFun
    (pressureFrequencyGradient_weightedPressureCoefficient hT path t k)
    coordinate
  calc
    scalarSpatialFourierCoeff
          (fun x ↦
            (weightedReconstructedPressureGradient hT path t coordinate x : ℂ))
          (Complex.continuous_ofReal.comp
            (continuous_weightedReconstructedPressureGradient
              hT path t coordinate))
          (fun x shiftedCoordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
            (isOnePeriodic_weightedReconstructedPressureGradient
              hT path t coordinate x shiftedCoordinate)) k =
        scalarPressureGradientCoefficient
          (weightedNativePressure hT path t) coordinate k := by
            simpa only [weightedReconstructedPressureGradient] using hcoefficient
    _ = pressureFrequencyGradient k
          (weightedPressureCoefficient hT path t k) coordinate := by
            rw [scalarPressureGradientCoefficient,
              weightedSobolevCoefficients_weightedNativePressure]
            rfl
    _ = (lerayProjectMode k (weightedUnprojectedDivergenceMode hT path t k) -
          weightedUnprojectedDivergenceMode hT path t k) coordinate := hgradient

section Audit

#print axioms norm_nativePressureMultiplier_le_two
#print axioms nativePressureFromH2
#print axioms norm_nativePressureFromH2_le
#print axioms weightedSobolevCoefficients_nativePressureFromH2
#print axioms isScalarWeightedFourierReal_nativePressureFromH2
#print axioms weightedSobolevCoefficients_weightedNativePressure
#print axioms isScalarWeightedFourierReal_weightedNativePressure
#print axioms contDiff_one_reconstructedRealPressure
#print axioms scalarSpatialFourierCoeff_reconstructedRealPressure
#print axioms fderiv_reconstructedRealPressure_apply_single
#print axioms scalarSpatialFourierCoeff_reconstructedRealPressureGradient
#print axioms scalarSpatialFourierCoeff_weightedReconstructedPressure
#print axioms scalarSpatialFourierCoeff_weightedReconstructedPressureGradient

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
