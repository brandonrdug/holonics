import ElementaryHolonics.Millennium.NavierStokesWeightedReality
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Full Fourier reconstruction from the native weighted H³ carrier

Every native weighted `H³` state unweights to an absolutely summable population on the complete
integer lattice.  This owner sums that population in the uniform norm on the genuine three-torus,
proves exact recovery of every addressed Fourier coefficient, and uses exact conjugate symmetry to
descend the complex synthesis to an actual real one-periodic Euclidean velocity field.

The owner also proves the missing endpoint first-moment theorem
`∑ k, |k_j| |û(k)| < ∞`, differentiates the full Fourier population uniformly in operator norm,
and returns an actual `C¹` velocity with exact basis-direction multiplier formulae.  No `C²`
regularity is claimed at the `H³` endpoint.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal NNReal
open Filter

namespace Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Scalar uniform synthesis -/

/-- One fixed Fourier receiver is a continuous linear functional on the uniform continuous-map
carrier. -/
def torusFourierCoefficientCLM (n : SpatialFrequency) :
    C(SpatialTorus, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun field ↦ torusSpatialFourierCoeff field n
      map_add' := fun left right ↦ torusSpatialFourierCoeff_add left right n
      map_smul' := by
        intro scalar field
        rw [torusSpatialFourierCoeff, torusSpatialFourierCoeff,
          UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with q
        change UnitAddTorus.mFourier (-n) q * (scalar * field q) =
          scalar * (UnitAddTorus.mFourier (-n) q * field q)
        ring }
    1 (fun field ↦ by
      change ‖∫ q : SpatialTorus,
        UnitAddTorus.mFourier (-n) q • field q‖ ≤ 1 * ‖field‖
      have hpoint : ∀ᵐ q : SpatialTorus,
          ‖UnitAddTorus.mFourier (-n) q • field q‖ ≤ ‖field‖ := by
        filter_upwards [] with q
        rw [norm_smul]
        have hcharacter : ‖UnitAddTorus.mFourier (-n) q‖ = 1 := by
          simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]
        rw [hcharacter, one_mul]
        exact field.norm_coe_le_norm q
      have hintegral := MeasureTheory.norm_integral_le_of_norm_le_const hpoint
      simpa using hintegral)

@[simp]
theorem torusFourierCoefficientCLM_apply
    (n : SpatialFrequency) (field : C(SpatialTorus, ℂ)) :
    torusFourierCoefficientCLM n field = torusSpatialFourierCoeff field n :=
  rfl

/-- One component's actual unweighted coefficient population. -/
def nativeUnweightedComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    SpatialFrequency → ℂ :=
  fun k ↦ (weightedSobolevCoefficients 3 (state component)).1 k

/-- Every component of a native weighted `H³` state is absolutely summable after unweighting. -/
theorem summable_norm_nativeUnweightedComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    Summable fun k ↦ ‖nativeUnweightedComponent state component k‖ :=
  summable_norm_periodicSobolevThreeCoefficient
    (weightedSobolevCoefficients 3 (state component))

/-- The character passages of one component are summable in the uniform norm. -/
theorem summable_nativeFourierPassages
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      nativeUnweightedComponent state component k • UnitAddTorus.mFourier k := by
  apply Summable.of_norm
  simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
    summable_norm_nativeUnweightedComponent state component

/-! ## The endpoint first lattice moment -/

/-- A one-dimensional fractional receiver whose threefold product has exactly the decay needed
for the first derivative of an `H³` Fourier population. -/
def fractionalCoordinateWeight (n : ℤ) : ℝ :=
  (1 + (n : ℝ) ^ 2) ^ (-(2 / 3 : ℝ))

theorem fractionalCoordinateWeight_nonneg (n : ℤ) :
    0 ≤ fractionalCoordinateWeight n := by
  exact Real.rpow_nonneg (by positivity) _

/-- The fractional coordinate receiver is summable on the complete integer line. -/
theorem summable_fractionalCoordinateWeight :
    Summable fractionalCoordinateWeight := by
  have hp : Summable fun n : ℤ ↦ |(n : ℝ)| ^ (-(4 / 3 : ℝ)) :=
    Real.summable_abs_int_rpow (by norm_num)
  let bound : ℤ → ℝ := fun n ↦ if n = 0 then 1 else |(n : ℝ)| ^ (-(4 / 3 : ℝ))
  have hbound : Summable bound := by
    apply hp.congr_cofinite
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [bound, hn]
  refine Summable.of_nonneg_of_le
    (fun n ↦ Real.rpow_nonneg (by positivity) _) (fun n ↦ ?_) hbound
  by_cases hn : n = 0
  · subst n
    simp [fractionalCoordinateWeight, bound]
  · rw [show bound n = |(n : ℝ)| ^ (-(4 / 3 : ℝ)) by simp [bound, hn]]
    have habs : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hsq : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := by rw [sq_abs]
    calc
      fractionalCoordinateWeight n ≤
          ((n : ℝ) ^ 2) ^ (-(2 / 3 : ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (by exact_mod_cast hn))
        · linarith
        · norm_num
      _ = |(n : ℝ)| ^ (-(4 / 3 : ℝ)) := by
        rw [hsq, ← Real.rpow_natCast]
        rw [← Real.rpow_mul (le_of_lt habs)]
        congr 2
        norm_num

private theorem summable_pair_fractionalCoordinateWeight :
    Summable fun k : ℤ × ℤ ↦
      fractionalCoordinateWeight k.1 * fractionalCoordinateWeight k.2 := by
  have hone : Summable fractionalCoordinateWeight := summable_fractionalCoordinateWeight
  exact hone.mul_of_nonneg hone fractionalCoordinateWeight_nonneg
    fractionalCoordinateWeight_nonneg

private theorem summable_triple_fractionalCoordinateWeight :
    Summable fun k : (ℤ × ℤ) × ℤ ↦
      (fractionalCoordinateWeight k.1.1 * fractionalCoordinateWeight k.1.2) *
        fractionalCoordinateWeight k.2 := by
  let pairWeight : ℤ × ℤ → ℝ := fun k ↦
    fractionalCoordinateWeight k.1 * fractionalCoordinateWeight k.2
  have hpair : Summable pairWeight := summable_pair_fractionalCoordinateWeight
  have hone : Summable fractionalCoordinateWeight := summable_fractionalCoordinateWeight
  exact hpair.mul_of_nonneg hone
    (fun k ↦ mul_nonneg (fractionalCoordinateWeight_nonneg k.1)
      (fractionalCoordinateWeight_nonneg k.2))
    fractionalCoordinateWeight_nonneg

/-- The full separable `2/3 + 2/3 + 2/3` reciprocal receiver on `ℤ³`. -/
def fractionalFirstMomentWeight (k : SpatialFrequency) : ℝ :=
  fractionalCoordinateWeight (k 0) *
    fractionalCoordinateWeight (k 1) *
      fractionalCoordinateWeight (k 2)

/-- The fractional first-moment receiver is summable on the complete spatial lattice. -/
theorem summable_fractionalFirstMomentWeight :
    Summable fractionalFirstMomentWeight := by
  have htranslated := frequencyTripleEquiv.summable_iff.mpr
    summable_triple_fractionalCoordinateWeight
  exact htranslated.congr (fun k ↦ by
    simp [Function.comp_apply, frequencyTripleEquiv,
      fractionalFirstMomentWeight])

/-- One addressed coordinate square divided by the exact `H³` weight is dominated by the
summable fractional receiver.  No coordinate or lattice mode is discarded. -/
theorem coordinate_sq_div_periodicSobolevWeight_three_le_fractional
    (coordinate : Fin 3) (k : SpatialFrequency) :
    (k coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 k ≤
      fractionalFirstMomentWeight k := by
  have hfrequency : 0 ≤ frequencySquared k := by
    unfold frequencySquared
    positivity
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hfrequencyEigen : frequencySquared k ≤ torusStokesEigenvalue k := by
    rw [torusStokesEigenvalue]
    exact le_mul_of_one_le_left hfrequency hscale
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  let total : ℝ := 1 + torusStokesEigenvalue k
  let product : ℝ :=
    (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) * (1 + (k 2 : ℝ) ^ 2)
  have htotal : 0 < total := by
    dsimp [total]
    linarith [torusStokesEigenvalue_nonneg k]
  have hcoordinateTotal : (k coordinate : ℝ) ^ 2 ≤ total := by
    dsimp [total]
    linarith
  have hfactor_le (address : Fin 3) :
      1 + (k address : ℝ) ^ 2 ≤ total := by
    dsimp [total]
    have haddress : (k address : ℝ) ^ 2 ≤ frequencySquared k := by
      unfold frequencySquared
      exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
        (Finset.mem_univ address)
    linarith
  have hproductPos : 0 < product := by
    dsimp [product]
    positivity
  have hproduct : product ≤ total ^ 3 := by
    dsimp [product]
    calc
      (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) *
          (1 + (k 2 : ℝ) ^ 2) ≤ total * total * total := by
        gcongr
        · exact hfactor_le 0
        · exact hfactor_le 1
        · exact hfactor_le 2
      _ = total ^ 3 := by ring
  have hrpow :
      (total ^ 3) ^ (-(2 / 3 : ℝ)) ≤ product ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hproductPos hproduct (by norm_num)
  have htotalRpow :
      (total ^ 3) ^ (-(2 / 3 : ℝ)) = (total ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt htotal)]
    norm_num [Real.rpow_neg_ofNat]
  have hproductRpow :
      product ^ (-(2 / 3 : ℝ)) = fractionalFirstMomentWeight k := by
    rw [fractionalFirstMomentWeight]
    simp only [fractionalCoordinateWeight]
    dsimp [product]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
  rw [periodicSobolevWeight]
  change (k coordinate : ℝ) ^ 2 / total ^ 3 ≤ _
  calc
    (k coordinate : ℝ) ^ 2 / total ^ 3 ≤ total / total ^ 3 := by
      exact div_le_div_of_nonneg_right hcoordinateTotal (pow_nonneg htotal.le 3)
    _ = (total ^ 2)⁻¹ := by field_simp
    _ = (total ^ 3) ^ (-(2 / 3 : ℝ)) := htotalRpow.symm
    _ ≤ product ^ (-(2 / 3 : ℝ)) := hrpow
    _ = fractionalFirstMomentWeight k := hproductRpow

/-- The exact coordinate reciprocal first moment of the `H³` weight is summable. -/
theorem summable_coordinate_sq_div_periodicSobolevWeight_three
    (coordinate : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      (k coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 k := by
  refine Summable.of_nonneg_of_le (fun k ↦ div_nonneg (sq_nonneg _)
    (periodicSobolevWeight_nonneg 3 k))
    (coordinate_sq_div_periodicSobolevWeight_three_le_fractional coordinate)
    summable_fractionalFirstMomentWeight

private theorem norm_coordinateReciprocalSobolevThreeSqrt_sq
    (coordinate : Fin 3) (k : SpatialFrequency) :
    ‖(((|(k coordinate : ℝ)| /
        Real.sqrt (periodicSobolevWeight 3 k) : ℝ) : ℂ))‖ ^ 2 =
      (k coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 k := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
    div_pow, sq_abs, Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k)]

/-- The addressed reciprocal first-derivative weight as a genuine Fourier `ℓ²` carrier. -/
def coordinateReciprocalSobolevThreeSqrt
    (coordinate : Fin 3) : PeriodicFourierL2 :=
  ⟨fun k ↦ (((|(k coordinate : ℝ)| /
      Real.sqrt (periodicSobolevWeight 3 k) : ℝ) : ℂ)), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two,
      norm_coordinateReciprocalSobolevThreeSqrt_sq] using
        summable_coordinate_sq_div_periodicSobolevWeight_three coordinate⟩

/-- The endpoint Fourier Cauchy--Schwarz estimate: every `H³` coefficient population retains
all first coordinate moments in `ℓ¹`. -/
theorem summable_coordinate_mul_norm_periodicSobolevThreeCoefficient
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      |(k coordinate : ℝ)| * ‖coeff.1 k‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hproduct := lp.summable_mul hholder
    (coordinateReciprocalSobolevThreeSqrt coordinate)
    (weightedSobolevThreeCoefficient coeff)
  apply hproduct.congr
  intro k
  have hweightPos : 0 < periodicSobolevWeight 3 k :=
    periodicSobolevWeight_pos 3 k
  have hsqrtPos : 0 < Real.sqrt (periodicSobolevWeight 3 k) :=
    Real.sqrt_pos.2 hweightPos
  simp only [coordinateReciprocalSobolevThreeSqrt,
    weightedSobolevThreeCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (abs_nonneg _),
    abs_of_pos hsqrtPos]
  field_simp

/-- Every native vector component has a summable addressed first Fourier moment. -/
theorem summable_coordinate_mul_norm_nativeUnweightedComponent
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      |(k coordinate : ℝ)| *
        ‖nativeUnweightedComponent state component k‖ :=
  summable_coordinate_mul_norm_periodicSobolevThreeCoefficient
    (weightedSobolevCoefficients 3 (state component)) coordinate

/-! ## Exact Euclidean character derivatives -/

/-- One addressed Euclidean factor of a spatial Fourier character. -/
def euclideanFourierFactor
    (k : SpatialFrequency) (coordinate : Fin 3) (x : Space) : ℂ :=
  fourier (k coordinate) ((x coordinate : ℝ) : UnitAddCircle)

/-- The full Euclidean Fourier character, retaining its three factor addresses. -/
def euclideanFourierCharacter (k : SpatialFrequency) (x : Space) : ℂ :=
  ∏ coordinate : Fin 3, euclideanFourierFactor k coordinate x

/-- The Euclidean character is exactly the genuine torus character pulled back through the
one-period quotient. -/
theorem euclideanFourierCharacter_eq_mFourier
    (k : SpatialFrequency) (x : Space) :
    euclideanFourierCharacter k x =
      UnitAddTorus.mFourier k (euclideanToSpatialTorus x) := by
  simp [euclideanFourierCharacter, euclideanFourierFactor,
    UnitAddTorus.mFourier, euclideanToSpatialTorus, piToSpatialTorus]

@[simp]
theorem norm_euclideanFourierFactor
    (k : SpatialFrequency) (coordinate : Fin 3) (x : Space) :
    ‖euclideanFourierFactor k coordinate x‖ = 1 := by
  rw [euclideanFourierFactor, fourier_apply]
  exact Circle.norm_coe _

@[simp]
theorem norm_euclideanFourierCharacter
    (k : SpatialFrequency) (x : Space) :
    ‖euclideanFourierCharacter k x‖ = 1 := by
  simp [euclideanFourierCharacter, norm_prod]

/-- The exact real Fréchet derivative of one addressed character factor. -/
def euclideanFourierFactorFDeriv
    (k : SpatialFrequency) (coordinate : Fin 3) (x : Space) :
    Space →L[ℝ] ℂ :=
  (EuclideanSpace.proj coordinate).smulRight
    (2 * Real.pi * Complex.I * (k coordinate) *
      euclideanFourierFactor k coordinate x)

/-- Mathlib's exact derivative of the circle Fourier character, transported through the
addressed Euclidean coordinate projection. -/
theorem hasFDerivAt_euclideanFourierFactor
    (k : SpatialFrequency) (coordinate : Fin 3) (x : Space) :
    HasFDerivAt (euclideanFourierFactor k coordinate)
      (euclideanFourierFactorFDeriv k coordinate x) x := by
  have h := (hasDerivAt_fourier (1 : ℝ) (k coordinate)
    (x coordinate : ℝ)).hasFDerivAt.comp x
      (EuclideanSpace.proj coordinate : Space →L[ℝ] ℝ).hasFDerivAt
  convert h using 1 <;> try rfl
  · ext direction
    simp [euclideanFourierFactor, euclideanFourierFactorFDeriv,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply]

/-- Product-rule derivative of the complete three-factor Euclidean character. -/
def euclideanFourierCharacterFDeriv
    (k : SpatialFrequency) (x : Space) : Space →L[ℝ] ℂ :=
  ∑ coordinate : Fin 3,
    (∏ other ∈ Finset.univ.erase coordinate,
      euclideanFourierFactor k other x) •
        euclideanFourierFactorFDeriv k coordinate x

/-- The complete character has the exact addressed product-rule derivative. -/
theorem hasFDerivAt_euclideanFourierCharacter
    (k : SpatialFrequency) (x : Space) :
    HasFDerivAt (euclideanFourierCharacter k)
      (euclideanFourierCharacterFDeriv k x) x := by
  have h := HasFDerivAt.finsetProd (u := Finset.univ)
    (fun coordinate _ ↦
      hasFDerivAt_euclideanFourierFactor k coordinate x)
  unfold euclideanFourierCharacter euclideanFourierCharacterFDeriv
  exact h

/-- Operator-norm bound for one addressed character-factor derivative. -/
theorem norm_euclideanFourierFactorFDeriv_le
    (k : SpatialFrequency) (coordinate : Fin 3) (x : Space) :
    ‖euclideanFourierFactorFDeriv k coordinate x‖ ≤
      2 * Real.pi * |(k coordinate : ℝ)| := by
  rw [euclideanFourierFactorFDeriv,
    ContinuousLinearMap.norm_smulRight_apply]
  have hproj :
      ‖(EuclideanSpace.proj coordinate : Space →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro direction
    simpa using PiLp.norm_apply_le direction coordinate
  calc
    ‖(EuclideanSpace.proj coordinate : Space →L[ℝ] ℝ)‖ *
        ‖2 * Real.pi * Complex.I * (k coordinate) *
          euclideanFourierFactor k coordinate x‖ ≤
        1 * ‖2 * Real.pi * Complex.I * (k coordinate) *
          euclideanFourierFactor k coordinate x‖ := by
      gcongr
    _ = 2 * Real.pi * |(k coordinate : ℝ)| := by
      simp only [one_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg, Complex.norm_I,
        Complex.norm_intCast, norm_euclideanFourierFactor, mul_one]

/-- Uniform first-derivative bound for a complete Fourier character. -/
theorem norm_euclideanFourierCharacterFDeriv_le
    (k : SpatialFrequency) (x : Space) :
    ‖euclideanFourierCharacterFDeriv k x‖ ≤
      2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)| := by
  rw [euclideanFourierCharacterFDeriv]
  calc
    ‖∑ coordinate : Fin 3,
        (∏ other ∈ Finset.univ.erase coordinate,
          euclideanFourierFactor k other x) •
            euclideanFourierFactorFDeriv k coordinate x‖ ≤
        ∑ coordinate : Fin 3,
          ‖(∏ other ∈ Finset.univ.erase coordinate,
            euclideanFourierFactor k other x) •
              euclideanFourierFactorFDeriv k coordinate x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ coordinate : Fin 3,
        (2 * Real.pi * |(k coordinate : ℝ)|) := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [norm_smul]
      simp only [norm_prod, norm_euclideanFourierFactor,
        Finset.prod_const_one, one_mul]
      exact norm_euclideanFourierFactorFDeriv_le k coordinate x
    _ = 2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)| := by
      rw [Finset.mul_sum]

/-- Applying the complete character derivative to one basis direction gives the exact Fourier
multiplier for that addressed coordinate. -/
theorem euclideanFourierCharacterFDeriv_apply_single
    (k : SpatialFrequency) (x : Space) (coordinate : Fin 3) :
    euclideanFourierCharacterFDeriv k x
        (EuclideanSpace.single coordinate 1) =
      2 * Real.pi * Complex.I * (k coordinate) *
        euclideanFourierCharacter k x := by
  unfold euclideanFourierCharacterFDeriv euclideanFourierFactorFDeriv
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_eq_single coordinate]
  · simp
    unfold euclideanFourierCharacter
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ coordinate)]
    ring
  · intro other _ hother
    simp [hother]
  · simp

/-- One actual Euclidean Fourier passage of a native component. -/
def euclideanNativeFourierPassage
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) : ℂ :=
  nativeUnweightedComponent state component k * euclideanFourierCharacter k x

/-- Exact derivative of one native Euclidean Fourier passage. -/
def euclideanNativeFourierPassageFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) : Space →L[ℝ] ℂ :=
  nativeUnweightedComponent state component k •
    euclideanFourierCharacterFDeriv k x

/-- Every native Euclidean Fourier passage carries its exact Fréchet derivative. -/
theorem hasFDerivAt_euclideanNativeFourierPassage
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) :
    HasFDerivAt (euclideanNativeFourierPassage state component k)
      (euclideanNativeFourierPassageFDeriv state component k x) x := by
  have h := (hasFDerivAt_euclideanFourierCharacter k x).const_mul
    (nativeUnweightedComponent state component k)
  unfold euclideanNativeFourierPassage euclideanNativeFourierPassageFDeriv
  exact h

/-- A differentiated native passage in one basis direction has exactly the addressed Fourier
multiplier. -/
theorem euclideanNativeFourierPassageFDeriv_apply_single
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (k : SpatialFrequency) (x : Space) :
    euclideanNativeFourierPassageFDeriv state component k x
        (EuclideanSpace.single coordinate 1) =
      2 * Real.pi * Complex.I * (k coordinate) *
        nativeUnweightedComponent state component k *
          euclideanFourierCharacter k x := by
  rw [euclideanNativeFourierPassageFDeriv,
    smul_apply,
    euclideanFourierCharacterFDeriv_apply_single]
  simp only [smul_eq_mul]
  ring

/-- The derivative of every individual native passage varies continuously in space. -/
theorem continuous_euclideanNativeFourierPassageFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    Continuous (euclideanNativeFourierPassageFDeriv state component k) := by
  unfold euclideanNativeFourierPassageFDeriv euclideanFourierCharacterFDeriv
    euclideanFourierFactorFDeriv euclideanFourierFactor
  fun_prop

/-- A summable modewise majorant for the full first derivative series. -/
def euclideanNativeFourierDerivativeBound
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) : ℝ :=
  2 * Real.pi * ∑ coordinate : Fin 3,
    |(k coordinate : ℝ)| *
      ‖nativeUnweightedComponent state component k‖

/-- The complete derivative majorant is summable over the full lattice. -/
theorem summable_euclideanNativeFourierDerivativeBound
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    Summable (euclideanNativeFourierDerivativeBound state component) := by
  have h0 := summable_coordinate_mul_norm_nativeUnweightedComponent
    state component (0 : Fin 3)
  have h1 := summable_coordinate_mul_norm_nativeUnweightedComponent
    state component (1 : Fin 3)
  have h2 := summable_coordinate_mul_norm_nativeUnweightedComponent
    state component (2 : Fin 3)
  apply Summable.mul_left (2 * Real.pi)
  simpa only [Fin.sum_univ_three] using (h0.add h1).add h2

/-- Every passage derivative is uniformly dominated by the summable first-moment receiver. -/
theorem norm_euclideanNativeFourierPassageFDeriv_le
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) :
    ‖euclideanNativeFourierPassageFDeriv state component k x‖ ≤
      euclideanNativeFourierDerivativeBound state component k := by
  rw [euclideanNativeFourierPassageFDeriv, norm_smul]
  unfold euclideanNativeFourierDerivativeBound
  calc
    ‖nativeUnweightedComponent state component k‖ *
        ‖euclideanFourierCharacterFDeriv k x‖ ≤
      ‖nativeUnweightedComponent state component k‖ *
        (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) := by
      gcongr
      exact norm_euclideanFourierCharacterFDeriv_le k x
    _ = 2 * Real.pi * ∑ coordinate : Fin 3,
        |(k coordinate : ℝ)| *
          ‖nativeUnweightedComponent state component k‖ := by
      simp only [Fin.sum_univ_three]
      ring

/-- Uniform full-lattice synthesis of one complex component. -/
def reconstructedTorusComplexComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    C(SpatialTorus, ℂ) :=
  ∑' k, nativeUnweightedComponent state component k • UnitAddTorus.mFourier k

/-- The complete character population sums to the reconstructed continuous component in the
uniform norm. -/
theorem hasSum_reconstructedTorusComplexComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    HasSum
      (fun k : SpatialFrequency ↦
        nativeUnweightedComponent state component k • UnitAddTorus.mFourier k)
      (reconstructedTorusComplexComponent state component) :=
  (summable_nativeFourierPassages state component).hasSum

/-- Evaluation exposes exactly the full pointwise Fourier series. -/
theorem reconstructedTorusComplexComponent_apply
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (q : SpatialTorus) :
    reconstructedTorusComplexComponent state component q =
      ∑' k, nativeUnweightedComponent state component k *
        UnitAddTorus.mFourier k q := by
  change (ContinuousMap.evalCLM ℂ q)
      (reconstructedTorusComplexComponent state component) = _
  rw [reconstructedTorusComplexComponent,
    (ContinuousMap.evalCLM ℂ q).map_tsum
      (summable_nativeFourierPassages state component)]
  apply tsum_congr
  intro k
  rfl

/-! ## Uniformly differentiated reconstruction -/

/-- The Euclidean native passages sum pointwise to the already-constructed uniform torus
component pulled back along the genuine quotient. -/
theorem tsum_euclideanNativeFourierPassage
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    (∑' k : SpatialFrequency,
        euclideanNativeFourierPassage state component k x) =
      reconstructedTorusComplexComponent state component
        (euclideanToSpatialTorus x) := by
  rw [reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [euclideanNativeFourierPassage,
    euclideanFourierCharacter_eq_mFourier]

/-- The derivative population of one reconstructed complex component. -/
def reconstructedComplexComponentFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    Space →L[ℝ] ℂ :=
  ∑' k : SpatialFrequency,
    euclideanNativeFourierPassageFDeriv state component k x

/-- At every spatial point, the complete operator-valued derivative population is summable. -/
theorem summable_euclideanNativeFourierPassageFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    Summable fun k : SpatialFrequency ↦
      euclideanNativeFourierPassageFDeriv state component k x :=
  Summable.of_norm_bounded
    (summable_euclideanNativeFourierDerivativeBound state component)
    (fun k ↦ norm_euclideanNativeFourierPassageFDeriv_le state component k x)

/-- The exact addressed Fourier-multiplier series is summable for every component, coordinate,
and spatial receiver point. -/
theorem summable_spatialDerivativeMultiplierSeries
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (x : Space) :
    Summable fun k : SpatialFrequency ↦
      2 * Real.pi * Complex.I * (k coordinate) *
        nativeUnweightedComponent state component k *
          euclideanFourierCharacter k x := by
  have h := (ContinuousLinearMap.apply ℝ ℂ
    (EuclideanSpace.single coordinate 1)).summable
      (summable_euclideanNativeFourierPassageFDeriv state component x)
  apply h.congr
  intro k
  exact euclideanNativeFourierPassageFDeriv_apply_single
    state component coordinate k x

/-- Evaluation of the reconstructed complex derivative exposes the full termwise derivative
series in the requested direction. -/
theorem reconstructedComplexComponentFDeriv_apply
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (x direction : Space) :
    reconstructedComplexComponentFDeriv state component x direction =
      ∑' k : SpatialFrequency,
        euclideanNativeFourierPassageFDeriv state component k x direction := by
  change (ContinuousLinearMap.apply ℝ ℂ direction)
      (reconstructedComplexComponentFDeriv state component x) = _
  rw [reconstructedComplexComponentFDeriv,
    (ContinuousLinearMap.apply ℝ ℂ direction).map_tsum
      (summable_euclideanNativeFourierPassageFDeriv state component x)]
  simp only [ContinuousLinearMap.apply_apply]

/-- In an addressed basis direction, the reconstructed complex derivative is precisely the full
Fourier multiplier series. -/
theorem reconstructedComplexComponentFDeriv_apply_single
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (x : Space) :
    reconstructedComplexComponentFDeriv state component x
        (EuclideanSpace.single coordinate 1) =
      ∑' k : SpatialFrequency,
        2 * Real.pi * Complex.I * (k coordinate) *
          nativeUnweightedComponent state component k *
            euclideanFourierCharacter k x := by
  rw [reconstructedComplexComponentFDeriv_apply]
  apply tsum_congr
  intro k
  exact euclideanNativeFourierPassageFDeriv_apply_single
    state component coordinate k x

/-- Termwise differentiation of the complete Euclidean Fourier series, with no truncation. -/
theorem hasFDerivAt_tsum_euclideanNativeFourierPassage
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    HasFDerivAt
      (fun y : Space ↦ ∑' k : SpatialFrequency,
        euclideanNativeFourierPassage state component k y)
      (reconstructedComplexComponentFDeriv state component x) x := by
  unfold reconstructedComplexComponentFDeriv
  refine hasFDerivAt_tsum (x₀ := (0 : Space))
    (summable_euclideanNativeFourierDerivativeBound state component)
    (fun k y ↦ hasFDerivAt_euclideanNativeFourierPassage state component k y)
    (fun k y ↦ norm_euclideanNativeFourierPassageFDeriv_le state component k y) ?_ x
  apply Summable.of_norm
  simpa only [euclideanNativeFourierPassage, norm_mul,
    norm_euclideanFourierCharacter, mul_one] using
      summable_norm_nativeUnweightedComponent state component

/-- The complete derivative population varies continuously, by uniform convergence in operator
norm against the summable first-moment receiver. -/
theorem continuous_reconstructedComplexComponentFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    Continuous (reconstructedComplexComponentFDeriv state component) := by
  unfold reconstructedComplexComponentFDeriv
  exact continuous_tsum
    (fun k ↦ continuous_euclideanNativeFourierPassageFDeriv state component k)
    (summable_euclideanNativeFourierDerivativeBound state component)
    (fun k x ↦ norm_euclideanNativeFourierPassageFDeriv_le state component k x)

/-- The full reconstructed complex component on Euclidean space is genuinely `C¹`. -/
theorem contDiff_one_reconstructedComplexComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    ContDiff ℝ 1 (fun x : Space ↦
      reconstructedTorusComplexComponent state component
        (euclideanToSpatialTorus x)) := by
  rw [show (fun x : Space ↦
      reconstructedTorusComplexComponent state component
        (euclideanToSpatialTorus x)) =
      (fun x : Space ↦ ∑' k : SpatialFrequency,
        euclideanNativeFourierPassage state component k x) by
    funext x
    exact (tsum_euclideanNativeFourierPassage state component x).symm]
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨reconstructedComplexComponentFDeriv state component,
      continuous_reconstructedComplexComponentFDeriv state component,
      hasFDerivAt_tsum_euclideanNativeFourierPassage state component⟩

/-- Exact termwise derivative of the actual reconstructed complex component, after identifying
the pointwise sum with the genuine torus pullback. -/
theorem hasFDerivAt_reconstructedComplexComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    HasFDerivAt
      (fun y : Space ↦ reconstructedTorusComplexComponent state component
        (euclideanToSpatialTorus y))
      (reconstructedComplexComponentFDeriv state component x) x := by
  rw [show (fun y : Space ↦
      reconstructedTorusComplexComponent state component
        (euclideanToSpatialTorus y)) =
      (fun y : Space ↦ ∑' k : SpatialFrequency,
        euclideanNativeFourierPassage state component k y) by
    funext y
    exact (tsum_euclideanNativeFourierPassage state component y).symm]
  exact hasFDerivAt_tsum_euclideanNativeFourierPassage state component x

/-! ## Exact coefficient recovery -/

/-- One character passage has precisely its addressed coefficient. -/
theorem torusSpatialFourierCoeff_nativeCharacter
    (coeff : SpatialFrequency → ℂ) (k n : SpatialFrequency) :
    torusSpatialFourierCoeff
        (fun q ↦ (coeff k • UnitAddTorus.mFourier k : C(SpatialTorus, ℂ)) q) n =
      if n = k then coeff k else 0 := by
  rw [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  change (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-n) q *
        (coeff k * UnitAddTorus.mFourier k q)) = _
  calc
    (∫ q : SpatialTorus,
        UnitAddTorus.mFourier (-n) q *
          (coeff k * UnitAddTorus.mFourier k q)) =
        ∫ q : SpatialTorus, coeff k *
          (UnitAddTorus.mFourier (-n) q * UnitAddTorus.mFourier k q) := by
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    _ = coeff k * (∫ q : SpatialTorus,
        UnitAddTorus.mFourier (-n) q * UnitAddTorus.mFourier k q) := by
      rw [integral_const_mul]
    _ = if n = k then coeff k else 0 := by
      rw [integral_mFourier_neg_mul_mFourier]
      by_cases hnk : n = k
      · simp [hnk]
      · simp [hnk]

/-- Every addressed Fourier coefficient of the uniform synthesis is exactly the source
unweighted coefficient; no mode is truncated or merged. -/
theorem torusSpatialFourierCoeff_reconstructedTorusComplexComponent
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (n : SpatialFrequency) :
    torusSpatialFourierCoeff
        (reconstructedTorusComplexComponent state component) n =
      nativeUnweightedComponent state component n := by
  change torusFourierCoefficientCLM n
      (reconstructedTorusComplexComponent state component) = _
  rw [reconstructedTorusComplexComponent,
    (torusFourierCoefficientCLM n).map_tsum
      (summable_nativeFourierPassages state component)]
  simp only [torusFourierCoefficientCLM_apply,
    torusSpatialFourierCoeff_nativeCharacter]
  simpa only [eq_comm] using
    (tsum_ite_eq n (fun k ↦ nativeUnweightedComponent state component k))

/-! ## Conjugate symmetry descends the complex synthesis to a real field -/

/-- The native reality incidence is exactly conjugate symmetry of every unweighted source
component. -/
theorem nativeUnweightedComponent_neg_eq_conj
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state)
    (component : Fin 3) (k : SpatialFrequency) :
    nativeUnweightedComponent state component (-k) =
      conj (nativeUnweightedComponent state component k) :=
  hstate component k

/-- Exact reindexing of the full character population proves that every reconstructed component
is pointwise fixed by complex conjugation. -/
theorem conj_reconstructedTorusComplexComponent_eq
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state)
    (component : Fin 3) (q : SpatialTorus) :
    conj (reconstructedTorusComplexComponent state component q) =
      reconstructedTorusComplexComponent state component q := by
  rw [reconstructedTorusComplexComponent_apply, Complex.conj_tsum]
  calc
    (∑' k, conj (nativeUnweightedComponent state component k *
        UnitAddTorus.mFourier k q)) =
        ∑' k, nativeUnweightedComponent state component (-k) *
          UnitAddTorus.mFourier (-k) q := by
      apply tsum_congr
      intro k
      rw [map_mul, nativeUnweightedComponent_neg_eq_conj hstate,
        UnitAddTorus.mFourier_neg]
    _ = ∑' k, nativeUnweightedComponent state component k *
        UnitAddTorus.mFourier k q := by
      rw [← (Equiv.neg SpatialFrequency).tsum_eq]
      simp

/-- Assemble all three uniformly reconstructed complex components without dropping their
component addresses. -/
def reconstructedTorusComplex
    (state : PeriodicVectorWeightedSobolev 3) : C(SpatialTorus, ComplexVector) where
  toFun q component := reconstructedTorusComplexComponent state component q
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro component
    exact (reconstructedTorusComplexComponent state component).continuous

@[simp]
theorem reconstructedTorusComplex_apply
    (state : PeriodicVectorWeightedSobolev 3)
    (q : SpatialTorus) (component : Fin 3) :
    reconstructedTorusComplex state q component =
      reconstructedTorusComplexComponent state component q :=
  rfl

/-- Take the real-coordinate face of the uniformly reconstructed complex torus field. -/
def reconstructedTorusReal
    (state : PeriodicVectorWeightedSobolev 3) : C(SpatialTorus, Space) where
  toFun q := vectorOfCoordinates
    (fun component ↦ (reconstructedTorusComplex state q component).re)
  continuous_toFun :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (by
      rw [continuous_pi_iff]
      intro component
      exact Complex.continuous_re.comp
        ((continuous_apply component).comp
          (reconstructedTorusComplex state).continuous))

@[simp]
theorem reconstructedTorusReal_apply
    (state : PeriodicVectorWeightedSobolev 3)
    (q : SpatialTorus) (component : Fin 3) :
    reconstructedTorusReal state q component =
      (reconstructedTorusComplex state q component).re :=
  rfl

/-- For a Fourier-real source, complexifying the returned real torus field recovers the complete
complex synthesis pointwise and componentwise. -/
theorem complexifySpace_reconstructedTorusReal
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state) (q : SpatialTorus) :
    complexifySpace (reconstructedTorusReal state q) =
      reconstructedTorusComplex state q := by
  funext component
  change
    ((reconstructedTorusComplex state q component).re : ℂ) =
      reconstructedTorusComplex state q component
  exact Complex.conj_eq_iff_re.mp
    (conj_reconstructedTorusComplexComponent_eq hstate component q)

/-! ## The actual continuous one-periodic Euclidean velocity -/

/-- Pull the real torus reconstruction back along the genuine quotient projection. -/
def reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3) : InitialVelocity :=
  fun x ↦ reconstructedTorusReal state (euclideanToSpatialTorus x)

/-- The reconstructed Euclidean velocity is honestly continuous. -/
theorem continuous_reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3) :
    Continuous (reconstructedVelocity state) :=
  (reconstructedTorusReal state).continuous.comp
    euclideanToSpatialTorus_isOpenQuotientMap.continuous

/-- The exact derivative of one real component, obtained by applying the real receiver to the
complete complex derivative population. -/
def reconstructedRealComponentFDeriv
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    Space →L[ℝ] ℝ :=
  Complex.reCLM.comp (reconstructedComplexComponentFDeriv state component x)

/-- Every reconstructed real component has the exact termwise Fourier derivative. -/
theorem hasFDerivAt_reconstructedVelocity_component
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    HasFDerivAt (fun y : Space ↦ reconstructedVelocity state y component)
      (reconstructedRealComponentFDeriv state component x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp x
    (hasFDerivAt_reconstructedComplexComponent state component x)
  simpa [reconstructedVelocity, reconstructedRealComponentFDeriv,
    reconstructedTorusReal_apply, reconstructedTorusComplex_apply,
    Function.comp_def] using h

/-- Every addressed component of the reconstructed velocity is genuinely `C¹`. -/
theorem contDiff_one_reconstructedVelocity_component
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    ContDiff ℝ 1 (fun x : Space ↦ reconstructedVelocity state x component) := by
  change ContDiff ℝ 1 (fun x : Space ↦
    (reconstructedTorusComplexComponent state component
      (euclideanToSpatialTorus x)).re)
  exact Complex.reCLM.contDiff.comp
    (contDiff_one_reconstructedComplexComponent state component)

/-- The actual reconstructed three-component velocity is `C¹` in space.  This is the exact
endpoint regularity supplied by the weighted `H³` carrier. -/
theorem contDiff_one_reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3) :
    ContDiff ℝ 1 (reconstructedVelocity state) := by
  rw [contDiff_piLp]
  exact contDiff_one_reconstructedVelocity_component state

/-- Evaluating the Fréchet derivative of a reconstructed component exposes the real receiver of
the complete differentiated Fourier population. -/
theorem fderiv_reconstructedVelocity_component_apply
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (x direction : Space) :
    fderiv ℝ (fun y : Space ↦ reconstructedVelocity state y component) x direction =
      reconstructedRealComponentFDeriv state component x direction := by
  have h := (hasFDerivAt_reconstructedVelocity_component state component x).fderiv
  rw [h]

/-- The addressed spatial partial derivative of one actual real velocity component is the real
receiver of the complete Fourier multiplier series. -/
theorem fderiv_reconstructedVelocity_component_apply_single
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (x : Space) :
    fderiv ℝ (fun y : Space ↦ reconstructedVelocity state y component) x
        (EuclideanSpace.single coordinate 1) =
      (∑' k : SpatialFrequency,
        2 * Real.pi * Complex.I * (k coordinate) *
          nativeUnweightedComponent state component k *
            euclideanFourierCharacter k x).re := by
  rw [fderiv_reconstructedVelocity_component_apply,
    reconstructedRealComponentFDeriv, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply,
    reconstructedComplexComponentFDeriv_apply_single]

/-- Projecting the vector Fréchet derivative agrees with the independently retained component
derivative. -/
theorem fderiv_reconstructedVelocity_apply_component
    (state : PeriodicVectorWeightedSobolev 3) (x direction : Space)
    (component : Fin 3) :
    (fderiv ℝ (reconstructedVelocity state) x direction) component =
      fderiv ℝ (fun y : Space ↦ reconstructedVelocity state y component) x direction := by
  have hvector := (contDiff_one_reconstructedVelocity state).differentiable
    (by norm_num) x
  have hproject :=
    (EuclideanSpace.proj component : Space →L[ℝ] ℝ).hasFDerivAt.comp x
      hvector.hasFDerivAt
  have heq := hproject.unique
    (hasFDerivAt_reconstructedVelocity_component state component x)
  have happ := congrArg (fun L : Space →L[ℝ] ℝ ↦ L direction) heq
  change (fderiv ℝ (reconstructedVelocity state) x direction) component =
    reconstructedRealComponentFDeriv state component x direction at happ
  rw [fderiv_reconstructedVelocity_component_apply]
  exact happ

/-- Adding one standard coordinate period does not change the genuine quotient point. -/
theorem euclideanToSpatialTorus_add_single_one
    (x : Space) (coordinate : Fin 3) :
    euclideanToSpatialTorus (x + EuclideanSpace.single coordinate 1) =
      euclideanToSpatialTorus x := by
  funext component
  by_cases hcomponent : component = coordinate
  · subst component
    simp [euclideanToSpatialTorus, piToSpatialTorus]
  · simp [euclideanToSpatialTorus, piToSpatialTorus, hcomponent]

/-- The reconstructed Euclidean velocity is one-periodic in every spatial coordinate. -/
theorem isOnePeriodic_reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3) :
    IsOnePeriodic (reconstructedVelocity state) := by
  intro x coordinate
  unfold reconstructedVelocity
  rw [euclideanToSpatialTorus_add_single_one]

/-- Descending the reconstructed Euclidean velocity returns exactly its source real torus field. -/
theorem periodicTorusLift_reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3) :
    periodicTorusLift (reconstructedVelocity state)
        (continuous_reconstructedVelocity state)
        (isOnePeriodic_reconstructedVelocity state) =
      reconstructedTorusReal state := by
  ext q component
  simp [periodicTorusLift, periodicTorusLiftFunction, reconstructedVelocity]

/-! ## Exact recovery on the actual real velocity -/

/-- Every addressed vector Fourier coefficient of the actual reconstructed real periodic velocity
is exactly the source native state's unweighted coefficient. -/
theorem vectorSpatialFourierCoeff_reconstructedVelocity
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state)
    (k : SpatialFrequency) :
    vectorSpatialFourierCoeff (reconstructedVelocity state)
        (continuous_reconstructedVelocity state)
        (isOnePeriodic_reconstructedVelocity state) k =
      fun component ↦ nativeUnweightedComponent state component k := by
  funext component
  rw [vectorSpatialFourierCoeff_apply]
  have hfield :
      periodicTorusLift
          (complexVelocityComponent (reconstructedVelocity state) component)
          (continuous_complexVelocityComponent
            (continuous_reconstructedVelocity state) component)
          (isOnePeriodic_complexVelocityComponent
            (isOnePeriodic_reconstructedVelocity state) component) =
        reconstructedTorusComplexComponent state component := by
    ext q
    change
      ((reconstructedTorusReal state
          (euclideanToSpatialTorus (euclideanRepresentative q)) component : ℝ) : ℂ) =
        reconstructedTorusComplexComponent state component q
    rw [euclideanToSpatialTorus_representative]
    exact congrFun (complexifySpace_reconstructedTorusReal hstate q) component
  rw [hfield, torusSpatialFourierCoeff_reconstructedTorusComplexComponent]

/- The preceding theorem can be read directly in the weighted owner's native coefficient chart. -/
theorem vectorSpatialFourierCoeff_reconstructedVelocity_eq_unweighted
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state)
    (k : SpatialFrequency) (component : Fin 3) :
    vectorSpatialFourierCoeff (reconstructedVelocity state)
        (continuous_reconstructedVelocity state)
        (isOnePeriodic_reconstructedVelocity state) k component =
      (weightedSobolevCoefficients 3 (state component)).1 k := by
  rw [vectorSpatialFourierCoeff_reconstructedVelocity hstate]
  rfl

section Audit

#print axioms contDiff_one_reconstructedVelocity
#print axioms fderiv_reconstructedVelocity_component_apply_single
#print axioms vectorSpatialFourierCoeff_reconstructedVelocity

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
