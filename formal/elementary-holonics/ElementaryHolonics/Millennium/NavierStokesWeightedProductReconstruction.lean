import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
import ElementaryHolonics.Millennium.NavierStokesH3DivergenceBilinear

/-!
# Native Fourier multiplication reconstructs as physical pointwise multiplication

**[proved-derived]** The native `H³` product already retains the exact complete-lattice
convolution coefficient.  This owner closes the complementary physical receiver: uniform inverse
Fourier reconstruction intertwines that convolution with pointwise multiplication on the genuine
periodic torus.

The proof retains the complete ordered pair population.  It multiplies the two absolutely
summable character series, rebases `(p,q)` to the addressed output/input pair `(p+q,p)`, and only
then condenses the inner population to the existing convolution coefficient.  Thus equality is
not inferred merely from equal endpoints or from an unproved Fourier-uniqueness interface.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## A scalar native state and its exact synthesis -/

/-- One scalar coefficient population embedded in the existing three-component reconstruction
owner.  Component choice is apparatus only: every component carries the same scalar occurrence. -/
def scalarAsVectorWeighted
    (coeff : PeriodicSobolevCoefficients 3) : PeriodicVectorWeightedSobolev 3 :=
  fun _component ↦ coefficientWeightedRealization 3 coeff

@[simp]
theorem nativeUnweightedComponent_scalarAsVectorWeighted
    (coeff : PeriodicSobolevCoefficients 3) (component : Fin 3)
    (k : SpatialFrequency) :
    nativeUnweightedComponent (scalarAsVectorWeighted coeff) component k = coeff.1 k := by
  rw [nativeUnweightedComponent, scalarAsVectorWeighted,
    weightedSobolevCoefficients_coefficientWeightedRealization]

/-- Uniform complex synthesis of one scalar native `H³` population. -/
def reconstructedTorusComplexScalar
    (coeff : PeriodicSobolevCoefficients 3) : C(SpatialTorus, ℂ) :=
  reconstructedTorusComplexComponent (scalarAsVectorWeighted coeff) 0

/-- Evaluation exposes the complete scalar Fourier population. -/
theorem reconstructedTorusComplexScalar_apply
    (coeff : PeriodicSobolevCoefficients 3) (q : SpatialTorus) :
    reconstructedTorusComplexScalar coeff q =
      ∑' k : SpatialFrequency, coeff.1 k * UnitAddTorus.mFourier k q := by
  rw [reconstructedTorusComplexScalar,
    reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [nativeUnweightedComponent_scalarAsVectorWeighted]

/-- One scalar character passage at a fixed physical receiver point. -/
def scalarFourierPassage
    (coeff : PeriodicSobolevCoefficients 3) (q : SpatialTorus)
    (k : SpatialFrequency) : ℂ :=
  coeff.1 k * UnitAddTorus.mFourier k q

/-- Every scalar character passage population is absolutely summable. -/
theorem summable_norm_scalarFourierPassage
    (coeff : PeriodicSobolevCoefficients 3) (q : SpatialTorus) :
    Summable fun k : SpatialFrequency ↦ ‖scalarFourierPassage coeff q k‖ := by
  apply (summable_norm_periodicSobolevThreeCoefficient coeff).congr
  intro k
  have hcharacter : ‖UnitAddTorus.mFourier k q‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  rw [scalarFourierPassage, norm_mul, hcharacter, mul_one]

theorem summable_scalarFourierPassage
    (coeff : PeriodicSobolevCoefficients 3) (q : SpatialTorus) :
    Summable (scalarFourierPassage coeff q) :=
  Summable.of_norm (summable_norm_scalarFourierPassage coeff q)

/-! ## The addressed pair rebase -/

/-- Rebase an ordered input pair `(p,q)` to its output pin and retained left input `(p+q,p)`. -/
def frequencyPairToOutputInput :
    SpatialFrequency × SpatialFrequency ≃
      SpatialFrequency × SpatialFrequency where
  toFun pair := (pair.1 + pair.2, pair.1)
  invFun pair := (pair.2, pair.1 - pair.2)
  left_inv pair := by
    ext coordinate <;> simp
  right_inv pair := by
    ext coordinate <;> simp

/-- The convolution character passage at addressed output `k` and retained input `p`. -/
def scalarConvolutionCharacterPassage
    (left right : PeriodicSobolevCoefficients 3) (q : SpatialTorus)
    (pair : SpatialFrequency × SpatialFrequency) : ℂ :=
  left.1 pair.2 * right.1 (pair.1 - pair.2) *
    UnitAddTorus.mFourier pair.1 q

/-- The pair rebase preserves the complete character passage, not merely its output pin. -/
theorem scalarConvolutionCharacterPassage_frequencyPairToOutputInput
    (left right : PeriodicSobolevCoefficients 3) (q : SpatialTorus)
    (pair : SpatialFrequency × SpatialFrequency) :
    scalarConvolutionCharacterPassage left right q
        (frequencyPairToOutputInput pair) =
      scalarFourierPassage left q pair.1 * scalarFourierPassage right q pair.2 := by
  change left.1 pair.1 * right.1 ((pair.1 + pair.2) - pair.1) *
      UnitAddTorus.mFourier (pair.1 + pair.2) q =
    (left.1 pair.1 * UnitAddTorus.mFourier pair.1 q) *
      (right.1 pair.2 * UnitAddTorus.mFourier pair.2 q)
  rw [show pair.1 + pair.2 - pair.1 = pair.2 by abel,
    UnitAddTorus.mFourier_add]
  ring

/-- One fixed-output convolution fibre is absolutely summable. -/
theorem summable_norm_scalarH3ConvolutionTerms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p : SpatialFrequency ↦ ‖left.1 p * right.1 (k - p)‖ := by
  have hleft := summable_norm_periodicSobolevThreeCoefficient left
  have hbound : Summable fun p : SpatialFrequency ↦
      ‖left.1 p‖ * ‖right.1‖ := hleft.mul_right ‖right.1‖
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) right.1 (k - p))
    (norm_nonneg _)

theorem summable_scalarH3ConvolutionTerms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p : SpatialFrequency ↦ left.1 p * right.1 (k - p) :=
  Summable.of_norm (summable_norm_scalarH3ConvolutionTerms left right k)

/-- The complete output/input convolution-character population is summable. -/
theorem summable_scalarConvolutionCharacterPassage
    (left right : PeriodicSobolevCoefficients 3) (q : SpatialTorus) :
    Summable (scalarConvolutionCharacterPassage left right q) := by
  let pairProduct : SpatialFrequency × SpatialFrequency → ℂ := fun pair ↦
    scalarFourierPassage left q pair.1 * scalarFourierPassage right q pair.2
  have hpair : Summable pairProduct := by
    exact summable_mul_of_summable_norm
      (summable_norm_scalarFourierPassage left q)
      (summable_norm_scalarFourierPassage right q)
  apply frequencyPairToOutputInput.summable_iff.mp
  apply hpair.congr
  intro pair
  change pairProduct pair = scalarConvolutionCharacterPassage left right q
      (frequencyPairToOutputInput pair)
  exact (scalarConvolutionCharacterPassage_frequencyPairToOutputInput
    left right q pair).symm

/-! ## The physical product intertwiner -/

/-- The exact native convolution reconstructs as the actual pointwise product on the torus.

Every intermediate ordered pair is retained through the proof; the output convolution is reached
by the explicit `frequencyPairToOutputInput` rebase. -/
theorem reconstructedTorusComplexScalar_scalarH3Product
    (left right : PeriodicSobolevCoefficients 3) (q : SpatialTorus) :
    reconstructedTorusComplexScalar (scalarH3Product left right) q =
      reconstructedTorusComplexScalar left q *
        reconstructedTorusComplexScalar right q := by
  have hleft := summable_scalarFourierPassage left q
  have hright := summable_scalarFourierPassage right q
  let pairProduct : SpatialFrequency × SpatialFrequency → ℂ := fun pair ↦
    scalarFourierPassage left q pair.1 * scalarFourierPassage right q pair.2
  have hpair : Summable pairProduct := by
    exact summable_mul_of_summable_norm
      (summable_norm_scalarFourierPassage left q)
      (summable_norm_scalarFourierPassage right q)
  have hconvolution := summable_scalarConvolutionCharacterPassage left right q
  rw [reconstructedTorusComplexScalar_apply,
    reconstructedTorusComplexScalar_apply,
    reconstructedTorusComplexScalar_apply]
  symm
  calc
    (∑' p, left.1 p * UnitAddTorus.mFourier p q) *
        ∑' r, right.1 r * UnitAddTorus.mFourier r q =
      ∑' pair : SpatialFrequency × SpatialFrequency, pairProduct pair := by
        exact hleft.tsum_mul_tsum hright hpair
    _ = ∑' pair : SpatialFrequency × SpatialFrequency,
        scalarConvolutionCharacterPassage left right q
          (frequencyPairToOutputInput pair) := by
      apply tsum_congr
      intro pair
      exact (scalarConvolutionCharacterPassage_frequencyPairToOutputInput
        left right q pair).symm
    _ = ∑' pair : SpatialFrequency × SpatialFrequency,
        scalarConvolutionCharacterPassage left right q pair :=
      frequencyPairToOutputInput.tsum_eq
        (scalarConvolutionCharacterPassage left right q)
    _ = ∑' k : SpatialFrequency, ∑' p : SpatialFrequency,
        scalarConvolutionCharacterPassage left right q (k, p) :=
      hconvolution.tsum_prod
    _ = ∑' k : SpatialFrequency,
        (scalarH3Product left right).1 k * UnitAddTorus.mFourier k q := by
      apply tsum_congr
      intro k
      rw [show (∑' p : SpatialFrequency,
          scalarConvolutionCharacterPassage left right q (k, p)) =
          (∑' p : SpatialFrequency, left.1 p * right.1 (k - p)) *
            UnitAddTorus.mFourier k q by
        simp only [scalarConvolutionCharacterPassage]
        exact (summable_scalarH3ConvolutionTerms left right k).tsum_mul_right _]
      rw [scalarH3Product_apply]

/-! ## Spatial derivatives and the physical divergence face -/

/-- The exact Fréchet derivative population of one scalar reconstruction. -/
def reconstructedTorusComplexScalarFDeriv
    (coeff : PeriodicSobolevCoefficients 3) (x : Space) : Space →L[ℝ] ℂ :=
  reconstructedComplexComponentFDeriv (scalarAsVectorWeighted coeff) 0 x

/-- One scalar reconstruction has its complete termwise Fréchet derivative. -/
theorem hasFDerivAt_reconstructedTorusComplexScalar
    (coeff : PeriodicSobolevCoefficients 3) (x : Space) :
    HasFDerivAt
      (fun y : Space ↦ reconstructedTorusComplexScalar coeff
        (euclideanToSpatialTorus y))
      (reconstructedTorusComplexScalarFDeriv coeff x) x := by
  simpa only [reconstructedTorusComplexScalar,
    reconstructedTorusComplexScalarFDeriv] using
      hasFDerivAt_reconstructedComplexComponent
        (scalarAsVectorWeighted coeff) 0 x

/-- Applying the scalar derivative to one basis direction exposes the exact multiplier series. -/
theorem reconstructedTorusComplexScalarFDeriv_apply_single
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3) (x : Space) :
    reconstructedTorusComplexScalarFDeriv coeff x
        (EuclideanSpace.single coordinate 1) =
      ∑' k : SpatialFrequency,
        2 * Real.pi * Complex.I * (k coordinate) * coeff.1 k *
          euclideanFourierCharacter k x := by
  rw [reconstructedTorusComplexScalarFDeriv,
    reconstructedComplexComponentFDeriv_apply_single]
  apply tsum_congr
  intro k
  rw [nativeUnweightedComponent_scalarAsVectorWeighted]

/-- The reconstructed native product carries the actual physical product-rule derivative. -/
theorem reconstructedTorusComplexScalarFDeriv_scalarH3Product
    (left right : PeriodicSobolevCoefficients 3) (x : Space) :
    reconstructedTorusComplexScalarFDeriv (scalarH3Product left right) x =
      reconstructedTorusComplexScalar left (euclideanToSpatialTorus x) •
          reconstructedTorusComplexScalarFDeriv right x +
        reconstructedTorusComplexScalar right (euclideanToSpatialTorus x) •
          reconstructedTorusComplexScalarFDeriv left x := by
  have hproduct := hasFDerivAt_reconstructedTorusComplexScalar
    (scalarH3Product left right) x
  have hpointwise :=
    (hasFDerivAt_reconstructedTorusComplexScalar left x).mul
      (hasFDerivAt_reconstructedTorusComplexScalar right x)
  have hpointwiseOnNative :
      HasFDerivAt
        (fun y : Space ↦ reconstructedTorusComplexScalar (scalarH3Product left right)
          (euclideanToSpatialTorus y))
        (reconstructedTorusComplexScalar left (euclideanToSpatialTorus x) •
            reconstructedTorusComplexScalarFDeriv right x +
          reconstructedTorusComplexScalar right (euclideanToSpatialTorus x) •
            reconstructedTorusComplexScalarFDeriv left x) x := by
    apply hpointwise.congr_of_eventuallyEq
    filter_upwards [] with y
    exact reconstructedTorusComplexScalar_scalarH3Product left right
      (euclideanToSpatialTorus y)
  exact hproduct.unique hpointwiseOnNative

/-- One physical coordinate derivative of the native product is the exact pointwise Leibniz
face of the two reconstructed factors. -/
theorem reconstructedTorusComplexScalarFDeriv_scalarH3Product_apply_single
    (left right : PeriodicSobolevCoefficients 3)
    (coordinate : Fin 3) (x : Space) :
    reconstructedTorusComplexScalarFDeriv (scalarH3Product left right) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedTorusComplexScalar left (euclideanToSpatialTorus x) *
          reconstructedTorusComplexScalarFDeriv right x
            (EuclideanSpace.single coordinate 1) +
        reconstructedTorusComplexScalar right (euclideanToSpatialTorus x) *
          reconstructedTorusComplexScalarFDeriv left x
            (EuclideanSpace.single coordinate 1) := by
  rw [reconstructedTorusComplexScalarFDeriv_scalarH3Product]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

/-- Physical unprojected divergence of the reconstructed product population. -/
def reconstructedUnprojectedDivergenceComponent
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (x : Space) : ℂ :=
  ∑ coordinate : Fin 3,
    reconstructedTorusComplexScalarFDeriv
      (scalarH3Product (advecting coordinate) (transported output)) x
        (EuclideanSpace.single coordinate 1)

/-- The physical divergence face is the sum of the actual pointwise product-rule faces. -/
theorem reconstructedUnprojectedDivergenceComponent_eq_productRule
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (x : Space) :
    reconstructedUnprojectedDivergenceComponent advecting transported output x =
      ∑ coordinate : Fin 3,
        (reconstructedTorusComplexScalar (advecting coordinate)
            (euclideanToSpatialTorus x) *
              reconstructedTorusComplexScalarFDeriv (transported output) x
                (EuclideanSpace.single coordinate 1) +
          reconstructedTorusComplexScalar (transported output)
            (euclideanToSpatialTorus x) *
              reconstructedTorusComplexScalarFDeriv (advecting coordinate) x
                (EuclideanSpace.single coordinate 1)) := by
  unfold reconstructedUnprojectedDivergenceComponent
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  exact reconstructedTorusComplexScalarFDeriv_scalarH3Product_apply_single
    (advecting coordinate) (transported output) coordinate x

/-- Each coordinate product-derivative series is summable on the complete lattice. -/
theorem summable_scalarH3ProductDerivativeSeries
    (coordinate : Fin 3) (left right : PeriodicSobolevCoefficients 3) (x : Space) :
    Summable fun k : SpatialFrequency ↦
      2 * Real.pi * Complex.I * (k coordinate) *
        (scalarH3Product left right).1 k * euclideanFourierCharacter k x := by
  have h := summable_spatialDerivativeMultiplierSeries
    (scalarAsVectorWeighted (scalarH3Product left right)) 0 coordinate x
  apply h.congr
  intro k
  rw [nativeUnweightedComponent_scalarAsVectorWeighted]

/-- The physical divergence face is exactly the inverse Fourier population of the native `H²`
divergence coefficient.  This closes the coefficient-to-pointwise constitutive bridge. -/
theorem reconstructedUnprojectedDivergenceComponent_eq_fourierSeries
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (x : Space) :
    reconstructedUnprojectedDivergenceComponent advecting transported output x =
      ∑' k : SpatialFrequency,
        (h3DivergenceConvolution advecting transported output).1 k *
          euclideanFourierCharacter k x := by
  unfold reconstructedUnprojectedDivergenceComponent
  simp_rw [reconstructedTorusComplexScalarFDeriv_apply_single]
  have hsummable : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun k : SpatialFrequency ↦
        2 * Real.pi * Complex.I * (k coordinate) *
          (scalarH3Product (advecting coordinate) (transported output)).1 k *
            euclideanFourierCharacter k x := by
    intro coordinate _hcoordinate
    exact summable_scalarH3ProductDerivativeSeries coordinate
      (advecting coordinate) (transported output) x
  rw [← Summable.tsum_finsetSum hsummable]
  apply tsum_congr
  intro k
  rw [h3DivergenceConvolution_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [scalarH3Product_apply]

/-! ## Incompressibility turns divergence form into advection -/

/-- Embed an unweighted vector coefficient population in the native weighted owner without
changing any raw Fourier occurrence. -/
def vectorCoefficientsAsWeighted
    (state : PeriodicVectorSobolevThree) : PeriodicVectorWeightedSobolev 3 :=
  fun component ↦ coefficientWeightedRealization 3 (state component)

@[simp]
theorem nativeUnweightedComponent_vectorCoefficientsAsWeighted
    (state : PeriodicVectorSobolevThree) (component : Fin 3)
    (k : SpatialFrequency) :
    nativeUnweightedComponent (vectorCoefficientsAsWeighted state) component k =
      (state component).1 k := by
  rw [nativeUnweightedComponent, vectorCoefficientsAsWeighted,
    weightedSobolevCoefficients_coefficientWeightedRealization]

/-- A modewise incompressible coefficient population has zero complete physical complex trace. -/
theorem sum_reconstructedTorusComplexScalarFDeriv_eq_zero
    {state : PeriodicVectorSobolevThree}
    (hstate : IsModewiseDivergenceFree (vectorCoefficientsAsWeighted state))
    (x : Space) :
    (∑ component : Fin 3,
      reconstructedTorusComplexScalarFDeriv (state component) x
        (EuclideanSpace.single component 1)) = 0 := by
  simp_rw [reconstructedTorusComplexScalarFDeriv_apply_single]
  simpa only [nativeUnweightedComponent_vectorCoefficientsAsWeighted] using
    sum_tsum_spatialDerivativeMultiplier_eq_zero hstate x

/-- Under the actual modewise incompressibility fibre, the reconstructed divergence form is the
physical advective derivative.  The discarded face is proved zero, not omitted from the type. -/
theorem reconstructedUnprojectedDivergenceComponent_eq_advection
    {advecting : PeriodicVectorSobolevThree}
    (hadvecting :
      IsModewiseDivergenceFree (vectorCoefficientsAsWeighted advecting))
    (transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (x : Space) :
    reconstructedUnprojectedDivergenceComponent advecting transported output x =
      ∑ coordinate : Fin 3,
        reconstructedTorusComplexScalar (advecting coordinate)
            (euclideanToSpatialTorus x) *
          reconstructedTorusComplexScalarFDeriv (transported output) x
            (EuclideanSpace.single coordinate 1) := by
  rw [reconstructedUnprojectedDivergenceComponent_eq_productRule,
    Finset.sum_add_distrib]
  have htrace := sum_reconstructedTorusComplexScalarFDeriv_eq_zero
    hadvecting x
  calc
    (∑ coordinate : Fin 3,
        reconstructedTorusComplexScalar (advecting coordinate)
              (euclideanToSpatialTorus x) *
            reconstructedTorusComplexScalarFDeriv (transported output) x
              (EuclideanSpace.single coordinate 1)) +
        ∑ coordinate : Fin 3,
          reconstructedTorusComplexScalar (transported output)
                (euclideanToSpatialTorus x) *
              reconstructedTorusComplexScalarFDeriv (advecting coordinate) x
                (EuclideanSpace.single coordinate 1) =
      (∑ coordinate : Fin 3,
        reconstructedTorusComplexScalar (advecting coordinate)
              (euclideanToSpatialTorus x) *
            reconstructedTorusComplexScalarFDeriv (transported output) x
              (EuclideanSpace.single coordinate 1)) +
        reconstructedTorusComplexScalar (transported output)
            (euclideanToSpatialTorus x) *
          (∑ coordinate : Fin 3,
            reconstructedTorusComplexScalarFDeriv (advecting coordinate) x
              (EuclideanSpace.single coordinate 1)) := by
        rw [Finset.mul_sum]
    _ = _ := by rw [htrace, mul_zero, add_zero]

section Audit

#print axioms nativeUnweightedComponent_scalarAsVectorWeighted
#print axioms reconstructedTorusComplexScalar_apply
#print axioms frequencyPairToOutputInput
#print axioms summable_scalarConvolutionCharacterPassage
#print axioms reconstructedTorusComplexScalar_scalarH3Product
#print axioms reconstructedTorusComplexScalarFDeriv_scalarH3Product
#print axioms reconstructedUnprojectedDivergenceComponent_eq_productRule
#print axioms reconstructedUnprojectedDivergenceComponent_eq_fourierSeries
#print axioms sum_reconstructedTorusComplexScalarFDeriv_eq_zero
#print axioms reconstructedUnprojectedDivergenceComponent_eq_advection

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
