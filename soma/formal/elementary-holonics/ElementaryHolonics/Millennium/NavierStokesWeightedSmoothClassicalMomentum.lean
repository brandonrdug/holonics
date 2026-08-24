import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothPathTower
import ElementaryHolonics.Millennium.NavierStokesWeightedMildPhysicalSource
import ElementaryHolonics.Millennium.NavierStokesCurlCommutation

/-!
# Pointwise classical momentum from a coherent weighted smooth path tower

**[proved-derived]** The coherent all-order path tower supplies the missing spatial derivatives,
while the mild physical-source and pressure owners identify the two nonlinear Fourier
populations.  This owner proves the remaining synthesis equalities and composes them with the
already-returned strong interior time derivative.  The result is an exact pointwise periodic
momentum equation for every component of the actual reconstructed velocity.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal Laplacian

namespace Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildPhysicalSource
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The spatial Stokes synthesis -/

/-- The length-two diagonal derivative word. -/
def diagonalSecondWord (coordinate : Fin 3) : Fin 2 → Fin 3 :=
  fun _ ↦ coordinate

/-- Summing the exact diagonal second-derivative words returns the negative Stokes symbol. -/
theorem sum_orderedDerivativeMultiplier_diagonalSecondWord
    (k : SpatialFrequency) :
    (∑ coordinate : Fin 3,
      orderedDerivativeMultiplier 2 (diagonalSecondWord coordinate) k) =
        -(torusStokesEigenvalue k : ℂ) := by
  unfold torusStokesEigenvalue frequencySquared
  rw [Finset.mul_sum, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  simp [diagonalSecondWord, orderedDerivativeMultiplier,
    coordinateFourierMultiplier]
  simp only [mul_pow, Complex.I_sq]
  ring

/-- The empty-word reconstruction from every lift is exactly the complexification of the common
actual real velocity face. -/
theorem reconstructedFiniteOrderComplexComponent_zero_eq_weightedVelocity
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    reconstructedFiniteOrderComplexComponent
        m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i)
          (tower.lift m t) component x =
      (weightedReconstructedVelocity hT base t.1 x component : ℂ) := by
  change reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree
        m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) (tower.lift m t))
      component (euclideanToSpatialTorus x) =
    ((reconstructedTorusReal (weightedPathExtension hT base t.1)
      (euclideanToSpatialTorus x) component : ℝ) : ℂ)
  rw [finiteOrderVectorDerivativeToThree_zero, tower.restrict_lift,
    weightedPathExtension_of_mem hT base t.2]
  have hcomplex := congrFun
    (complexifySpace_reconstructedTorusReal
      (hreal t) (euclideanToSpatialTorus x)) component
  simpa only [reconstructedTorusComplex_apply] using hcomplex.symm

/-- Two actual diagonal Fréchet derivatives of the lift's empty-word reconstruction are exactly
the reconstructed length-two diagonal word. -/
theorem secondFDeriv_reconstructedFiniteOrderComplexComponent_zero
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ (fderiv ℝ
        (reconstructedFiniteOrderComplexComponent
          2 0 (by omega) (fun i ↦ Fin.elim0 i)
            (tower.lift 2 t) component)) x
        (EuclideanSpace.single coordinate 1)
        (EuclideanSpace.single coordinate 1) =
      reconstructedFiniteOrderComplexComponent
        2 2 (by omega) (diagonalSecondWord coordinate)
          (tower.lift 2 t) component x := by
  let emptyWord : Fin 0 → Fin 3 := fun i ↦ Fin.elim0 i
  let oneWord : Fin 1 → Fin 3 := Fin.cons coordinate emptyWord
  let f₀ : Space → ℂ := reconstructedFiniteOrderComplexComponent
    2 0 (by omega) emptyWord (tower.lift 2 t) component
  let f₁ : Space → ℂ := reconstructedFiniteOrderComplexComponent
    2 1 (by omega) oneWord (tower.lift 2 t) component
  let e : Space := EuclideanSpace.single coordinate 1
  have hf₀ : ContDiff ℝ 3 f₀ := by
    simpa only [f₀, reconstructedHigherOrderComplexComponent] using
      contDiff_reconstructedHigherOrderComplexComponent
        2 (tower.lift 2 t) component
  have hDf₀ : DifferentiableAt ℝ (fderiv ℝ f₀) x :=
    (hf₀.fderiv_right (m := 2) (by norm_num)).differentiable
      (by norm_num) x
  have happly := fderiv_clm_apply hDf₀ (differentiableAt_const e)
  have hdiagonal :
      fderiv ℝ (fun y ↦ fderiv ℝ f₀ y e) x e =
        fderiv ℝ (fderiv ℝ f₀) x e e := by
    rw [happly]
    simp
  have hfirst : (fun y ↦ fderiv ℝ f₀ y e) = f₁ := by
    funext y
    exact tower.fderiv_finiteDerivative_apply_single
      2 0 (by omega) emptyWord t component coordinate y
  change fderiv ℝ (fderiv ℝ f₀) x e e = _
  calc
    fderiv ℝ (fderiv ℝ f₀) x e e =
        fderiv ℝ (fun y ↦ fderiv ℝ f₀ y e) x e := hdiagonal.symm
    _ = fderiv ℝ f₁ x e := by rw [hfirst]
    _ = reconstructedFiniteOrderComplexComponent
          2 2 (by omega) (Fin.cons coordinate oneWord)
            (tower.lift 2 t) component x :=
      tower.fderiv_finiteDerivative_apply_single
        2 1 (by omega) oneWord t component coordinate x
    _ = reconstructedFiniteOrderComplexComponent
          2 2 (by omega) (diagonalSecondWord coordinate)
            (tower.lift 2 t) component x := by
      congr 2
      funext i
      fin_cases i <;> rfl

/-- The actual complexified velocity Laplacian is the finite sum of the tower's exact diagonal
second-derivative reconstructions. -/
theorem laplacian_weightedReconstructedVelocity_component_eq_secondWords
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    Δ (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x =
      ∑ coordinate : Fin 3,
        reconstructedFiniteOrderComplexComponent
          2 2 (by omega) (diagonalSecondWord coordinate)
            (tower.lift 2 t) component x := by
  have hfield :
      (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) =
      reconstructedFiniteOrderComplexComponent
        2 0 (by omega) (fun i ↦ Fin.elim0 i)
          (tower.lift 2 t) component := by
    funext y
    exact (reconstructedFiniteOrderComplexComponent_zero_eq_weightedVelocity
      hT tower hreal 2 t component y).symm
  rw [hfield, laplacian_eq_sum_secondFDeriv]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [EuclideanSpace.basisFun_apply]
  exact secondFDeriv_reconstructedFiniteOrderComplexComponent_zero
    tower t component coordinate x

/-- The finite population of diagonal second-word reconstructions is exactly the complete
negative-Stokes Fourier synthesis of the common base coefficients. -/
theorem sum_secondWords_eq_stokesFourierSeries
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    (∑ coordinate : Fin 3,
        reconstructedFiniteOrderComplexComponent
          2 2 (by omega) (diagonalSecondWord coordinate)
            (tower.lift 2 t) component x) =
      ∑' k : SpatialFrequency,
        (-(torusStokesEigenvalue k : ℂ)) *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x := by
  have hsummable : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable (fun k : SpatialFrequency ↦
        orderedDerivativeMultiplier 2 (diagonalSecondWord coordinate) k *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x) := by
    intro coordinate _hcoordinate
    let derivativeState := finiteOrderVectorDerivativeToThree
      2 2 (by omega) (diagonalSecondWord coordinate) (tower.lift 2 t)
    have hnative := summable_norm_nativeUnweightedComponent derivativeState component
    apply Summable.of_norm
    apply hnative.congr
    intro k
    rw [norm_mul, norm_euclideanFourierCharacter, mul_one]
    change ‖(weightedSobolevCoefficients 3 (derivativeState component)).1 k‖ =
      ‖(orderedDerivativeMultiplier 2 (diagonalSecondWord coordinate) k *
        (weightedSobolevCoefficients 3 (base t component)).1 k)‖
    rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
      tower.weightedSobolevCoefficients_lift_eq_base]
  change (∑ coordinate : Fin 3,
      reconstructedTorusComplexComponent
        (finiteOrderVectorDerivativeToThree
          2 2 (by omega) (diagonalSecondWord coordinate) (tower.lift 2 t))
        component (euclideanToSpatialTorus x)) = _
  simp_rw [reconstructedTorusComplexComponent_apply, nativeUnweightedComponent,
    weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    tower.weightedSobolevCoefficients_lift_eq_base,
    ← euclideanFourierCharacter_eq_mFourier]
  rw [← Summable.tsum_finsetSum hsummable]
  apply tsum_congr
  intro k
  calc
    ∑ coordinate : Fin 3,
        orderedDerivativeMultiplier 2 (diagonalSecondWord coordinate) k *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x =
      (∑ coordinate : Fin 3,
        orderedDerivativeMultiplier 2 (diagonalSecondWord coordinate) k) *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = (-(torusStokesEigenvalue k : ℂ)) *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x := by
      rw [sum_orderedDerivativeMultiplier_diagonalSecondWord]

/-- The complete negative-Stokes Fourier population is exactly the spatial Laplacian of the
actual complexified velocity component. -/
theorem stokesFourierSeries_eq_laplacian_weightedReconstructedVelocity_component
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    (∑' k : SpatialFrequency,
        (-(torusStokesEigenvalue k : ℂ)) *
          (weightedSobolevCoefficients 3 (base t component)).1 k *
            euclideanFourierCharacter k x) =
      Δ (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x := by
  rw [laplacian_weightedReconstructedVelocity_component_eq_secondWords
    hT tower hreal t component x]
  exact (sum_secondWords_eq_stokesFourierSeries
    tower t component x).symm

/-- **Exact viscous Fourier-to-physical identification.**  The viscous population appearing in
the differentiated mild equation is viscosity times the actual spatial Laplacian. -/
theorem viscousFourierSeries_eq_laplacian
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (nu : ℝ≥0) (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    (∑' k : SpatialFrequency,
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient
            hT base component k t.1) * euclideanFourierCharacter k x) =
      (nu : ℂ) *
        Δ (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x := by
  calc
    (∑' k : SpatialFrequency,
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient
            hT base component k t.1) * euclideanFourierCharacter k x) =
      ∑' k : SpatialFrequency,
        (nu : ℂ) *
          ((-(torusStokesEigenvalue k : ℂ)) *
            (weightedSobolevCoefficients 3 (base t component)).1 k *
              euclideanFourierCharacter k x) := by
        apply tsum_congr
        intro k
        rw [weightedReconstructedVelocityCoefficient_eq_base
          hT hreal component k t.2]
        push_cast
        ring
    _ = (nu : ℂ) *
        (∑' k : SpatialFrequency,
          (-(torusStokesEigenvalue k : ℂ)) *
            (weightedSobolevCoefficients 3 (base t component)).1 k *
              euclideanFourierCharacter k x) := tsum_mul_left
    _ = (nu : ℂ) *
        Δ (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x := by
      rw [stokesFourierSeries_eq_laplacian_weightedReconstructedVelocity_component
        hT tower hreal t component x]

/-- The complete negative-Stokes population is summable under the tower's `H⁸` face. -/
theorem CoherentWeightedSmoothPathTower.summable_stokesFourierSeries
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      (-(torusStokesEigenvalue k : ℂ)) *
        (weightedSobolevCoefficients 3 (base t component)).1 k *
          euclideanFourierCharacter k x) := by
  have hmajorant := summable_periodicSobolevWeight_three_inv.mul_left
    ‖tower.lift 5‖
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_) hmajorant
  rw [norm_mul, norm_mul, norm_euclideanFourierCharacter, mul_one,
    norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (torusStokesEigenvalue_nonneg k)]
  exact tower.stokes_mul_norm_baseCoefficient_le t component k

/-- The viscosity-scaled population using the actual reconstructed field coefficients is
summable at every addressed face. -/
theorem CoherentWeightedSmoothPathTower.summable_viscousFourierSeries
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (nu : ℝ≥0) (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient hT base component k t.1) *
        euclideanFourierCharacter k x) := by
  have hscaled :=
    (CoherentWeightedSmoothPathTower.summable_stokesFourierSeries
      tower t component x).mul_left (nu : ℂ)
  apply hscaled.congr
  intro k
  rw [weightedReconstructedVelocityCoefficient_eq_base
    hT hreal component k t.2]
  push_cast
  ring

/-! ## The nonlinear source and pressure synthesis -/

/-- The complete Fourier population of one unprojected quadratic divergence component is
summable at every physical receiver. -/
theorem summable_h3DivergenceConvolution_mul_character
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      (h3DivergenceConvolution advecting transported output).1 k *
        euclideanFourierCharacter k x) := by
  have hcoordinates : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable (fun k : SpatialFrequency ↦
        2 * Real.pi * Complex.I * (k coordinate) *
          (scalarH3Product (advecting coordinate) (transported output)).1 k *
            euclideanFourierCharacter k x) := by
    intro coordinate _hcoordinate
    exact summable_scalarH3ProductDerivativeSeries coordinate
      (advecting coordinate) (transported output) x
  have hsum := summable_sum hcoordinates
  apply hsum.congr
  intro k
  rw [h3DivergenceConvolution_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [scalarH3Product_apply]

/-- The actual unprojected quadratic source sequence is summable along every addressed path
face. -/
theorem summable_weightedUnprojectedDivergenceMode_mul_character
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T)
    (t : ℝ) (output : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      weightedUnprojectedDivergenceMode hT base t k output *
        euclideanFourierCharacter k x) := by
  exact summable_h3DivergenceConvolution_mul_character
    (unweightedVectorThree (weightedPathExtension hT base t))
    (unweightedVectorThree (weightedPathExtension hT base t)) output x

/-- The complete modal Leray-complement population is exactly the actual reconstructed real
pressure-gradient component, viewed in the complex coefficient receiver. -/
theorem pressureComplementFourierSeries_eq_reconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (t : ℝ) (component : Fin 3) (x : Space) :
    (∑' k : SpatialFrequency,
      (lerayProjectMode k
          (weightedUnprojectedDivergenceMode hT base t k) -
        weightedUnprojectedDivergenceMode hT base t k) component *
          euclideanFourierCharacter k x) =
      (weightedReconstructedPressureGradient
        hT base t component x : ℂ) := by
  let pressureState := weightedNativePressure hT base t
  let q := euclideanToSpatialTorus x
  have hpressureReal :
      ((reconstructedScalarTorusGradient pressureState component q).re : ℂ) =
        reconstructedScalarTorusGradient pressureState component q :=
    Complex.conj_eq_iff_re.mp
      (conj_reconstructedScalarTorusGradient_eq
        (isScalarWeightedFourierReal_weightedNativePressure hT hreal t)
        component q)
  change (∑' k : SpatialFrequency,
      (lerayProjectMode k
          (weightedUnprojectedDivergenceMode hT base t k) -
        weightedUnprojectedDivergenceMode hT base t k) component *
          euclideanFourierCharacter k x) =
    ((reconstructedScalarTorusGradient pressureState component q).re : ℂ)
  rw [hpressureReal, reconstructedScalarTorusGradient_apply]
  apply tsum_congr
  intro k
  rw [← euclideanFourierCharacter_eq_mFourier]
  congr 1
  change (lerayProjectMode k
        (weightedUnprojectedDivergenceMode hT base t k) -
      weightedUnprojectedDivergenceMode hT base t k) component =
    pressureFrequencyGradient k
      ((weightedSobolevCoefficients 3 pressureState).1 k) component
  rw [weightedSobolevCoefficients_weightedNativePressure]
  exact (congrFun
    (pressureFrequencyGradient_weightedPressureCoefficient hT base t k)
    component).symm

/-- The modal pressure-complement Fourier population is summable at every physical receiver. -/
theorem summable_pressureComplement_mul_character
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T)
    (t : ℝ) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      (lerayProjectMode k
          (weightedUnprojectedDivergenceMode hT base t k) -
        weightedUnprojectedDivergenceMode hT base t k) component *
          euclideanFourierCharacter k x) := by
  let pressureState := weightedNativePressure hT base t
  have hmoment :=
    summable_coordinate_mul_norm_nativeUnweightedComponent
      (scalarNativeDiagonalVector pressureState) 0 component
  have hscaled := hmoment.mul_left (2 * Real.pi)
  have hgradient : Summable (fun k : SpatialFrequency ↦
      scalarPressureGradientCoefficient pressureState component k *
        euclideanFourierCharacter k x) := by
    apply Summable.of_norm
    apply hscaled.congr
    intro k
    simp only [norm_mul, norm_euclideanFourierCharacter, mul_one,
      scalarPressureGradientCoefficient, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, Complex.norm_intCast,
      nativeUnweightedComponent_scalarNativeDiagonalVector]
    ring
  apply hgradient.congr
  intro k
  congr 1
  change pressureFrequencyGradient k
      ((weightedSobolevCoefficients 3 pressureState).1 k) component =
    (lerayProjectMode k
        (weightedUnprojectedDivergenceMode hT base t k) -
      weightedUnprojectedDivergenceMode hT base t k) component
  rw [weightedSobolevCoefficients_weightedNativePressure]
  exact congrFun
    (pressureFrequencyGradient_weightedPressureCoefficient hT base t k)
    component

/-- The projected quadratic source population is summable after splitting it into the actual
unprojected divergence and Leray-complement populations. -/
theorem summable_projectedSourceFourierSeries
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k *
          euclideanFourierCharacter k x) := by
  have hmode (k : SpatialFrequency) :
      weightedUnprojectedDivergenceMode hT base t.1 k =
        (fun output ↦
          (h3DivergenceConvolution
            (unweightedVectorThree (base t))
            (unweightedVectorThree (base t)) output).1 k) := by
    funext output
    rw [weightedUnprojectedDivergenceMode_apply,
      weightedPathExtension_of_mem hT base t.2]
  have hprojected (k : SpatialFrequency) :
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k =
      lerayProjectMode k
        (weightedUnprojectedDivergenceMode hT base t.1 k) component := by
    have hcoefficient := congrFun
      (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) k) component
    simpa only [vectorCoefficientAt, periodicVectorSobolevTwoUnderlying,
      hmode k] using hcoefficient
  have hunprojected :=
    summable_weightedUnprojectedDivergenceMode_mul_character
      hT base t.1 component x
  have hpressure :=
    summable_pressureComplement_mul_character hT base t.1 component x
  apply (hunprojected.add hpressure).congr
  intro k
  rw [hprojected]
  simp only [Pi.sub_apply]
  ring

/-- **Exact projected-source Fourier-to-physical identification.**  The projected quadratic
population is the actual unprojected product-rule divergence plus the actual reconstructed
pressure-gradient component. -/
theorem projectedSourceFourierSeries_eq_physicalQuadratic_add_pressureGradient
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    (∑' k : SpatialFrequency,
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k *
          euclideanFourierCharacter k x) =
      physicalUnprojectedQuadraticComponent (base t) component x +
        (weightedReconstructedPressureGradient
          hT base t.1 component x : ℂ) := by
  have hmode (k : SpatialFrequency) :
      weightedUnprojectedDivergenceMode hT base t.1 k =
        (fun output ↦
          (h3DivergenceConvolution
            (unweightedVectorThree (base t))
            (unweightedVectorThree (base t)) output).1 k) := by
    funext output
    rw [weightedUnprojectedDivergenceMode_apply,
      weightedPathExtension_of_mem hT base t.2]
  have hprojected (k : SpatialFrequency) :
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k =
      lerayProjectMode k
        (weightedUnprojectedDivergenceMode hT base t.1 k) component := by
    have hcoefficient := congrFun
      (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) k) component
    simpa only [vectorCoefficientAt, periodicVectorSobolevTwoUnderlying,
      hmode k] using hcoefficient
  have hunprojected :=
    summable_weightedUnprojectedDivergenceMode_mul_character
      hT base t.1 component x
  have hpressure :=
    summable_pressureComplement_mul_character hT base t.1 component x
  calc
    (∑' k : SpatialFrequency,
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k *
          euclideanFourierCharacter k x) =
      ∑' k : SpatialFrequency,
        (weightedUnprojectedDivergenceMode hT base t.1 k component +
          (lerayProjectMode k
              (weightedUnprojectedDivergenceMode hT base t.1 k) -
            weightedUnprojectedDivergenceMode hT base t.1 k) component) *
              euclideanFourierCharacter k x := by
        apply tsum_congr
        intro k
        rw [hprojected]
        simp only [Pi.sub_apply]
        ring
    _ = (∑' k : SpatialFrequency,
          weightedUnprojectedDivergenceMode hT base t.1 k component *
            euclideanFourierCharacter k x) +
        ∑' k : SpatialFrequency,
          (lerayProjectMode k
              (weightedUnprojectedDivergenceMode hT base t.1 k) -
            weightedUnprojectedDivergenceMode hT base t.1 k) component *
              euclideanFourierCharacter k x := by
        rw [← hunprojected.tsum_add hpressure]
        apply tsum_congr
        intro k
        ring
    _ = physicalUnprojectedQuadraticComponent (base t) component x +
        (weightedReconstructedPressureGradient
          hT base t.1 component x : ℂ) := by
      congr 1
      · rw [physicalUnprojectedQuadraticComponent,
          reconstructedUnprojectedDivergenceComponent_eq_fourierSeries]
        apply tsum_congr
        intro k
        rw [weightedUnprojectedDivergenceMode_apply,
          weightedPathExtension_of_mem hT base t.2]
      · exact pressureComplementFourierSeries_eq_reconstructedPressureGradient
          hT hreal t.1 component x

/-- Scalar reconstruction of one base component is exactly the corresponding complexified
coordinate of the actual real velocity. -/
theorem reconstructedTorusComplexScalar_baseComponent_eq_weightedVelocity
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    reconstructedTorusComplexScalar
        (weightedSobolevCoefficients 3 (base t component))
        (euclideanToSpatialTorus x) =
      (weightedReconstructedVelocity hT base t.1 x component : ℂ) := by
  have hcomplex := congrFun
    (complexifySpace_reconstructedTorusReal
      (hreal t) (euclideanToSpatialTorus x)) component
  change ((reconstructedTorusReal (base t)
      (euclideanToSpatialTorus x) component : ℝ) : ℂ) =
    reconstructedTorusComplexComponent (base t) component
      (euclideanToSpatialTorus x) at hcomplex
  change reconstructedTorusComplexScalar
      (weightedSobolevCoefficients 3 (base t component))
      (euclideanToSpatialTorus x) =
    ((reconstructedTorusReal (weightedPathExtension hT base t.1)
      (euclideanToSpatialTorus x) component : ℝ) : ℂ)
  rw [weightedPathExtension_of_mem hT base t.2, hcomplex]
  rw [reconstructedTorusComplexScalar_apply,
    reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [nativeUnweightedComponent]

/-- The scalar physical derivative used by the product owner is the actual spatial Fréchet
derivative of the corresponding complexified velocity component. -/
theorem reconstructedTorusComplexScalarFDeriv_baseComponent_eq_fderiv_weightedVelocity
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (t : Icc (0 : ℝ) T) (component coordinate : Fin 3) (x : Space) :
    reconstructedTorusComplexScalarFDeriv
        (weightedSobolevCoefficients 3 (base t component)) x
        (EuclideanSpace.single coordinate 1) =
      fderiv ℝ
        (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
        (EuclideanSpace.single coordinate 1) := by
  have hderivative :=
    (hasFDerivAt_reconstructedTorusComplexScalar
      (weightedSobolevCoefficients 3 (base t component)) x).fderiv
  have hfield :
      (fun y : Space ↦ reconstructedTorusComplexScalar
        (weightedSobolevCoefficients 3 (base t component))
          (euclideanToSpatialTorus y)) =
      (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) := by
    funext y
    exact reconstructedTorusComplexScalar_baseComponent_eq_weightedVelocity
      hT hreal t component y
  rw [← hfield, hderivative]

/-! ## The pointwise classical interior momentum return -/

/-- **Pointwise classical periodic momentum equation.**  A Fourier-real fixed mild path carrying
a coherent all-order native tower has a genuine interior time derivative at every physical point.
That derivative is viscosity times the actual spatial Laplacian, minus the actual product-rule
quadratic divergence, minus the actual reconstructed pressure gradient. -/
theorem CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (x : Space) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        (weightedReconstructedVelocity hT base tau x component : ℂ))
      ((nu : ℂ) *
          Δ (fun y : Space ↦
            (weightedReconstructedVelocity hT base t y component : ℂ)) x -
        physicalUnprojectedQuadraticComponent
          (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) component x -
        (weightedReconstructedPressureGradient
          hT base t component x : ℂ)) t := by
  let addressedTime : Icc (0 : ℝ) T :=
    ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
  have htime := tower.hasDerivAt_reconstructedVelocity_component
    hT nu hnu initial hfixed hreal component x ht
  have hviscous :=
    CoherentWeightedSmoothPathTower.summable_viscousFourierSeries
      hT tower hreal nu addressedTime component x
  have hsource := summable_projectedSourceFourierSeries
    hT base addressedTime component x
  have hsplit :
      (∑' k : SpatialFrequency,
        (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
            weightedReconstructedVelocityCoefficient
              hT base component k t -
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (base addressedTime))
            (unweightedVectorThree (base addressedTime)) component).1 k) *
              euclideanFourierCharacter k x) =
        (∑' k : SpatialFrequency,
          (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
              weightedReconstructedVelocityCoefficient
                hT base component k t) * euclideanFourierCharacter k x) -
        ∑' k : SpatialFrequency,
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (base addressedTime))
            (unweightedVectorThree (base addressedTime)) component).1 k *
              euclideanFourierCharacter k x := by
    rw [← hviscous.tsum_sub hsource]
    apply tsum_congr
    intro k
    ring
  have hphysical :
      (∑' k : SpatialFrequency,
        (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
            weightedReconstructedVelocityCoefficient
              hT base component k t -
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (base addressedTime))
            (unweightedVectorThree (base addressedTime)) component).1 k) *
              euclideanFourierCharacter k x) =
        (nu : ℂ) *
            Δ (fun y : Space ↦
              (weightedReconstructedVelocity hT base t y component : ℂ)) x -
          physicalUnprojectedQuadraticComponent
            (base addressedTime) component x -
          (weightedReconstructedPressureGradient
            hT base t component x : ℂ) := by
    rw [hsplit,
      viscousFourierSeries_eq_laplacian
        hT tower hreal nu addressedTime component x,
      projectedSourceFourierSeries_eq_physicalQuadratic_add_pressureGradient
        hT hreal addressedTime component x]
    ring
  rw [hphysical] at htime
  exact htime

/-- **Classical advective form.**  On the modewise incompressible path fibre, the physical
product-rule divergence is exactly `(u · ∇)u`; hence the same strong interior derivative satisfies
the standard pointwise component momentum equation. -/
theorem CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum_advection
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (hdivergence : IsWeightedDivergenceFreePath base)
    (component : Fin 3) (x : Space) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        (weightedReconstructedVelocity hT base tau x component : ℂ))
      ((nu : ℂ) *
          Δ (fun y : Space ↦
            (weightedReconstructedVelocity hT base t y component : ℂ)) x -
        ∑ coordinate : Fin 3,
          (weightedReconstructedVelocity
              hT base t x coordinate : ℂ) *
            fderiv ℝ
              (fun y : Space ↦
                (weightedReconstructedVelocity
                  hT base t y component : ℂ)) x
              (EuclideanSpace.single coordinate 1) -
        (weightedReconstructedPressureGradient
          hT base t component x : ℂ)) t := by
  let addressedTime : Icc (0 : ℝ) T :=
    ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
  have hmomentum :=
    CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum
      hT tower nu hnu initial hfixed hreal component x ht
  have hadvection :
      physicalUnprojectedQuadraticComponent
          (base addressedTime) component x =
        ∑ coordinate : Fin 3,
          (weightedReconstructedVelocity
              hT base t x coordinate : ℂ) *
            fderiv ℝ
              (fun y : Space ↦
                (weightedReconstructedVelocity
                  hT base t y component : ℂ)) x
              (EuclideanSpace.single coordinate 1) := by
    rw [physicalUnprojectedQuadraticComponent_eq_advection
      (hdivergence addressedTime) component x]
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    rw [reconstructedTorusComplexScalar_baseComponent_eq_weightedVelocity
        hT hreal addressedTime coordinate x,
      reconstructedTorusComplexScalarFDeriv_baseComponent_eq_fderiv_weightedVelocity
        hT hreal addressedTime component coordinate x]
  rw [hadvection] at hmomentum
  exact hmomentum

section Audit

#print axioms viscousFourierSeries_eq_laplacian
#print axioms projectedSourceFourierSeries_eq_physicalQuadratic_add_pressureGradient
#print axioms CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum
#print axioms CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum_advection

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum
