import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionRemainderBound
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesWeightedOrderRestriction

/-!
# Translation differences factor through the Stokes dissipation population

**[proved-derived]** A spatial translation acts diagonally on the complete torus Fourier carrier.
The returned difference of one character is controlled by its exact derivative word, and the
three-coordinate Cauchy comparison converts that word into the Stokes eigenvalue.  Summing over
every retained frequency proves that the complete translation-difference mass factors through
the scale-sensitive dissipation population, rather than through order-zero energy.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesTranslationDissipation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction

/-- The exact multiplier returned by translating one Fourier character away from the zero chart. -/
def characterTranslationDifference (k : SpatialFrequency) (displacement : Space) : ℂ :=
  euclideanFourierCharacter k displacement - 1

/-- The complete squared translation-difference population of a Fourier coefficient carrier. -/
def fourierTranslationDifferenceMass
    (coeff : PeriodicFourierL2) (displacement : Space) : ℝ :=
  ∑' k : SpatialFrequency,
    ‖characterTranslationDifference k displacement * coeff k‖ ^ 2

/-- The complete Stokes-weighted coefficient population.  Under the physical Fourier receiver
this is the component gradient-square population appearing in vorticity dissipation. -/
def stokesDissipationMass (coeff : PeriodicFourierL2) : ℝ :=
  ∑' k : SpatialFrequency, torusStokesEigenvalue k * ‖coeff k‖ ^ 2

/-- The exact character difference is bounded by its three addressed derivative factors. -/
theorem norm_characterTranslationDifference_le
    (k : SpatialFrequency) (displacement : Space) :
    ‖characterTranslationDifference k displacement‖ ≤
      2 * Real.pi * frequencyL1 k * ‖displacement‖ := by
  have hdiff : ∀ x ∈ (Set.univ : Set Space),
      DifferentiableAt ℝ (euclideanFourierCharacter k) x := by
    intro x _hx
    exact (hasFDerivAt_euclideanFourierCharacter k x).differentiableAt
  have hbound : ∀ x ∈ (Set.univ : Set Space),
      ‖fderiv ℝ (euclideanFourierCharacter k) x‖ ≤
        2 * Real.pi * frequencyL1 k := by
    intro x _hx
    rw [(hasFDerivAt_euclideanFourierCharacter k x).fderiv]
    have hsum :
        (∑ coordinate : Fin 3, |(k coordinate : ℝ)|) = frequencyL1 k := by
      simp [frequencyL1, Fin.sum_univ_succ, add_assoc]
    rw [← hsum]
    exact norm_euclideanFourierCharacterFDeriv_le k x
  have htransport := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (Set.mem_univ (0 : Space)) (Set.mem_univ displacement)
  simpa [characterTranslationDifference, euclideanFourierCharacter,
    euclideanFourierFactor, frequencyL1] using htransport

/-- Squaring the returned difference exposes the exact Stokes scale.  The constant three is the
finite coordinate comparison `|k|₁² ≤ 3|k|₂²`, not a mode count or asymptotic estimate. -/
theorem norm_characterTranslationDifference_sq_le_stokes
    (k : SpatialFrequency) (displacement : Space) :
    ‖characterTranslationDifference k displacement‖ ^ 2 ≤
      3 * ‖displacement‖ ^ 2 * torusStokesEigenvalue k := by
  have hdifference := norm_characterTranslationDifference_le k displacement
  have hfrequency := frequencyL1_sq_le_three_mul_frequencySquared k
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hfrequencyNonneg : 0 ≤ frequencyL1 k := frequencyL1_nonneg k
  have hdisplacement : 0 ≤ ‖displacement‖ := norm_nonneg _
  have hsquare :
      ‖characterTranslationDifference k displacement‖ ^ 2 ≤
        (2 * Real.pi * frequencyL1 k * ‖displacement‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hdifference 2
  calc
    ‖characterTranslationDifference k displacement‖ ^ 2 ≤
        (2 * Real.pi * frequencyL1 k * ‖displacement‖) ^ 2 := hsquare
    _ = (2 * Real.pi) ^ 2 * frequencyL1 k ^ 2 * ‖displacement‖ ^ 2 := by ring
    _ ≤ (2 * Real.pi) ^ 2 * (3 * frequencySquared k) * ‖displacement‖ ^ 2 := by
      gcongr
    _ = 3 * ‖displacement‖ ^ 2 * torusStokesEigenvalue k := by
      simp [torusStokesEigenvalue]
      ring

/-- One transported coefficient occurrence is controlled by the matching dissipation occurrence. -/
theorem norm_characterTranslationDifference_mul_sq_le
    (coeff : PeriodicFourierL2) (k : SpatialFrequency) (displacement : Space) :
    ‖characterTranslationDifference k displacement * coeff k‖ ^ 2 ≤
      (3 * ‖displacement‖ ^ 2) *
        (torusStokesEigenvalue k * ‖coeff k‖ ^ 2) := by
  rw [norm_mul, mul_pow]
  have h := mul_le_mul_of_nonneg_right
    (norm_characterTranslationDifference_sq_le_stokes k displacement)
    (sq_nonneg ‖coeff k‖)
  nlinarith

/-- Every order-one Sobolev coefficient population carries an honestly summable Stokes
dissipation population. -/
theorem summable_stokesDissipation_of_hasPeriodicSobolevCoefficients_one
    (coeff : PeriodicFourierL2)
    (hcoeff : HasPeriodicSobolevCoefficients 1 coeff) :
    Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k * ‖coeff k‖ ^ 2 := by
  unfold HasPeriodicSobolevCoefficients at hcoeff
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (torusStokesEigenvalue_nonneg k) (sq_nonneg _))
    (fun k ↦ ?_) hcoeff
  have hscale : torusStokesEigenvalue k ≤ 1 + torusStokesEigenvalue k := by
    linarith
  calc
    torusStokesEigenvalue k * ‖coeff k‖ ^ 2 ≤
        (1 + torusStokesEigenvalue k) * ‖coeff k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscale (sq_nonneg _)
    _ = periodicSobolevWeight 1 k * ‖coeff k‖ ^ 2 := by
      simp [periodicSobolevWeight]

/-- **[proved-derived; formal-checked]** The complete translation-difference receiver factors
through the complete Stokes dissipation population.  No supremum derivative or order-zero energy
coefficient is introduced. -/
theorem fourierTranslationDifferenceMass_le_stokesDissipationMass
    (coeff : PeriodicFourierL2) (displacement : Space)
    (hdissipation : Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k * ‖coeff k‖ ^ 2) :
    fourierTranslationDifferenceMass coeff displacement ≤
      3 * ‖displacement‖ ^ 2 * stokesDissipationMass coeff := by
  let C : ℝ := 3 * ‖displacement‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hright : Summable fun k : SpatialFrequency ↦
      C * (torusStokesEigenvalue k * ‖coeff k‖ ^ 2) :=
    hdissipation.mul_left C
  have hleft : Summable fun k : SpatialFrequency ↦
      ‖characterTranslationDifference k displacement * coeff k‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun _ ↦ sq_nonneg _)
      (fun k ↦ by
        simpa [C] using
          norm_characterTranslationDifference_mul_sq_le coeff k displacement)
      hright
  unfold fourierTranslationDifferenceMass stokesDissipationMass
  calc
    (∑' k : SpatialFrequency,
        ‖characterTranslationDifference k displacement * coeff k‖ ^ 2) ≤
      ∑' k : SpatialFrequency,
        C * (torusStokesEigenvalue k * ‖coeff k‖ ^ 2) :=
      hleft.tsum_le_tsum
        (fun k ↦ by
          simpa [C] using
            norm_characterTranslationDifference_mul_sq_le coeff k displacement)
        hright
    _ = C * ∑' k : SpatialFrequency,
        torusStokesEigenvalue k * ‖coeff k‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = 3 * ‖displacement‖ ^ 2 *
        ∑' k : SpatialFrequency,
          torusStokesEigenvalue k * ‖coeff k‖ ^ 2 := rfl

/-- The order-one Sobolev carrier discharges the only summability port of the complete
translation-to-dissipation passage. -/
theorem fourierTranslationDifferenceMass_le_stokesDissipationMass_of_sobolevOne
    (coeff : PeriodicFourierL2) (displacement : Space)
    (hcoeff : HasPeriodicSobolevCoefficients 1 coeff) :
    fourierTranslationDifferenceMass coeff displacement ≤
      3 * ‖displacement‖ ^ 2 * stokesDissipationMass coeff :=
  fourierTranslationDifferenceMass_le_stokesDissipationMass coeff displacement
    (summable_stokesDissipation_of_hasPeriodicSobolevCoefficients_one coeff hcoeff)

/-! ## Exact attachment to the physical vorticity carrier -/

/-- One strict-interior vorticity slice is globally smooth in space.  This is the spatial
restriction of the already-founded jointly smooth open world-tube, not an additional regularity
hypothesis. -/
theorem openPeriodicSolutionOn_vorticitySlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    ContDiff ℝ ∞ (fun x ↦ vorticityField velocity x t.1) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hdomain : Set.univ ×ˢ Ioo 0 T ∈ nhds (x, t.1) := by
    exact prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds t.2.1 t.2.2)
  have hsource :=
    (openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt hdomain
  have hslice : ContDiffAt ℝ ∞ (fun y : Space ↦ (y, t.1)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def, Function.uncurry] using hsource.comp x hslice

/-- The complete scalar Fourier carrier of one addressed component of the actual descended
vorticity slice. -/
def openPeriodicVorticityComponentFourierL2
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) : PeriodicFourierL2 :=
  smoothSliceFourierL2 (fun x ↦ vorticityField velocity x t.1)
    (openPeriodicSolutionOn_vorticitySlice_contDiff solution t)
    (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2) component

/-- The scalar carrier is coefficientwise exactly the matching component of the active complex
vorticity mode. -/
theorem openPeriodicVorticityComponentFourierL2_apply
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) (k : SpatialFrequency) :
    openPeriodicVorticityComponentFourierL2 solution t component k =
      openPeriodicVorticityFourierMode solution t k component := by
  rw [openPeriodicVorticityComponentFourierL2, smoothSliceFourierL2_apply]
  rfl

/-- Every actual vorticity component enters the complete order-one coefficient carrier.  The
proof first places the smooth slice in H³ and then lowers only the receiver weight while retaining
the coefficient occurrence literally. -/
theorem hasPeriodicSobolevCoefficients_one_openPeriodicVorticityComponent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) :
    HasPeriodicSobolevCoefficients 1
      (openPeriodicVorticityComponentFourierL2 solution t component) := by
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ ∞ omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  let source : PeriodicSobolevCoefficients 3 :=
    smoothSliceSobolevCoefficients omega homega hperiodic component
  have hrestricted :=
    (periodicSobolevCoefficientsRestrict 1 3 (by omega) source).2
  simpa [source, omega, homega, hperiodic,
    periodicSobolevCoefficientsRestrict,
    openPeriodicVorticityComponentFourierL2] using hrestricted

/-- A coordinate derivative of a vector field and the derivative of its addressed scalar
component are the same occurrence at the component receiver. -/
theorem spatialDirectionalJet_component_eq_fderiv_component
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (coordinate component : Fin 3) (x : Space) :
    spatialDirectionalJet u coordinate x component =
      fderiv ℝ (fun y ↦ u y component) x (spatialBasisVector coordinate) := by
  have hcomponent := (EuclideanSpace.proj component).hasFDerivAt.comp x
    ((hu.differentiable (by simp) x).hasFDerivAt)
  have happly := congrArg
    (fun L : Space →L[ℝ] ℝ ↦ L (spatialBasisVector coordinate)) hcomponent.fderiv
  simpa [Function.comp_def, spatialDirectionalJet] using happly.symm

/-- The metric gradient square is exactly the sum of the three addressed directional-derivative
squares.  No norm comparison or dimension-dependent estimate is used. -/
theorem norm_gradient_component_sq_eq_sum_spatialDirectionalJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (component : Fin 3) (x : Space) :
    ‖gradient (fun y ↦ u y component) x‖ ^ 2 =
      ∑ coordinate : Fin 3, (spatialDirectionalJet u coordinate x component) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  have hcomponentSmooth : ContDiff ℝ ∞ (fun y ↦ u y component) := by
    simpa [Function.comp_def] using
      (EuclideanSpace.proj component).contDiff.comp hu
  have hdiff : DifferentiableAt ℝ (fun y ↦ u y component) x :=
    hcomponentSmooth.differentiable (by simp) x
  have hgradient :
      gradient (fun y ↦ u y component) x coordinate =
        fderiv ℝ (fun y ↦ u y component) x (spatialBasisVector coordinate) := by
    rw [← EuclideanSpace.inner_basisFun_real
      (Fin 3) (gradient (fun y ↦ u y component) x : Space) coordinate]
    simpa [spatialBasisVector] using
      (inner_gradient_left hdiff :
        inner ℝ (gradient (fun y ↦ u y component) x)
            (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) =
          fderiv ℝ (fun y ↦ u y component) x
            (EuclideanSpace.basisFun (Fin 3) ℝ coordinate))
  rw [Real.norm_eq_abs, sq_abs, hgradient,
    ← spatialDirectionalJet_component_eq_fderiv_component u hu coordinate component x]

/-- Parseval identifies the complete Stokes coefficient population of a smooth periodic scalar
component with its physical gradient-square population on the unit cube. -/
theorem stokesDissipationMass_smoothSliceFourierL2_eq_integral_gradient_sq
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    stokesDissipationMass (smoothSliceFourierL2 u hu hperiodic component) =
      ∫ x in unitCube, ‖gradient (fun y ↦ u y component) x‖ ^ 2 := by
  let derivativeCoeff := fun coordinate : Fin 3 ↦
    smoothSliceFourierL2 (spatialDirectionalJet u coordinate)
      (spatialDirectionalJet_contDiff u hu coordinate)
      (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate) component
  have hcomponentSummable : ∀ coordinate : Fin 3,
      Summable fun k : SpatialFrequency ↦ ‖derivativeCoeff coordinate k‖ ^ 2 := by
    intro coordinate
    exact (hasSum_sq_smoothSliceFourierL2
      (spatialDirectionalJet u coordinate)
      (spatialDirectionalJet_contDiff u hu coordinate)
      (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate)
      component).summable
  have hinterchange :
      (∑' k : SpatialFrequency,
          ∑ coordinate : Fin 3, ‖derivativeCoeff coordinate k‖ ^ 2) =
        ∑ coordinate : Fin 3,
          ∑' k : SpatialFrequency, ‖derivativeCoeff coordinate k‖ ^ 2 :=
    Summable.tsum_finsetSum (s := Finset.univ)
      (fun coordinate _hcoordinate ↦ hcomponentSummable coordinate)
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hintegrable : ∀ coordinate : Fin 3,
      IntegrableOn (fun x ↦
        (spatialDirectionalJet u coordinate x component) ^ 2) unitCube := by
    intro coordinate
    have hcomponentSmooth : ContDiff ℝ ∞
        (fun x ↦ spatialDirectionalJet u coordinate x component) := by
      simpa [Function.comp_def] using
        (EuclideanSpace.proj component).contDiff.comp
          (spatialDirectionalJet_contDiff u hu coordinate)
    exact (hcomponentSmooth.pow 2).continuous.continuousOn
      |>.integrableOn_compact hcubeCompact
  unfold stokesDissipationMass
  calc
    (∑' k : SpatialFrequency, torusStokesEigenvalue k *
        ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2) =
        ∑' k : SpatialFrequency,
          ∑ coordinate : Fin 3, ‖derivativeCoeff coordinate k‖ ^ 2 := by
      apply tsum_congr
      intro k
      exact (sum_norm_sq_smoothSliceFourierL2_first
        u hu hperiodic component k).symm
    _ = ∑ coordinate : Fin 3,
        ∑' k : SpatialFrequency, ‖derivativeCoeff coordinate k‖ ^ 2 := hinterchange
    _ = ∑ coordinate : Fin 3,
        ∫ x in unitCube, (spatialDirectionalJet u coordinate x component) ^ 2 := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      simpa [derivativeCoeff] using
        (tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
          (spatialDirectionalJet u coordinate)
          (spatialDirectionalJet_contDiff u hu coordinate)
          (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate) component)
    _ = ∫ x in unitCube,
        ∑ coordinate : Fin 3,
          (spatialDirectionalJet u coordinate x component) ^ 2 := by
      rw [integral_finset_sum Finset.univ
        (fun coordinate _hcoordinate ↦ hintegrable coordinate)]
    _ = ∫ x in unitCube, ‖gradient (fun y ↦ u y component) x‖ ^ 2 := by
      apply setIntegral_congr_fun hcubeCompact.measurableSet
      intro x _hx
      exact (norm_gradient_component_sq_eq_sum_spatialDirectionalJet
        u hu component x).symm

/-- The complete actual vorticity Stokes population, with all three component addresses retained,
is exactly the physical vorticity dissipation appearing in the enstrophy identity. -/
theorem sum_stokesDissipationMass_openPeriodicVorticityComponent_eq_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    (∑ component : Fin 3,
      stokesDissipationMass
        (openPeriodicVorticityComponentFourierL2 solution t component)) =
      periodicVorticityDissipation velocity t.1 := by
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ ∞ omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hintegrable : ∀ component : Fin 3,
      IntegrableOn (fun x ↦ ‖gradient (fun y ↦ omega y component) x‖ ^ 2)
        unitCube := by
    intro component
    have hcomponent : ContDiff ℝ 2 (fun y ↦ omega y component) :=
      ((EuclideanSpace.proj component).contDiff.comp homega).of_le (by
        show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    exact ((gradient_contDiff_one _ hcomponent).norm_sq ℝ).continuous.continuousOn
      |>.integrableOn_compact hcubeCompact
  unfold periodicVorticityDissipation
  simp_rw [show ∀ component : Fin 3,
      stokesDissipationMass
          (openPeriodicVorticityComponentFourierL2 solution t component) =
        ∫ x in unitCube, ‖gradient (fun y ↦ omega y component) x‖ ^ 2 by
    intro component
    exact stokesDissipationMass_smoothSliceFourierL2_eq_integral_gradient_sq
      omega homega hperiodic component]
  rw [← integral_finset_sum Finset.univ
    (fun component _hcomponent ↦ hintegrable component)]

/-- **[proved-derived; formal-checked]** The actual vorticity translation receiver is controlled
by the physical dissipation term with the exact geometric factor `3 ‖d‖²`.  This is the first
constitutive bridge in the direction/Hodge line which carries a spatial difference directly into
the viscosity-scale population instead of replacing it by a global Lipschitz scalar. -/
theorem sum_fourierTranslationDifferenceMass_openPeriodicVorticity_le_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (displacement : Space) :
    (∑ component : Fin 3,
      fourierTranslationDifferenceMass
        (openPeriodicVorticityComponentFourierL2 solution t component) displacement) ≤
      3 * ‖displacement‖ ^ 2 * periodicVorticityDissipation velocity t.1 := by
  have hcomponent : ∀ component : Fin 3,
      fourierTranslationDifferenceMass
          (openPeriodicVorticityComponentFourierL2 solution t component) displacement ≤
        3 * ‖displacement‖ ^ 2 *
          stokesDissipationMass
            (openPeriodicVorticityComponentFourierL2 solution t component) := by
    intro component
    exact fourierTranslationDifferenceMass_le_stokesDissipationMass_of_sobolevOne
      (openPeriodicVorticityComponentFourierL2 solution t component) displacement
      (hasPeriodicSobolevCoefficients_one_openPeriodicVorticityComponent
        solution t component)
  calc
    (∑ component : Fin 3,
        fourierTranslationDifferenceMass
          (openPeriodicVorticityComponentFourierL2 solution t component) displacement) ≤
        ∑ component : Fin 3, 3 * ‖displacement‖ ^ 2 *
          stokesDissipationMass
            (openPeriodicVorticityComponentFourierL2 solution t component) :=
      Finset.sum_le_sum fun component _hcomponent ↦ hcomponent component
    _ = 3 * ‖displacement‖ ^ 2 *
        ∑ component : Fin 3,
          stokesDissipationMass
            (openPeriodicVorticityComponentFourierL2 solution t component) := by
      rw [Finset.mul_sum]
    _ = 3 * ‖displacement‖ ^ 2 * periodicVorticityDissipation velocity t.1 := by
      rw [sum_stokesDissipationMass_openPeriodicVorticityComponent_eq_dissipation
        solution t]

section Audit

#print axioms norm_characterTranslationDifference_le
#print axioms norm_characterTranslationDifference_sq_le_stokes
#print axioms norm_characterTranslationDifference_mul_sq_le
#print axioms summable_stokesDissipation_of_hasPeriodicSobolevCoefficients_one
#print axioms fourierTranslationDifferenceMass_le_stokesDissipationMass
#print axioms fourierTranslationDifferenceMass_le_stokesDissipationMass_of_sobolevOne
#print axioms openPeriodicSolutionOn_vorticitySlice_contDiff
#print axioms openPeriodicVorticityComponentFourierL2_apply
#print axioms hasPeriodicSobolevCoefficients_one_openPeriodicVorticityComponent
#print axioms spatialDirectionalJet_component_eq_fderiv_component
#print axioms norm_gradient_component_sq_eq_sum_spatialDirectionalJet
#print axioms stokesDissipationMass_smoothSliceFourierL2_eq_integral_gradient_sq
#print axioms sum_stokesDissipationMass_openPeriodicVorticityComponent_eq_dissipation
#print axioms sum_fourierTranslationDifferenceMass_openPeriodicVorticity_le_dissipation

end Audit

end Soma.Holonics.Millennium.NavierStokesTranslationDissipation
