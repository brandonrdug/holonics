import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelMoment

/-!
# The fixed dyadic base descends to lower-order velocity energy

**[proved-derived]** The radius-zero Hodge carrier contains only the twenty-seven frequencies in
the unit integer cube.  Parseval bounds every actual velocity coefficient by its componentwise
`L²` energy; the exact curl multiplier, finite-frequency incidence, and Hodge ascent then transport
that lower-order receiver to the complete scale-zero Jacobian and stretching readings.

This removes the former circular payment of the base term by the critical vorticity rate.  It does
not assert the still-open summability of the higher dyadic kernel moments or perform the final time
integration.
-/

noncomputable section

open ContDiff Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Parseval returns a lower-order receiver for every actual velocity pin -/

/-- The componentwise square-root `L²` receiver of an actual strict-interior velocity slice.
Every component and the exact Euclidean unit-cube chart remain explicit. -/
def openPeriodicVelocityL2RootReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑ component : Fin 3,
    Real.sqrt (∫ x in unitCube, (velocity x t.1 component) ^ 2)

theorem openPeriodicVelocityL2RootReceiver_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ openPeriodicVelocityL2RootReceiver solution t := by
  unfold openPeriodicVelocityL2RootReceiver
  exact Finset.sum_nonneg fun component _ ↦ Real.sqrt_nonneg _

/-- One component's exact cube square population is a face of twice the ordinary periodic kinetic
energy. -/
theorem componentCubeEnergy_le_two_mul_periodicKineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (component : Fin 3) :
    (∫ x in unitCube, (velocity x t.1 component) ^ 2) ≤
      2 * periodicKineticEnergy velocity t.1 := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hslice := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have hleftInt : IntegrableOn (fun x : Space ↦ (velocity x t.1 component) ^ 2) unitCube :=
    (((EuclideanSpace.proj component).continuous.comp hslice.continuous).pow 2).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hrightInt : IntegrableOn (fun x : Space ↦ ‖velocity x t.1‖ ^ 2) unitCube :=
    (hslice.continuous.norm.pow 2).continuousOn.integrableOn_compact hcubeCompact
  have hpoint : ∀ x ∈ unitCube,
      (velocity x t.1 component) ^ 2 ≤ ‖velocity x t.1‖ ^ 2 := by
    intro x _hx
    rw [EuclideanSpace.norm_sq_eq]
    have hsingle := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun c : Fin 3 ↦ ‖velocity x t.1 c‖ ^ 2)
      (fun c _hc ↦ sq_nonneg _)
      (Finset.mem_univ component)
    simpa [Real.norm_eq_abs, sq_abs] using hsingle
  calc
    (∫ x in unitCube, (velocity x t.1 component) ^ 2) ≤
        ∫ x in unitCube, ‖velocity x t.1‖ ^ 2 :=
      setIntegral_mono_on hleftInt hrightInt hcubeMeasurable hpoint
    _ = 2 * periodicKineticEnergy velocity t.1 := by
      unfold periodicKineticEnergy kineticEnergyDensity
      rw [← integral_const_mul]
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      ring

theorem periodicKineticEnergy_nonneg_of_openPeriodicSolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ periodicKineticEnergy velocity t.1 := by
  unfold periodicKineticEnergy kineticEnergyDensity
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x ↦ mul_nonneg (by norm_num) (sq_nonneg _))

/-- The componentwise receiver is itself bounded by the ordinary kinetic-energy receiver.  The
factor three is the exact number of retained component addresses. -/
theorem openPeriodicVelocityL2RootReceiver_le_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    openPeriodicVelocityL2RootReceiver solution t ≤
      3 * Real.sqrt (2 * periodicKineticEnergy velocity t.1) := by
  unfold openPeriodicVelocityL2RootReceiver
  calc
    (∑ component : Fin 3,
        Real.sqrt (∫ x in unitCube, (velocity x t.1 component) ^ 2)) ≤
      ∑ _component : Fin 3,
        Real.sqrt (2 * periodicKineticEnergy velocity t.1) := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact Real.sqrt_le_sqrt
        (componentCubeEnergy_le_two_mul_periodicKineticEnergy solution t component)
    _ = 3 * Real.sqrt (2 * periodicKineticEnergy velocity t.1) := by simp

/-- One addressed Fourier coefficient is bounded by the square root of the complete Parseval
population containing it. -/
theorem norm_smoothSliceFourierL2_le_sqrt_cubeEnergy
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) (frequency : SpatialFrequency) :
    ‖smoothSliceFourierL2 u hu hperiodic component frequency‖ ≤
      Real.sqrt (∫ x in unitCube, (u x component) ^ 2) := by
  have hsummable :=
    (hasSum_sq_smoothSliceFourierL2 u hu hperiodic component).summable
  have hsingle :
      ‖smoothSliceFourierL2 u hu hperiodic component frequency‖ ^ 2 ≤
        ∑' k, ‖smoothSliceFourierL2 u hu hperiodic component k‖ ^ 2 := by
    simpa using hsummable.sum_le_tsum {frequency}
      (fun k _hk ↦ sq_nonneg ‖smoothSliceFourierL2 u hu hperiodic component k‖)
  rw [tsum_sq_smoothSliceFourierL2_eq_integral_unitCube] at hsingle
  have henergy : 0 ≤ ∫ x in unitCube, (u x component) ^ 2 := by
    rw [← tsum_sq_smoothSliceFourierL2_eq_integral_unitCube u hu hperiodic component]
    exact tsum_nonneg fun k ↦ sq_nonneg ‖smoothSliceFourierL2 u hu hperiodic component k‖
  nlinarith [Real.sq_sqrt henergy,
    norm_nonneg (smoothSliceFourierL2 u hu hperiodic component frequency),
    Real.sqrt_nonneg (∫ x in unitCube, (u x component) ^ 2)]

/-- The complete three-component `L¹` coefficient receiver descends to the retained lower-order
velocity energy face. -/
theorem complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency) ≤
      openPeriodicVelocityL2RootReceiver solution t := by
  have hcomponent : ∀ component : Fin 3,
      ‖openPeriodicVelocityFourierMode solution t frequency component‖ ≤
        Real.sqrt (∫ x in unitCube, (velocity x t.1 component) ^ 2) := by
    intro component
    simpa [openPeriodicVelocityFourierMode, smoothSliceFourierL2_apply] using
      norm_smoothSliceFourierL2_le_sqrt_cubeEnergy
        (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component frequency
  unfold complexVectorL1 openPeriodicVelocityL2RootReceiver
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun component _hcomponent ↦ hcomponent component)
  simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-! ## The unit frequency lattice transports energy through curl and Hodge ascent -/

/-- Every frequency in the radius-zero outer cube has real `L¹` magnitude at most three. -/
theorem frequencyL1_le_three_of_mem_scaleZeroOuterCube
    {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (valleePoussinOuterRadius 0)) :
    frequencyL1 frequency ≤ 3 := by
  rw [mem_frequencyCube_iff] at hfrequency
  have hcoordinate : ∀ coordinate : Fin 3, |(frequency coordinate : ℝ)| ≤ 1 := by
    intro coordinate
    rw [abs_le]
    constructor
    · exact_mod_cast (hfrequency coordinate).1
    · exact_mod_cast (hfrequency coordinate).2
  unfold frequencyL1
  nlinarith [hcoordinate 0, hcoordinate 1, hcoordinate 2]

/-- The ambient supremum norm of a complex three-vector is bounded by its addressed `L¹`
receiver. -/
theorem norm_complexVector_le_complexVectorL1 (v : ComplexVector) :
    ‖v‖ ≤ complexVectorL1 v := by
  rw [pi_norm_le_iff_of_nonneg (complexVectorL1_nonneg v)]
  intro component
  fin_cases component
  · change ‖v 0‖ ≤ ‖v 0‖ + ‖v 1‖ + ‖v 2‖
    nlinarith [norm_nonneg (v 1), norm_nonneg (v 2)]
  · change ‖v 1‖ ≤ ‖v 0‖ + ‖v 1‖ + ‖v 2‖
    nlinarith [norm_nonneg (v 0), norm_nonneg (v 2)]
  · change ‖v 2‖ ≤ ‖v 0‖ + ‖v 1‖ + ‖v 2‖
    nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]

/-- On the finite scale-zero lattice, the exact curl multiplier costs at most `6π` times the
lower-order velocity receiver. -/
theorem complexVectorL1_openPeriodicVorticityFourierMode_le_baseEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (valleePoussinOuterRadius 0)) :
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) ≤
      (6 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier,
    frequencyCurlMultiplier, complexVectorL1_smul]
  have hscalar : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg]
  rw [hscalar]
  calc
    (2 * Real.pi) *
        complexVectorL1
          (complexCross (complexFrequencyVector frequency)
            (openPeriodicVelocityFourierMode solution t frequency)) ≤
      (2 * Real.pi) *
        (complexVectorL1 (complexFrequencyVector frequency) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency)) :=
      mul_le_mul_of_nonneg_left
        (complexVectorL1_cross_le_mul _ _) (mul_nonneg (by norm_num) Real.pi_nonneg)
    _ = (2 * Real.pi) *
        (frequencyL1 frequency *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency)) := by
      rw [complexVectorL1_complexFrequencyVector]
    _ ≤ (2 * Real.pi) *
        (3 * openPeriodicVelocityL2RootReceiver solution t) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) Real.pi_nonneg)
      exact mul_le_mul
        (frequencyL1_le_three_of_mem_scaleZeroOuterCube hfrequency)
        (complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver
          solution t frequency)
        (complexVectorL1_nonneg _)
        (by norm_num)
    _ = (6 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by ring

/-- The actual vorticity pin inherits the same finite-lattice energy bound in its ambient norm. -/
theorem norm_openPeriodicVorticityFourierMode_le_baseEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (valleePoussinOuterRadius 0)) :
    ‖openPeriodicVorticityFourierMode solution t frequency‖ ≤
      (6 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t :=
  (norm_complexVector_le_complexVectorL1 _).trans
    (complexVectorL1_openPeriodicVorticityFourierMode_le_baseEnergy
      solution t hfrequency)

/-- Each actual Jacobian pin in the fixed scale-zero lattice costs at most `18π` times the
lower-order velocity receiver. -/
theorem norm_openPeriodicJacobianFourierMode_le_baseEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (valleePoussinOuterRadius 0)) :
    ‖openPeriodicJacobianFourierMode solution t frequency‖ ≤
      (18 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by
  calc
    ‖openPeriodicJacobianFourierMode solution t frequency‖ =
        ‖hodgeJacobianMode frequency
          (openPeriodicVorticityFourierMode solution t frequency)‖ := by
      rw [hodgeJacobianMode_openPeriodicVorticityFourierMode]
    _ ≤ 3 * ‖openPeriodicVorticityFourierMode solution t frequency‖ :=
      norm_hodgeJacobianMode_le_three_mul _ _
    _ ≤ 3 * ((6 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t) :=
      mul_le_mul_of_nonneg_left
        (norm_openPeriodicVorticityFourierMode_le_baseEnergy solution t hfrequency)
        (by norm_num)
    _ = (18 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by ring

/-! ## The complete base term no longer uses the critical vorticity rate -/

/-- The complete radius-zero low pass contains exactly twenty-seven weighted modes and is
controlled by the lower-order velocity receiver with the exact coarse constant `486π`. -/
theorem norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_baseEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0 q‖ ≤
      (486 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by
  unfold openPeriodicSmoothHodgeJacobianLowPass
  refine (norm_finiteFourierSynthesis_le_sum_norm _ _ q).trans ?_
  calc
    (∑ frequency ∈ frequencyCube (valleePoussinOuterRadius 0),
        ‖(tensorValleePoussinWeight 0 frequency : ℂ) •
          openPeriodicJacobianFourierMode solution t frequency‖) ≤
      ∑ _frequency ∈ frequencyCube (valleePoussinOuterRadius 0),
        (18 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by
      apply Finset.sum_le_sum
      intro frequency hfrequency
      rw [norm_smul]
      obtain ⟨hweightNonneg, hweightOne⟩ :=
        tensorValleePoussinWeight_mem_unitInterval 0 frequency
      have hweightNorm : ‖(tensorValleePoussinWeight 0 frequency : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hweightNonneg] using hweightOne
      exact (mul_le_mul hweightNorm
        (norm_openPeriodicJacobianFourierMode_le_baseEnergy
          solution t hfrequency)
        (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
    _ = (486 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t := by
      rw [Finset.sum_const, nsmul_eq_mul, card_frequencyCube]
      norm_num [valleePoussinOuterRadius]
      ring

/-- The same complete base low pass factors through the ordinary periodic kinetic-energy
receiver. -/
theorem norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0 q‖ ≤
      (1458 * Real.pi) *
        Real.sqrt (2 * periodicKineticEnergy velocity t.1) := by
  calc
    ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0 q‖ ≤
        (486 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t :=
      norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_baseEnergy solution t q
    _ ≤ (486 * Real.pi) *
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity t.1)) :=
      mul_le_mul_of_nonneg_left
        (openPeriodicVelocityL2RootReceiver_le_kineticEnergy solution t)
        (mul_nonneg (by norm_num) Real.pi_nonneg)
    _ = (1458 * Real.pi) *
        Real.sqrt (2 * periodicKineticEnergy velocity t.1) := by ring

/-- **Non-circular base closure.** The scale-zero vortex-stretching face is paid for by the fixed
lower-order velocity `L²` receiver, while the critical vorticity magnitude appears only in the
literal pointwise quadratic receiver where the equation itself places it. -/
theorem norm_openPeriodicDyadicBaseStrainReading_le_baseEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicDyadicBaseStrainReading solution t q‖ ≤
      ((486 * Real.pi) * openPeriodicVelocityL2RootReceiver solution t) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  unfold openPeriodicDyadicBaseStrainReading
  let base : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart base)‖ ≤ _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  refine (norm_complexStretchingReading_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change ‖openPeriodicDyadicHodgeJacobianLowPass solution t 0 q‖ ≤ _
  rw [openPeriodicDyadicHodgeJacobianLowPass_zero]
  exact norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_baseEnergy solution t q

/-- The scale-zero vortex-stretching face therefore closes against ordinary kinetic energy, with
no payment by the critical vorticity rate. -/
theorem norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicDyadicBaseStrainReading solution t q‖ ≤
      ((1458 * Real.pi) *
        Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  unfold openPeriodicDyadicBaseStrainReading
  let base : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart base)‖ ≤ _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  refine (norm_complexStretchingReading_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change ‖openPeriodicDyadicHodgeJacobianLowPass solution t 0 q‖ ≤ _
  rw [openPeriodicDyadicHodgeJacobianLowPass_zero]
  exact norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_kineticEnergy solution t q

/-! ## The complete infinite-depth route inherits the non-circular base -/

/-- Every finite assembled spatial word now carries ordinary kinetic energy at its base, the
literal cross-coherence word in its middle, and the exact coefficient reconstruction fibre. -/
theorem norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (2 * openPeriodicJacobianCoefficientTailMass solution t
            (frequencyCube (dyadicHodgeInnerCutoff depth))) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hband :=
    norm_openPeriodicDyadicHodgeStrainWord_le_spatialCrossCoherenceWord
      solution t q depth hvorticity
  rw [openPeriodicDyadicHodgeStrainWord_eq_spatialDirectionRemainderWord] at hband
  rw [openPeriodicFullStrainReading_eq_dyadicSpatialDirectionWord_add_fiber]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((norm_add_le _ _).trans
        (add_le_add
          (norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy solution t q)
          hband))
      (norm_openPeriodicDyadicReconstructionFiberStrainReading_le solution t q depth))

/-- Every finite kinetic-energy assembly factors through the full spatial cross carrier plus the
named tail that vanishes along dyadic depth. -/
theorem norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0)
    (depth : ℕ) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        openPeriodicDyadicSpatialAssemblyTail solution t q depth := by
  refine (norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence_kineticEnergy
    solution t q depth hvorticity).trans ?_
  have hword := openPeriodicDyadicSpatialCrossCoherenceWord_le_full
    solution t q hsummable depth
  have hfactor :
      0 ≤ ‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) :=
    mul_nonneg (norm_nonneg _) (complexVectorL1_nonneg _)
  have hmiddle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hword hfactor)
    (sq_nonneg (complexVectorL1 (openPeriodicComplexVorticityAt solution t q)))
  exact add_le_add
    (add_le_add le_rfl hmiddle)
    (openPeriodicDyadicCoefficientTailTerm_le_spatialAssemblyTail solution t q depth)

/-- **Infinite-depth non-circular spatial receiver.** Under the exact geometric summability law,
the coefficient fibre disappears and the base is paid only by ordinary kinetic energy. -/
theorem norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hlimit : Tendsto (fun depth : ℕ ↦
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        openPeriodicDyadicSpatialAssemblyTail solution t q depth) atTop
      (nhds (((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_openPeriodicDyadicSpatialAssemblyTail_atTop solution t q)
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun depth ↦
    norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail_kineticEnergy
      solution t q hsummable hvorticity depth

/-- The same estimate returns to the literal real physical vortex-stretching occurrence. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  by_cases hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) = 0
  · have htorus : torusVorticityEvolution solution t q = 0 := by
      change vorticityField velocity (euclideanRepresentative q) t.1 = 0
      simpa [vorticityField] using hvorticity
    have hreceiver : openPeriodicComplexVorticityAt solution t q = 0 := by
      rw [openPeriodicComplexVorticityAt_eq_torusComplexification, htorus]
      rfl
    simp [openPeriodicPhysicalVortexStretchingAt, htorus, hreceiver, complexVectorL1]
  · rw [← norm_openPeriodicFullStrainReading_eq_abs_physical]
    exact norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_kineticEnergy
      solution t q hsummable hvorticity

section Audit

#print axioms openPeriodicVelocityL2RootReceiver_nonneg
#print axioms componentCubeEnergy_le_two_mul_periodicKineticEnergy
#print axioms periodicKineticEnergy_nonneg_of_openPeriodicSolution
#print axioms openPeriodicVelocityL2RootReceiver_le_kineticEnergy
#print axioms norm_smoothSliceFourierL2_le_sqrt_cubeEnergy
#print axioms complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver
#print axioms frequencyL1_le_three_of_mem_scaleZeroOuterCube
#print axioms norm_complexVector_le_complexVectorL1
#print axioms complexVectorL1_openPeriodicVorticityFourierMode_le_baseEnergy
#print axioms norm_openPeriodicVorticityFourierMode_le_baseEnergy
#print axioms norm_openPeriodicJacobianFourierMode_le_baseEnergy
#print axioms norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_baseEnergy
#print axioms norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le_kineticEnergy
#print axioms norm_openPeriodicDyadicBaseStrainReading_le_baseEnergy
#print axioms norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy
#print axioms norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence_kineticEnergy
#print axioms norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail_kineticEnergy
#print axioms norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_kineticEnergy
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence_kineticEnergy

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
