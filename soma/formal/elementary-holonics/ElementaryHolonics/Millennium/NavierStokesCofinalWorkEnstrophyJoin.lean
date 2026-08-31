import ElementaryHolonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
import ElementaryHolonics.Millennium.NavierStokesEnstrophyTerminalCurrent
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge

/-!
# The cofinal linear work as physical stretching with its scale-zero fibre

**[proved-derived; formal-checked]**  The complete unweighted output-parent stretching
population is the scalar Parseval presentation of the literal physical vortex-stretching
integral.  Consequently the real cofinal linear work is physical stretching minus exactly two
scale-zero faces: the low-pass stretching boundary and the Hermitian low-pass transport boundary.

On an addressed compact time interval, the periodic enstrophy identity then rewrites the physical
stretching integral as endpoint enstrophy plus viscous dissipation.  The scale-zero boundary is
retained as the complete reconstruction fibre.  No estimate of that fibre, terminal passage, or
regularity conclusion is asserted.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

namespace Soma.Holonics.Millennium.NavierStokesCofinalWorkEnstrophyJoin

open Soma.Holonics.Millennium.HolonicTerminalCurrent
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
open Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit
open Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCompactL1
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesEnstrophyTerminalCurrent
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityThreeStrands
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The complete physical stretching source -/

/-- One component of `(omega · nabla) u`, built from the literal smooth torus lifts. -/
def fullVortexStretchingSourceComponent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : Fin 3) : C(SpatialTorus, ℂ) :=
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let huPeriodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ (⊤ : ℕ∞) omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let homegaPeriodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  ∑ coordinate : Fin 3,
    smoothSliceComponentLift omega homega homegaPeriodic coordinate *
      smoothSliceComponentLift (directionalDerivativeField u coordinate)
        (directionalDerivativeField_contDiff_infty hu coordinate)
        (directionalDerivativeField_isOnePeriodic huPeriodic coordinate) output

/-- The complete source component is literally the Jacobian acting on physical vorticity. -/
theorem fullVortexStretchingSourceComponent_apply
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : Fin 3) (q : SpatialTorus) :
    fullVortexStretchingSourceComponent solution t output q =
      complexMatrixAction
        (openPeriodicTorusJacobianArraySlice solution t q)
        (openPeriodicComplexVorticityAt solution t q) output := by
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
  simp only [fullVortexStretchingSourceComponent, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, smoothSliceComponentLift, periodicTorusLift_projection]
  rw [openPeriodicComplexVorticityAt_eq_torusComplexification,
    torusVorticityEvolution_projection]
  unfold complexMatrixAction complexOfRealSpace directionalDerivativeField
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [openPeriodicTorusJacobianArraySlice_projection]
  unfold complexVelocityComponent
  rw [show NavierStokesH3Production.spatialBasisVector coordinate =
      EuclideanSpace.basisFun (Fin 3) ℝ coordinate by rfl]
  ring

/-- Every Fourier coefficient of the physical stretching source retains its complete
advecting-vorticity parent fibre. -/
theorem mFourierCoeff_fullVortexStretchingSourceComponent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : Fin 3) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fullVortexStretchingSourceComponent solution t output) frequency =
      ∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
        openPeriodicVorticityFourierMode solution t parent coordinate *
          (openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 (frequency - parent) := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let huPeriodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ (⊤ : ℕ∞) omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let homegaPeriodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  let field : Fin 3 → C(SpatialTorus, ℂ) := fun coordinate ↦
    smoothSliceComponentLift omega homega homegaPeriodic coordinate *
      smoothSliceComponentLift (directionalDerivativeField u coordinate)
        (directionalDerivativeField_contDiff_infty hu coordinate)
        (directionalDerivativeField_isOnePeriodic huPeriodic coordinate) output
  change torusSpatialFourierCoeff (⇑(∑ coordinate : Fin 3, field coordinate))
    frequency = _
  have hsum := torusSpatialFourierCoeff_finset_sum
    (Finset.univ : Finset (Fin 3)) field frequency
  rw [hsum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  unfold field
  change torusSpatialFourierCoeff
      ((⇑(smoothSliceComponentLift omega homega homegaPeriodic coordinate) :
          SpatialTorus → ℂ) *
        ⇑(smoothSliceComponentLift (directionalDerivativeField u coordinate)
          (directionalDerivativeField_contDiff_infty hu coordinate)
          (directionalDerivativeField_isOnePeriodic huPeriodic coordinate) output))
      frequency = _
  rw [torusSpatialFourierCoeff_smoothSliceComponentLift_mul,
    scalarH3Product_apply]
  apply tsum_congr
  intro parent
  rw [smoothSliceSobolevCoefficients, smoothSliceFourierL2_apply]
  have homegaMode :=
    smoothSliceFourierL2_vorticity_eq_openPeriodicVorticityFourierMode
      solution t coordinate parent
  rw [smoothSliceFourierL2_apply] at homegaMode
  change vectorSpatialFourierCoeff omega homega.continuous homegaPeriodic
    parent coordinate = _ at homegaMode
  rw [homegaMode]
  congr 1

/-- The complete physical strain reading is the scalar pairing with the source components above. -/
theorem openPeriodicFullStrainReading_eq_fullVortexStretchingSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullStrainReading solution t q =
      ∑ output : Fin 3,
        openPeriodicComplexVorticityAt solution t q output *
          fullVortexStretchingSourceComponent solution t output q := by
  let J : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicTorusJacobianArraySlice solution t q component coordinate
  rw [openPeriodicFullStrainReading]
  change complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart J) = _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  unfold complexStretchingReading complexDot dotProduct
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [fullVortexStretchingSourceComponent_apply]
  rfl

/-- Componentwise scalar Parseval for the complete unweighted physical stretching source. -/
theorem integral_openPeriodicFullStrainReading_eq_component_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (∫ q : SpatialTorus, openPeriodicFullStrainReading solution t q) =
      ∑ output : Fin 3, ∑' frequency : SpatialFrequency,
        conj (openPeriodicVorticityFourierMode solution t frequency output) *
          (∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
            openPeriodicVorticityFourierMode solution t parent coordinate *
              (openVelocityDirectionalDerivativeH3State
                solution t coordinate output).1 (frequency - parent)) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun q ↦
    openPeriodicFullStrainReading_eq_fullVortexStretchingSource solution t q)]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro output _houtput
    let left := openPeriodicVorticityScalarField solution t output
    let right := fullVortexStretchingSourceComponent solution t output
    have hparseval := tsum_conj_mFourierCoeff_mul_eq_integral left right
    have hleft (q : SpatialTorus) : conj (left q) = left q := by
      simp [left, openPeriodicVorticityScalarField,
        complexTorusVorticitySlice, complexifySpace]
    calc
      (∫ q : SpatialTorus,
          openPeriodicComplexVorticityAt solution t q output *
            fullVortexStretchingSourceComponent solution t output q) =
        ∫ q : SpatialTorus, conj (left q) * right q := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [hleft]
          rfl
      _ = ∑' frequency : SpatialFrequency,
          conj (openPeriodicVorticityFourierMode solution t frequency output) *
            (∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
              openPeriodicVorticityFourierMode solution t parent coordinate *
                (openVelocityDirectionalDerivativeH3State
                  solution t coordinate output).1 (frequency - parent)) := by
        rw [← hparseval]
        apply tsum_congr
        intro frequency
        rw [mFourierCoeff_openPeriodicVorticityScalarField]
        rw [mFourierCoeff_fullVortexStretchingSourceComponent]
  · intro output _houtput
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          openPeriodicComplexVorticityAt solution t q output *
            fullVortexStretchingSourceComponent solution t output q
        continuous_toFun := by
          change Continuous (fun q : SpatialTorus ↦
            complexTorusVorticitySlice solution t q output *
              fullVortexStretchingSourceComponent solution t output q)
          exact ((continuous_apply output).comp
            (complexTorusVorticitySlice solution t).continuous).mul
              (fullVortexStretchingSourceComponent solution t output).continuous }

/-! ## Complete output-parent Parseval assembly -/

/-- The complete unsymmetrized first phase before taking its real symmetric receiver. -/
def completeFullStretchingFirstPhaseWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    ∑ output : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address

/-- Absolute summability of the complete first-phase population. -/
theorem summable_completeFullStretchingFirstPhasePopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteStretchingAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address := by
  have hcoordinates : Summable fun address : CompleteStretchingAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_norm_completeOpenVorticityStretchingCoordinateFace
      solution t coordinate output
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    hcoordinates
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _)

/-- One output/component Fourier pairing is exactly its coordinate-parent first-phase fibre. -/
theorem fullVortexStretchingSource_pairing_eq_parentFibres
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) (output : Fin 3) :
    conj (openPeriodicVorticityFourierMode solution t frequency output) *
        (∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
          openPeriodicVorticityFourierMode solution t parent coordinate *
            (openVelocityDirectionalDerivativeH3State
              solution t coordinate output).1 (frequency - parent)) =
      ∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output (frequency, parent) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [← tsum_mul_left]
  apply tsum_congr
  intro parent
  unfold completeOpenVorticityStretchingCoordinateFace
  ring

/-- The complete first phase, regrouped first by physical vector component and then by output
frequency. -/
theorem completeFullStretchingFirstPhaseWork_eq_component_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completeFullStretchingFirstPhaseWork solution t =
      ∑ output : Fin 3, ∑' frequency : SpatialFrequency,
        conj (openPeriodicVorticityFourierMode solution t frequency output) *
          (∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
            openPeriodicVorticityFourierMode solution t parent coordinate *
              (openVelocityDirectionalDerivativeH3State
                solution t coordinate output).1 (frequency - parent)) := by
  let face : Fin 3 → Fin 3 → CompleteStretchingAddress → ℂ :=
    fun output coordinate address ↦
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address
  have hface (output coordinate : Fin 3) :
      Summable fun address : CompleteStretchingAddress ↦
        face output coordinate address :=
    (summable_norm_completeOpenVorticityStretchingCoordinateFace
      solution t coordinate output).of_norm
  have hfaceOuter (output coordinate : Fin 3) :
      Summable fun frequency : SpatialFrequency ↦
        ∑' parent : SpatialFrequency, face output coordinate (frequency, parent) :=
    (hface output coordinate).prod
  have hcomponent (output : Fin 3) :
      Summable fun frequency : SpatialFrequency ↦
        ∑ coordinate : Fin 3, ∑' parent : SpatialFrequency,
          face output coordinate (frequency, parent) := by
    apply summable_sum
    intro coordinate _hcoordinate
    exact hfaceOuter output coordinate
  have haddressComponents : ∀ output ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun address : CompleteStretchingAddress ↦
        ∑ coordinate : Fin 3, face output coordinate address := by
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    exact hface output coordinate
  have haddressCoordinates (output : Fin 3) :
      ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
        Summable fun address : CompleteStretchingAddress ↦
          face output coordinate address := by
    intro coordinate _hcoordinate
    exact hface output coordinate
  unfold completeFullStretchingFirstPhaseWork
  change (∑' address : CompleteStretchingAddress,
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        face output coordinate address) = _
  rw [Summable.tsum_finsetSum haddressComponents]
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [Summable.tsum_finsetSum (haddressCoordinates output)]
  have hproduct :
      (∑ coordinate : Fin 3,
          ∑' address : CompleteStretchingAddress,
            face output coordinate address) =
        ∑ coordinate : Fin 3,
          ∑' frequency : SpatialFrequency,
            ∑' parent : SpatialFrequency,
              face output coordinate (frequency, parent) := by
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    exact (hface output coordinate).tsum_prod
  rw [hproduct]
  rw [← Summable.tsum_finsetSum (fun coordinate _hcoordinate ↦
    hfaceOuter output coordinate)]
  apply tsum_congr
  intro frequency
  rw [fullVortexStretchingSource_pairing_eq_parentFibres]

/-- Simultaneous frequency negation makes the conjugate complete first phase equal the first
phase itself. -/
theorem tsum_completeFullStretching_conjFirstPhase_eq_firstPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (∑' address : CompleteStretchingAddress,
      conj (∑ output : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address)) =
      completeFullStretchingFirstPhaseWork solution t := by
  let first : CompleteStretchingAddress → ℂ := fun address ↦
    ∑ output : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address
  let reverse : CompleteStretchingAddress → ℂ := fun address ↦
    conj (first address)
  have hreindex :
      (∑' address : CompleteStretchingAddress,
        reverse (completeStretchingNegEquiv address)) =
      ∑' address : CompleteStretchingAddress, reverse address :=
    completeStretchingNegEquiv.tsum_eq reverse
  have hpoint (address : CompleteStretchingAddress) :
      reverse (completeStretchingNegEquiv address) = first address := by
    change conj (first (-address.1, -address.2)) = first address
    rw [show first (-address.1, -address.2) = conj (first address) by
      exact completeStretchingFirstPhase_neg solution t address]
    simp
  change (∑' address : CompleteStretchingAddress, reverse address) =
    ∑' address : CompleteStretchingAddress, first address
  rw [← hreindex]
  exact tsum_congr hpoint

/-- The complete first phase is already real after the full address population is retained. -/
theorem completeFullStretchingFirstPhaseWork_eq_completeFullStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completeFullStretchingFirstPhaseWork solution t =
      completeFullStretchingPopulation solution t := by
  let first : CompleteStretchingAddress → ℂ := fun address ↦
    ∑ output : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address
  let reverse : CompleteStretchingAddress → ℂ := fun address ↦
    conj (first address)
  have hfirst : Summable first :=
    summable_completeFullStretchingFirstPhasePopulation solution t
  have hreverse : Summable reverse := by
    apply Summable.of_norm
    exact hfirst.norm.congr (fun address ↦ by
      simp only [first, reverse, starRingEnd_apply, norm_star])
  have hreverseEq : (∑' address, reverse address) =
      ∑' address, first address := by
    simpa only [first, reverse, completeFullStretchingFirstPhaseWork] using
      tsum_completeFullStretching_conjFirstPhase_eq_firstPhase solution t
  unfold completeFullStretchingFirstPhaseWork
    completeFullStretchingPopulation
  change (∑' address, first address) =
    ∑' address : CompleteStretchingAddress,
      (1 / 2 : ℂ) * (first address + reverse address)
  calc
    (∑' address, first address) =
        (1 / 2 : ℂ) *
          ((∑' address, first address) + ∑' address, reverse address) := by
      rw [hreverseEq]
      ring
    _ = ∑' address : CompleteStretchingAddress,
        (1 / 2 : ℂ) * (first address + reverse address) := by
      rw [← hfirst.tsum_add hreverse, tsum_mul_left]
    _ = ∑' address : CompleteStretchingAddress,
        completeOpenVorticityStretchingFace solution t address := by
      apply tsum_congr
      intro address
      unfold completeOpenVorticityStretchingFace
      rfl

/-- **Exact full spatial Parseval join.**  The complete unweighted output-parent population is
the integral of the actual full strain reading. -/
theorem integral_openPeriodicFullStrainReading_eq_completeFullStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (∫ q : SpatialTorus, openPeriodicFullStrainReading solution t q) =
      completeFullStretchingPopulation solution t := by
  rw [integral_openPeriodicFullStrainReading_eq_component_tsum]
  rw [← completeFullStretchingFirstPhaseWork_eq_component_tsum]
  exact completeFullStretchingFirstPhaseWork_eq_completeFullStretchingPopulation
    solution t

/-- Spatial integration on the genuine torus is the periodic cube vortex-stretching receiver. -/
theorem integral_openPeriodicPhysicalVortexStretchingAt_eq_periodicVortexStretching
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (∫ q : SpatialTorus,
      openPeriodicPhysicalVortexStretchingAt solution t q) =
      periodicVortexStretching velocity t.1 := by
  let signedField : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦ openPeriodicPhysicalVortexStretchingAt solution t q
    continuous_toFun := by
      unfold openPeriodicPhysicalVortexStretchingAt openPeriodicTorusJacobianSlice
      fun_prop }
  have hchart := integral_euclideanToSpatialTorus_unitCube signedField
  simp only [MeasureTheory.volume_pi, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] at hchart
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  calc
    (∫ q : SpatialTorus,
        openPeriodicPhysicalVortexStretchingAt solution t q) =
      ∫ q : SpatialTorus, signedField q := rfl
    _ = ∫ x in unitCube,
        signedField (euclideanToSpatialTorus x) := hchart.symm
    _ = periodicVortexStretching velocity t.1 := by
      unfold periodicVortexStretching
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      exact openPeriodicPhysicalVortexStretchingAt_projection solution t x

/-- The real receiver of the complete Fourier population is the literal signed physical vortex
stretching term in the periodic enstrophy law. -/
theorem completeFullStretchingPopulation_re_eq_periodicVortexStretching
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (completeFullStretchingPopulation solution t).re =
      periodicVortexStretching velocity t.1 := by
  have hintegrable : Integrable (fun q : SpatialTorus ↦
      (openPeriodicPhysicalVortexStretchingAt solution t q : ℂ)) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          (openPeriodicPhysicalVortexStretchingAt solution t q : ℂ)
        continuous_toFun := by
          unfold openPeriodicPhysicalVortexStretchingAt openPeriodicTorusJacobianSlice
          fun_prop }
  have hphysical : completeFullStretchingPopulation solution t =
      ∫ q : SpatialTorus,
        (openPeriodicPhysicalVortexStretchingAt solution t q : ℂ) := by
    rw [← integral_openPeriodicFullStrainReading_eq_completeFullStretchingPopulation]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q ↦
      openPeriodicFullStrainReading_eq_physical solution t q
  rw [hphysical]
  change Complex.reCLM
    (∫ q : SpatialTorus,
      (openPeriodicPhysicalVortexStretchingAt solution t q : ℂ)) = _
  rw [← Complex.reCLM.integral_comp_comm hintegrable]
  exact integral_openPeriodicPhysicalVortexStretchingAt_eq_periodicVortexStretching
    solution t

/-! ## The retained scale-zero reconstruction fibre -/

/-- Exactly the two scale-zero faces omitted by the cofinal cumulative multiplier. -/
def completeScaleZeroLinearWorkBoundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℂ :=
  completeLowPassStretchingBoundary solution t +
    (1 / 2 : ℂ) *
      (completeLowPassTransportBoundary solution t +
        conj (completeLowPassTransportBoundary solution t))

/-- **Exact pointwise cofinal receiver.**  The complete cofinal work is physical vortex
stretching minus the retained scale-zero boundary, with no magnitude quotient. -/
theorem completeCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (completeCofinalLinearMultiplierWork solution t).re =
      periodicVortexStretching velocity t.1 -
        (completeScaleZeroLinearWorkBoundary solution t).re := by
  unfold completeCofinalLinearMultiplierWork completeScaleZeroLinearWorkBoundary
  simp only [Complex.sub_re, Complex.add_re]
  rw [completeFullStretchingPopulation_re_eq_periodicVortexStretching]
  ring

/-- The same scale-zero fibre in the compact endpoint-projection chart. -/
def compactScaleZeroLinearWorkBoundary
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) : ℂ :=
  completeScaleZeroLinearWorkBoundary solution
    (compactInteriorTime ha hab hbT time)

theorem compactCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    (compactCofinalLinearMultiplierWork solution ha hab hbT time).re =
      periodicVortexStretching velocity
          (compactInteriorTime ha hab hbT time).1 -
        (compactScaleZeroLinearWorkBoundary
          solution ha hab hbT time).re := by
  exact completeCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero
    solution (compactInteriorTime ha hab hbT time)

/-! ## Compact time integration and the exact enstrophy join -/

/-- The strongest unconditional compact-time receiver keeps stretching and its scale-zero
reconstruction fibre under one signed integral.  This form needs no separate integrability
assumption for either summand. -/
def compactCofinalPhysicalResidualRealIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  ∫ time in a..b,
    periodicVortexStretching velocity time -
      (compactScaleZeroLinearWorkBoundary
        solution ha hab hbT time).re

/-- **Exact unconditional compact cofinal identity.**  The real part of the complex cofinal
work integral is the signed integral of physical vortex stretching minus the complete
scale-zero fibre.  No independent strand receipt or magnitude quotient is used. -/
theorem compactCofinalLinearMultiplierWorkRealIntegral_eq_physicalResidual
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    compactCofinalLinearMultiplierWorkRealIntegral solution ha hab hbT =
      compactCofinalPhysicalResidualRealIntegral solution ha hab hbT := by
  unfold compactCofinalLinearMultiplierWorkRealIntegral
    compactCofinalLinearMultiplierWorkIntegral
    compactCofinalPhysicalResidualRealIntegral
  have hcofinal := intervalIntegrable_compactCofinalLinearMultiplierWork
    solution ha hab hbT
  change Complex.reCLM
    (∫ time in a..b,
      compactCofinalLinearMultiplierWork solution ha hab hbT time) = _
  rw [← Complex.reCLM.intervalIntegral_comp_comm hcofinal]
  apply intervalIntegral.integral_congr
  intro time htime
  rw [uIcc_of_le hab] at htime
  change (compactCofinalLinearMultiplierWork
      solution ha hab hbT time).re = _
  rw [compactCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero]
  rw [compactInteriorTime_eq ha hab hbT htime]

/-- The real cofinal integrand inherits interval integrability from the complete complex
cofinal work without collapsing any of its reconstruction data. -/
theorem intervalIntegrable_compactCofinalLinearMultiplierWork_re
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable
      (fun time ↦
        (compactCofinalLinearMultiplierWork solution ha hab hbT time).re)
      volume a b := by
  have hcofinal := intervalIntegrable_compactCofinalLinearMultiplierWork
    solution ha hab hbT
  exact ⟨Complex.reCLM.integrableOn_comp hcofinal.1,
    Complex.reCLM.integrableOn_comp hcofinal.2⟩

/-- The retained scale-zero fibre integrated separately.  This separation is used only after
the existing source-specific enstrophy strands have supplied their exact interval-integrability
receipt. -/
def compactScaleZeroLinearWorkBoundaryRealIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  ∫ time in a..b,
    (compactScaleZeroLinearWorkBoundary solution ha hab hbT time).re

/-- Once physical stretching is independently interval-integrable, the exact pointwise cofinal
identity itself proves interval integrability of the scale-zero reconstruction fibre. -/
theorem intervalIntegrable_compactScaleZeroLinearWorkBoundary_re
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hstretching :
      IntervalIntegrable (periodicVortexStretching velocity) volume a b) :
    IntervalIntegrable
      (fun time ↦
        (compactScaleZeroLinearWorkBoundary solution ha hab hbT time).re)
      volume a b := by
  have hdiff := hstretching.sub
    (intervalIntegrable_compactCofinalLinearMultiplierWork_re
      solution ha hab hbT)
  apply hdiff.congr_uIoo
  intro time htime
  rw [uIoo_of_le hab] at htime
  have htimeIcc : time ∈ Icc a b := ⟨htime.1.le, htime.2.le⟩
  have hpoint := compactCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero
    solution ha hab hbT time
  rw [compactInteriorTime_eq ha hab hbT htimeIcc] at hpoint
  linarith

/-- With the existing exact stretching receipt, the unconditional combined integral separates
into physical stretching minus the scale-zero boundary integral. -/
theorem compactCofinalLinearMultiplierWorkRealIntegral_eq_stretching_sub_scaleZero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hstretching :
      IntervalIntegrable (periodicVortexStretching velocity) volume a b) :
    compactCofinalLinearMultiplierWorkRealIntegral solution ha hab hbT =
      (∫ time in a..b, periodicVortexStretching velocity time) -
        compactScaleZeroLinearWorkBoundaryRealIntegral
          solution ha hab hbT := by
  rw [compactCofinalLinearMultiplierWorkRealIntegral_eq_physicalResidual]
  unfold compactCofinalPhysicalResidualRealIntegral
    compactScaleZeroLinearWorkBoundaryRealIntegral
  rw [intervalIntegral.integral_sub hstretching
    (intervalIntegrable_compactScaleZeroLinearWorkBoundary_re
      solution ha hab hbT hstretching)]

/-- **Exact endpoint enstrophy form.**  The pre-existing source-specific strand receipt is the
only additional hypothesis required to split the unconditional combined receiver.  In the
unforced equation the curl-forcing face vanishes, leaving endpoint enstrophy, accumulated viscous
dissipation, and the complete scale-zero reconstruction fibre. -/
theorem compactCofinalLinearMultiplierWorkRealIntegral_eq_endpointEnstrophy
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt :
      EnstrophyStrandIntervalReceipt
        (0 : VelocityField) velocity a b) :
    compactCofinalLinearMultiplierWorkRealIntegral solution ha hab hbT =
      periodicEnstrophy velocity b - periodicEnstrophy velocity a +
        nu * (∫ time in a..b,
          periodicVorticityDissipation velocity time) -
        compactScaleZeroLinearWorkBoundaryRealIntegral
          solution ha hab hbT := by
  rw [compactCofinalLinearMultiplierWorkRealIntegral_eq_stretching_sub_scaleZero
    solution ha hab hbT receipt.stretching]
  have hlaw := intervalEnstrophyCurrent_add_dissipation_eq_exterior
    solution ha hab hbT receipt
  unfold intervalCurrent stretchingForcingExteriorCurrent at hlaw
  simp only [periodicCurlForcingWork_zero, intervalIntegral.integral_zero,
    add_zero] at hlaw
  linarith

section Audit

#print axioms integral_openPeriodicFullStrainReading_eq_completeFullStretchingPopulation
#print axioms completeFullStretchingPopulation_re_eq_periodicVortexStretching
#print axioms compactCofinalLinearMultiplierWork_re_eq_physical_sub_scaleZero
#print axioms compactCofinalLinearMultiplierWorkRealIntegral_eq_physicalResidual
#print axioms compactCofinalLinearMultiplierWorkRealIntegral_eq_endpointEnstrophy

end Audit

end Soma.Holonics.Millennium.NavierStokesCofinalWorkEnstrophyJoin
