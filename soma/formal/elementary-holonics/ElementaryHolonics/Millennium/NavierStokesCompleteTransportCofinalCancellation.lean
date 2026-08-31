import ElementaryHolonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Complete transport cancellation through a cofinal multiplier aperture

**[proved-derived; formal-checked]**  The finite multiplier-crossing faces do not cancel at a
fixed aperture.  This owner first forms the complete ordered transport population, proves that
exchange of the transported and receiving pins is an involution, and performs the constant-weight
cancellation only under an explicit absolute-summability hypothesis.  Tannery's theorem then
passes the cumulative de la Vallée Poussin multiplier to its cofinal limit.

The surviving limit is the negative scale-zero low-pass transport boundary.  Every finite output
cube retains its exact output tail; no finite aperture is identified with the complete population,
and no terminal Navier--Stokes estimate is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## The complete closed transport population and its exchange -/

/-- An ordered complete transport address retains the advecting and transported pins. -/
abbrev CompleteTransportAddress := SpatialFrequency × SpatialFrequency

/-- Closure determines the receiving pin without quotienting either parent occurrence. -/
def completeTransportReceiver (address : CompleteTransportAddress) : SpatialFrequency :=
  -address.1 - address.2

/-- Every ordered address induces a literally closed addressed Fourier triad. -/
def completeTransportTriad (address : CompleteTransportAddress) :
    AddressedClosedFourierTriad where
  advecting := address.1
  transported := address.2
  receiver := completeTransportReceiver address
  closed := by
    unfold completeTransportReceiver
    abel

/-- Exchange the transported and receiving pins while retaining the advecting pin. -/
def completeTransportExchange : CompleteTransportAddress ≃ CompleteTransportAddress where
  toFun address := (address.1, completeTransportReceiver address)
  invFun address := (address.1, completeTransportReceiver address)
  left_inv := by
    intro address
    apply Prod.ext
    · rfl
    · funext coordinate
      simp [completeTransportReceiver]
  right_inv := by
    intro address
    apply Prod.ext
    · rfl
    · funext coordinate
      simp [completeTransportReceiver]

@[simp]
theorem completeTransportExchange_first (address : CompleteTransportAddress) :
    (completeTransportExchange address).1 = address.1 := rfl

@[simp]
theorem completeTransportExchange_second (address : CompleteTransportAddress) :
    (completeTransportExchange address).2 = completeTransportReceiver address := rfl

@[simp]
theorem completeTransportReceiver_exchange (address : CompleteTransportAddress) :
    completeTransportReceiver (completeTransportExchange address) = address.2 := by
  funext coordinate
  simp [completeTransportReceiver, completeTransportExchange]

/-- The actual signed one-face transport occurrence before any multiplier or norm receiver. -/
def completeOpenVorticityTransportFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) : ℂ :=
  triadicEnergyFace address.1 address.2
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVorticityFourierMode solution t address.2)
    (openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address))

/-- Exchanging transported and receiving pins negates the actual face, pointwise. -/
theorem completeOpenVorticityTransportFace_exchange
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) :
    completeOpenVorticityTransportFace solution t
        (completeTransportExchange address) =
      -completeOpenVorticityTransportFace solution t address := by
  have hcancel := exchanged_triadicEnergyFace_cancel
    (completeTransportTriad address)
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVorticityFourierMode solution t address.2)
    (openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address))
    (openPeriodicVelocityFourierMode_divergenceFree solution t address.1)
  exact eq_neg_of_add_eq_zero_right (by simpa [completeOpenVorticityTransportFace,
    completeTransportTriad] using hcancel)

/-! ## Native smooth-H³ proof of absolute summability -/

/-- The actual vorticity slice, retained as an old unweighted smooth `H³` coefficient state. -/
def openVorticityH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
      Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart.PeriodicVectorSobolevThree :=
  smoothSliceH3State (fun x ↦ vorticityField velocity x t.1)
    (openPeriodicSolutionOn_vorticitySlice_contDiff solution t)
    (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)

/-- One addressed spatial derivative of the actual vorticity slice, again retained in smooth
`H³`.  Smoothness supplies this stronger carrier without a terminal estimate. -/
def openVorticityDirectionalDerivativeH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (coordinate : Fin 3) :
      Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart.PeriodicVectorSobolevThree :=
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ (⊤ : ℕ∞) omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  smoothSliceH3State (spatialDirectionalJet omega coordinate)
    (spatialDirectionalJet_contDiff omega homega coordinate)
    (spatialDirectionalJet_isOnePeriodic omega hperiodic coordinate)

theorem openVorticityDirectionalDerivativeH3State_apply_eq_smoothSlice
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (coordinate output : Fin 3)
    (frequency : SpatialFrequency) :
    (openVorticityDirectionalDerivativeH3State solution t coordinate output).1 frequency =
      smoothSliceFourierL2
        (spatialDirectionalJet (fun x ↦ vorticityField velocity x t.1) coordinate)
        (spatialDirectionalJet_contDiff (fun x ↦ vorticityField velocity x t.1)
          (openPeriodicSolutionOn_vorticitySlice_contDiff solution t) coordinate)
        (spatialDirectionalJet_isOnePeriodic (fun x ↦ vorticityField velocity x t.1)
          (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2) coordinate)
        output frequency := by
  rfl

theorem smoothSliceFourierL2_vorticity_eq_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : Fin 3) (frequency : SpatialFrequency) :
    smoothSliceFourierL2 (fun x ↦ vorticityField velocity x t.1)
        (openPeriodicSolutionOn_vorticitySlice_contDiff solution t)
        (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
        output frequency =
      openPeriodicVorticityFourierMode solution t frequency output := by
  change openPeriodicVorticityComponentFourierL2 solution t output frequency = _
  exact openPeriodicVorticityComponentFourierL2_apply solution t output frequency

/-- The velocity coefficients are absolutely summable componentwise on the actual slice. -/
theorem summable_norm_openPeriodicVelocityFourierMode_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (component : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      ‖openPeriodicVelocityFourierMode solution t frequency component‖ := by
  simpa only [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode] using
    (periodicVectorSobolevThree_hasAbsolutelySummableComponents
      (openVelocityH3State solution t) component)

/-- Every addressed differentiated-vorticity component is absolutely summable. -/
theorem summable_norm_openVorticityDirectionalDerivativeH3State_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (coordinate output : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      ‖(openVorticityDirectionalDerivativeH3State
        solution t coordinate output).1 frequency‖ :=
  periodicVectorSobolevThree_hasAbsolutelySummableComponents
    (openVorticityDirectionalDerivativeH3State solution t coordinate) output

/-- One coordinate-resolved complete transport occurrence. -/
def completeOpenVorticityTransportCoordinateFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (coordinate output : Fin 3)
    (address : CompleteTransportAddress) : ℂ :=
  openPeriodicVelocityFourierMode solution t address.1 coordinate *
    (openVorticityDirectionalDerivativeH3State
      solution t coordinate output).1 address.2 *
    openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address) output

/-- The finite sum of the native derivative occurrences is exactly the established advective
interaction component.  This uses the inherited Fourier-jet constraint rather than restating its
coordinate scale as a new scalar constant. -/
theorem sum_velocity_mul_openVorticityDirectionalDerivative_eq_advectiveInteraction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (p q : SpatialFrequency) (output : Fin 3) :
    (∑ coordinate : Fin 3,
      openPeriodicVelocityFourierMode solution t p coordinate *
        (openVorticityDirectionalDerivativeH3State
          solution t coordinate output).1 q) =
      complexAdvectiveInteraction p q
        (openPeriodicVelocityFourierMode solution t p)
        (openPeriodicVorticityFourierMode solution t q) output := by
  unfold complexAdvectiveInteraction complexDot dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [openVorticityDirectionalDerivativeH3State_apply_eq_smoothSlice]
  rw [smoothSliceFourierL2_spatialDirectionalJet
    (fun x ↦ vorticityField velocity x t.1)
    (openPeriodicSolutionOn_vorticitySlice_contDiff solution t)
    (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
    coordinate output q]
  rw [smoothSliceFourierL2_vorticity_eq_openPeriodicVorticityFourierMode
    solution t output q]
  simp only [complexFrequencyVector]
  ring

/-- The exact face is the finite coordinate/output sum of native smooth derivative occurrences. -/
theorem completeOpenVorticityTransportFace_eq_sum_coordinateFaces
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) :
    completeOpenVorticityTransportFace solution t address =
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityTransportCoordinateFace
          solution t coordinate output address := by
  simp only [completeOpenVorticityTransportFace, triadicEnergyFace,
    complexDot, dotProduct, completeOpenVorticityTransportCoordinateFace]
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [← sum_velocity_mul_openVorticityDirectionalDerivative_eq_advectiveInteraction
    solution t address.1 address.2 output]
  rw [Finset.sum_mul]

/-- One component coefficient is bounded by the complete actual vorticity `L¹` mass. -/
theorem norm_openPeriodicVorticityFourierMode_component_le_fullMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) (component : Fin 3) :
    ‖openPeriodicVorticityFourierMode solution t frequency component‖ ≤
      ∑' mode : SpatialFrequency,
        complexVectorL1 (openPeriodicVorticityFourierMode solution t mode) := by
  have hcomponent :
      ‖openPeriodicVorticityFourierMode solution t frequency component‖ ≤
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
    exact (norm_le_pi_norm
      (openPeriodicVorticityFourierMode solution t frequency) component).trans
        (norm_complexVector_le_complexVectorL1 _)
  have hsingle :=
    (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t).sum_le_tsum
      {frequency} (fun mode _hmode ↦ complexVectorL1_nonneg _)
  exact hcomponent.trans (by simpa using hsingle)

/-- Each coordinate-resolved complete transport population is absolutely summable on the product
lattice. -/
theorem summable_norm_completeOpenVorticityTransportCoordinateFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (coordinate output : Fin 3) :
    Summable fun address : CompleteTransportAddress ↦
      ‖completeOpenVorticityTransportCoordinateFace
        solution t coordinate output address‖ := by
  let mass : ℝ := ∑' mode : SpatialFrequency,
    complexVectorL1 (openPeriodicVorticityFourierMode solution t mode)
  have hvelocity :=
    summable_norm_openPeriodicVelocityFourierMode_component solution t coordinate
  have hderivative :=
    summable_norm_openVorticityDirectionalDerivativeH3State_component
      solution t coordinate output
  have hproduct : Summable fun address : CompleteTransportAddress ↦
      ‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
        ‖(openVorticityDirectionalDerivativeH3State
          solution t coordinate output).1 address.2‖ :=
    hvelocity.mul_of_nonneg hderivative (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hmajorant := hproduct.mul_right mass
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hmajorant
  rw [completeOpenVorticityTransportCoordinateFace, norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact norm_openPeriodicVorticityFourierMode_component_le_fullMass
    solution t (completeTransportReceiver address) output

/-- **Actual absolute-summability bridge.**  Smooth `H³` coefficient owners for velocity and
each spatial derivative of vorticity majorize the literal complete two-pin transport population.
This discharges the exchange premise without a terminal or summability assumption. -/
theorem summable_norm_completeOpenVorticityTransportFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      ‖completeOpenVorticityTransportFace solution t address‖ := by
  have hmajorant : Summable fun address : CompleteTransportAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityTransportCoordinateFace
          solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_norm_completeOpenVorticityTransportCoordinateFace
      solution t coordinate output
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hmajorant
  rw [completeOpenVorticityTransportFace_eq_sum_coordinateFaces]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _)

/-! ## Absolute exchange and constant-weight cancellation -/

/-- A summable population which is negated by a fixed-point-free-or-not involution has zero
complete sum.  The proof reindexes the complete sum; it is not a finite pairing argument. -/
theorem tsum_eq_zero_of_equiv_exchange_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {index : Type*} (exchange : index ≃ index) (face : index → E)
    (hsummable : Summable fun address ↦ ‖face address‖)
    (hexchange : ∀ address, face (exchange address) = -face address) :
    (∑' address, face address) = 0 := by
  have hface : Summable face := hsummable.of_norm
  have hreindex : (∑' address, face (exchange address)) = ∑' address, face address :=
    exchange.tsum_eq face
  have hneg : (∑' address, face (exchange address)) = -∑' address, face address := by
    rw [tsum_congr hexchange, tsum_neg]
  have hopposite : (∑' address, face address) = -∑' address, face address := by
    calc
      (∑' address, face address) = ∑' address, face (exchange address) := hreindex.symm
      _ = -∑' address, face address := hneg
  have htwo : (2 : ℝ) • (∑' address, face address) = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp hopposite)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Constant-weight complete vorticity transport cancels only after the explicit absolute
summability premise has licensed the infinite exchange. -/
theorem tsum_completeOpenVorticityTransportFace_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T)
    (hsummable : Summable fun address : CompleteTransportAddress ↦
      ‖completeOpenVorticityTransportFace solution t address‖) :
    (∑' address, completeOpenVorticityTransportFace solution t address) = 0 := by
  exact tsum_eq_zero_of_equiv_exchange_neg completeTransportExchange
    (completeOpenVorticityTransportFace solution t) hsummable
    (completeOpenVorticityTransportFace_exchange solution t)

/-- The actual smooth solution supplies the absolute exchange premise internally. -/
theorem tsum_completeOpenVorticityTransportFace_actual_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    (∑' address, completeOpenVorticityTransportFace solution t address) = 0 :=
  tsum_completeOpenVorticityTransportFace_eq_zero solution t
    (summable_norm_completeOpenVorticityTransportFace solution t)

/-! ## Cofinal cumulative multiplier and retained low-pass boundary -/

/-- The complete transport population observed through the cumulative depth multiplier. -/
def completeCumulativeTransportContribution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑' address : CompleteTransportAddress,
    (finiteDepthBoundaryWeight depth address.2 : ℂ) *
      completeOpenVorticityTransportFace solution t address

/-- The scale-zero low-pass transport boundary which survives the cofinal cancellation. -/
def completeLowPassTransportBoundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℂ :=
  ∑' address : CompleteTransportAddress,
    (tensorValleePoussinWeight (dyadicHodgeParameter 0) address.2 : ℂ) *
      completeOpenVorticityTransportFace solution t address

/-- Every fixed frequency eventually lies in the unit plateau of the dyadic low-pass multiplier. -/
theorem eventually_tensorValleePoussinWeight_dyadic_eq_one
    (frequency : SpatialFrequency) :
    ∀ᶠ depth in atTop,
      tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency = 1 := by
  obtain ⟨radius, hfrequency⟩ := exists_mem_frequencyCube frequency
  have hgrowth : Tendsto dyadicRadius atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  filter_upwards [hgrowth.eventually (eventually_ge_atTop radius)] with depth hdepth
  apply tensorValleePoussinWeight_eq_one
  rw [dyadicHodgeParameter_add_one]
  exact frequencyCube_mono hdepth hfrequency

/-- The cumulative multiplier is uniformly bounded by one in absolute value. -/
theorem abs_finiteDepthBoundaryWeight_le_one
    (depth : ℕ) (frequency : SpatialFrequency) :
    |finiteDepthBoundaryWeight depth frequency| ≤ 1 := by
  have hdepth := tensorValleePoussinWeight_mem_unitInterval
    (dyadicHodgeParameter depth) frequency
  have hzero := tensorValleePoussinWeight_mem_unitInterval
    (dyadicHodgeParameter 0) frequency
  unfold finiteDepthBoundaryWeight
  rw [abs_le]
  constructor <;> linarith

/-- The retained scale-zero multiplier is uniformly bounded by one. -/
theorem abs_tensorValleePoussinWeight_zero_le_one
    (frequency : SpatialFrequency) :
    |tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency| ≤ 1 := by
  have hweight := tensorValleePoussinWeight_mem_unitInterval
    (dyadicHodgeParameter 0) frequency
  rw [abs_of_nonneg hweight.1]
  exact hweight.2

/-- **Complete cofinal transport cancellation.**  Under absolute summability of the literal
one-face population, the cumulative depth contribution converges to the negative scale-zero
low-pass boundary.  The constant-weight complete face is cancelled only inside this proof, after
absolute convergence and reindexing have been supplied. -/
theorem tendsto_completeCumulativeTransportContribution_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T)
    (hsummable : Summable fun address : CompleteTransportAddress ↦
      ‖completeOpenVorticityTransportFace solution t address‖) :
    Tendsto (completeCumulativeTransportContribution solution t) atTop
      (nhds (-completeLowPassTransportBoundary solution t)) := by
  let face : CompleteTransportAddress → ℂ :=
    completeOpenVorticityTransportFace solution t
  let lowWeight : CompleteTransportAddress → ℂ := fun address ↦
    (tensorValleePoussinWeight (dyadicHodgeParameter 0) address.2 : ℂ)
  have hpointwise (address : CompleteTransportAddress) :
      Tendsto
        (fun depth : ℕ ↦
          (finiteDepthBoundaryWeight depth address.2 : ℂ) * face address)
        atTop (nhds ((1 - lowWeight address) * face address)) := by
    have heventual := eventually_tensorValleePoussinWeight_dyadic_eq_one address.2
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [heventual] with depth hdepth
    simp [finiteDepthBoundaryWeight, hdepth, lowWeight]
  have hbound : ∀ᶠ depth in atTop, ∀ address : CompleteTransportAddress,
      ‖(finiteDepthBoundaryWeight depth address.2 : ℂ) * face address‖ ≤
        ‖face address‖ := by
    filter_upwards [] with depth address
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_finiteDepthBoundaryWeight_le_one depth address.2)
  have htannery := tendsto_tsum_of_dominated_convergence
    hsummable hpointwise hbound
  have hlowNorm : Summable fun address : CompleteTransportAddress ↦
      ‖lowWeight address * face address‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hsummable
    dsimp only [lowWeight]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_tensorValleePoussinWeight_zero_le_one address.2)
  have hface : Summable face := hsummable.of_norm
  have hlow : Summable fun address ↦ lowWeight address * face address :=
    hlowNorm.of_norm
  have htarget :
      (∑' address, (1 - lowWeight address) * face address) =
        -completeLowPassTransportBoundary solution t := by
    have hreexpress (address : CompleteTransportAddress) :
        (1 - lowWeight address) * face address =
          face address - lowWeight address * face address := by ring
    rw [tsum_congr hreexpress, hface.tsum_sub hlow]
    rw [tsum_completeOpenVorticityTransportFace_eq_zero solution t hsummable]
    change 0 - (∑' address, lowWeight address * face address) =
      -(∑' address, lowWeight address * face address)
    exact zero_sub _
  change Tendsto
    (fun depth ↦ ∑' address : CompleteTransportAddress,
      (finiteDepthBoundaryWeight depth address.2 : ℂ) * face address)
    atTop (nhds (-completeLowPassTransportBoundary solution t))
  rw [← htarget]
  exact htannery

/-- Actual smooth-solution specialization of the complete cofinal transport passage. -/
theorem tendsto_completeCumulativeTransportContribution_actual_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto (completeCumulativeTransportContribution solution t) atTop
      (nhds (-completeLowPassTransportBoundary solution t)) :=
  tendsto_completeCumulativeTransportContribution_atTop solution t
    (summable_norm_completeOpenVorticityTransportFace solution t)

/-! ## Exact finite-output tail and reconstruction fibre -/

/-- A cofinal finite output aperture retains both independent address pins. -/
def completeTransportOutputAperture (radius : ℕ) :
    Finset CompleteTransportAddress :=
  frequencyCube radius ×ˢ frequencyCube radius

theorem completeTransportOutputAperture_mono :
    Monotone completeTransportOutputAperture := by
  intro inner outer hinner
  exact Finset.product_subset_product
    (frequencyCube_mono hinner) (frequencyCube_mono hinner)

/-- The two-pin cube family is cofinal in the complete ordered address population. -/
theorem tendsto_completeTransportOutputAperture_atTop :
    Tendsto completeTransportOutputAperture atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro population
  obtain ⟨radius, hradius⟩ :
      ∃ radius : ℕ, population ⊆ completeTransportOutputAperture radius := by
    classical
    induction population using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert address population haddress ih =>
        obtain ⟨populationRadius, hpopulation⟩ := ih
        obtain ⟨firstRadius, hfirst⟩ := exists_mem_frequencyCube address.1
        obtain ⟨secondRadius, hsecond⟩ := exists_mem_frequencyCube address.2
        let addressRadius := max firstRadius secondRadius
        let radius := max populationRadius addressRadius
        refine ⟨radius, ?_⟩
        intro other hother
        rw [Finset.mem_insert] at hother
        rcases hother with rfl | hother
        · apply Finset.mem_product.2
          constructor
          · exact frequencyCube_mono
              ((Nat.le_max_left firstRadius secondRadius).trans
                (Nat.le_max_right populationRadius addressRadius)) hfirst
          · exact frequencyCube_mono
              ((Nat.le_max_right firstRadius secondRadius).trans
                (Nat.le_max_right populationRadius addressRadius)) hsecond
        · exact completeTransportOutputAperture_mono
            (Nat.le_max_left _ _) (hpopulation hother)
  exact Filter.eventually_atTop.2 ⟨radius, fun later hlater ↦
    hradius.trans (completeTransportOutputAperture_mono hlater)⟩

/-- For every fixed depth, the complete cumulative-weight population is absolutely summable. -/
theorem summable_completeCumulativeTransportPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Summable fun address : CompleteTransportAddress ↦
      (finiteDepthBoundaryWeight depth address.2 : ℂ) *
        completeOpenVorticityTransportFace solution t address := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_norm_completeOpenVorticityTransportFace solution t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (abs_finiteDepthBoundaryWeight_le_one depth address.2)

/-- The exact omitted output tail of a finite address cube. -/
def completeCumulativeTransportOutputTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth radius : ℕ) : ℂ :=
  completeCumulativeTransportContribution solution t depth -
    ∑ address ∈ completeTransportOutputAperture radius,
      (finiteDepthBoundaryWeight depth address.2 : ℂ) *
        completeOpenVorticityTransportFace solution t address

/-- Every finite cube plus its exact output tail reconstructs the complete cumulative transport
contribution.  No claim is made that the tail vanishes at a fixed radius. -/
theorem finiteOutput_add_completeCumulativeTransportOutputTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth radius : ℕ) :
    (∑ address ∈ completeTransportOutputAperture radius,
      (finiteDepthBoundaryWeight depth address.2 : ℂ) *
        completeOpenVorticityTransportFace solution t address) +
      completeCumulativeTransportOutputTail solution t depth radius =
        completeCumulativeTransportContribution solution t depth := by
  unfold completeCumulativeTransportOutputTail
  ring

/-- At fixed multiplier depth, the retained output tail tends to zero only along the cofinal
two-pin aperture. -/
theorem tendsto_completeCumulativeTransportOutputTail_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Tendsto (completeCumulativeTransportOutputTail solution t depth) atTop
      (nhds 0) := by
  let population : CompleteTransportAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth address.2 : ℂ) *
      completeOpenVorticityTransportFace solution t address
  have hsum : Summable population :=
    summable_completeCumulativeTransportPopulation solution t depth
  have hfinite : Tendsto
      (fun radius ↦ ∑ address ∈ completeTransportOutputAperture radius,
        population address) atTop (nhds (∑' address, population address)) :=
    hsum.hasSum.comp tendsto_completeTransportOutputAperture_atTop
  have hconstant : Tendsto (fun _ : ℕ ↦ ∑' address, population address)
      atTop (nhds (∑' address, population address)) := tendsto_const_nhds
  change Tendsto
    (fun radius ↦ (∑' address, population address) -
      ∑ address ∈ completeTransportOutputAperture radius, population address)
    atTop (nhds 0)
  simpa only [sub_self] using hconstant.sub hfinite

/-- The cofinal reconstruction fibre is the cumulative contribution plus the retained low-pass
boundary; the preceding theorem says exactly that this fibre tends to zero. -/
def completeTransportCofinalReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  completeCumulativeTransportContribution solution t depth +
    completeLowPassTransportBoundary solution t

theorem tendsto_completeTransportCofinalReconstructionFiber_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T)
    (hsummable : Summable fun address : CompleteTransportAddress ↦
      ‖completeOpenVorticityTransportFace solution t address‖) :
    Tendsto (completeTransportCofinalReconstructionFiber solution t) atTop
      (nhds 0) := by
  have htransport :=
    tendsto_completeCumulativeTransportContribution_atTop solution t hsummable
  have hboundary : Tendsto
      (fun _ : ℕ ↦ completeLowPassTransportBoundary solution t)
    atTop (nhds (completeLowPassTransportBoundary solution t)) :=
    tendsto_const_nhds
  change Tendsto
    (fun depth ↦ completeCumulativeTransportContribution solution t depth +
      completeLowPassTransportBoundary solution t) atTop (nhds 0)
  simpa only [neg_add_cancel] using htransport.add hboundary

/-- Actual smooth-solution specialization of the vanishing reconstruction fibre. -/
theorem tendsto_completeTransportCofinalReconstructionFiber_actual_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto (completeTransportCofinalReconstructionFiber solution t) atTop
      (nhds 0) :=
  tendsto_completeTransportCofinalReconstructionFiber_atTop solution t
    (summable_norm_completeOpenVorticityTransportFace solution t)

end Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
