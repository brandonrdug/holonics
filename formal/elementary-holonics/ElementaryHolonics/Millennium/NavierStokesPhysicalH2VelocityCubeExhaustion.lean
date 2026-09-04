import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
import ElementaryHolonics.Millennium.NavierStokesOpenFourierSpatialSymbols
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin

/-!
# Cofinal exhaustion of the physical H2 velocity-triad current

**[proved-derived; formal-checked]**  The common three-pin frequency cubes are a genuinely
cofinal family of complete ordered transport addresses.  Smoothness of an actual strict-interior
solution slice supplies absolute coefficient summability after the completed physical `H2`
multiplier, so the exact finite exchange identity survives the cofinal passage.

Grouping the retained address population by output identifies its inner fibre with the literal
complete velocity-advection coefficient.  Negation reality then returns the declared real
physical-current orientation: negative real raw transport is positive one half of the real
completed exchanged swing.  No terminal estimate, time-uniform bound, or continuation claim is
made.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators ComplexConjugate Laplacian

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedReality

/-! ## Smooth carrier for the completed physical multiplier -/

/-- The physical multiplier applied to one actual velocity slice as the literal smooth field
`laplacian (laplacian u) - laplacian u`. -/
def openPhysicalH2MultiplierVelocityH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : PeriodicVectorSobolevThree :=
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let hfirst : ContDiff ℝ (⊤ : ℕ∞) (Δ u) := laplacian_contDiff hu
  let hsecond : ContDiff ℝ (⊤ : ℕ∞) (Δ (Δ u)) := laplacian_contDiff hfirst
  let hperiodicFirst : IsOnePeriodic (Δ u) :=
    laplacian_isOnePeriodic (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic
  let hperiodicSecond : IsOnePeriodic (Δ (Δ u)) :=
    laplacian_isOnePeriodic (hfirst.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodicFirst
  smoothSliceH3State (fun x ↦ Δ (Δ u) x - Δ u x)
    (hsecond.sub hfirst) (fun x coordinate ↦ by
      change Δ (Δ u) (x + EuclideanSpace.single coordinate 1) -
          Δ u (x + EuclideanSpace.single coordinate 1) = Δ (Δ u) x - Δ u x
      rw [hperiodicSecond x coordinate, hperiodicFirst x coordinate])

/-- Vector Fourier coefficients preserve subtraction of smooth periodic fields. -/
theorem vectorSpatialFourierCoeff_sub
    (left right : InitialVelocity)
    (hleft : Continuous left) (hright : Continuous right)
    (hperiodicLeft : IsOnePeriodic left) (hperiodicRight : IsOnePeriodic right)
    (frequency : SpatialFrequency) :
    vectorSpatialFourierCoeff (fun x ↦ left x - right x)
    (hleft.sub hright) (fun x coordinate ↦ by
          change left (x + EuclideanSpace.single coordinate 1) -
              right (x + EuclideanSpace.single coordinate 1) = left x - right x
          rw [hperiodicLeft x coordinate, hperiodicRight x coordinate]) frequency =
      vectorSpatialFourierCoeff left hleft hperiodicLeft frequency -
        vectorSpatialFourierCoeff right hright hperiodicRight frequency := by
  let hsub : IsOnePeriodic (fun x ↦ left x - right x) := fun x coordinate ↦ by
    change left (x + EuclideanSpace.single coordinate 1) -
        right (x + EuclideanSpace.single coordinate 1) = left x - right x
    rw [hperiodicLeft x coordinate, hperiodicRight x coordinate]
  change vectorSpatialFourierCoeff (fun x ↦ left x - right x)
      (hleft.sub hright) hsub frequency = _
  funext component
  change vectorSpatialFourierCoeff (fun x ↦ left x - right x) _ _ frequency component =
    vectorSpatialFourierCoeff left hleft hperiodicLeft frequency component -
      vectorSpatialFourierCoeff right hright hperiodicRight frequency component
  rw [vectorSpatialFourierCoeff_apply (fun x ↦ left x - right x)
      (hleft.sub hright) hsub,
    vectorSpatialFourierCoeff_apply left hleft hperiodicLeft,
    vectorSpatialFourierCoeff_apply right hright hperiodicRight]
  rw [← torusSpatialFourierCoeff_sub]
  congr 1
  ext q
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
  simp [complexVelocityComponent]

/-- The smooth carrier has exactly the completed physical multiplier times each actual velocity
coefficient. -/
theorem openPhysicalH2MultiplierVelocityH3State_apply
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) (frequency : SpatialFrequency) :
    (openPhysicalH2MultiplierVelocityH3State solution t component).1 frequency =
      physicalH2CurlEnergyMultiplier frequency *
        openPeriodicVelocityFourierMode solution t frequency component := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let hfirst : ContDiff ℝ (⊤ : ℕ∞) (Δ u) := laplacian_contDiff hu
  let hsecond : ContDiff ℝ (⊤ : ℕ∞) (Δ (Δ u)) := laplacian_contDiff hfirst
  let hperiodicFirst : IsOnePeriodic (Δ u) :=
    laplacian_isOnePeriodic (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic
  let hperiodicSecond : IsOnePeriodic (Δ (Δ u)) :=
    laplacian_isOnePeriodic (hfirst.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodicFirst
  let hperiodicDifference : IsOnePeriodic (fun x ↦ Δ (Δ u) x - Δ u x) :=
    fun x coordinate ↦ by
      change Δ (Δ u) (x + EuclideanSpace.single coordinate 1) -
          Δ u (x + EuclideanSpace.single coordinate 1) = Δ (Δ u) x - Δ u x
      rw [hperiodicSecond x coordinate, hperiodicFirst x coordinate]
  unfold openPhysicalH2MultiplierVelocityH3State smoothSliceH3State
  dsimp only
  unfold smoothSliceSobolevCoefficients
  change (smoothSliceFourierL2 (fun x ↦ Δ (Δ u) x - Δ u x)
      (hsecond.sub hfirst) hperiodicDifference
      component).1 frequency = _
  rw [smoothSliceFourierL2_apply]
  change vectorSpatialFourierCoeff (fun x ↦ Δ (Δ u) x - Δ u x) _ _ frequency component = _
  rw [vectorSpatialFourierCoeff_sub (Δ (Δ u)) (Δ u)
    hsecond.continuous hfirst.continuous hperiodicSecond hperiodicFirst]
  rw [vectorSpatialFourierCoeff_laplacian_eq_stokes (Δ u) hfirst hperiodicFirst]
  rw [vectorSpatialFourierCoeff_laplacian_eq_stokes u hu hperiodic]
  change ((-(torusStokesEigenvalue frequency : ℂ)) *
      (-(torusStokesEigenvalue frequency : ℂ) *
        vectorSpatialFourierCoeff u hu.continuous hperiodic frequency component) -
      (-(torusStokesEigenvalue frequency : ℂ) *
        vectorSpatialFourierCoeff u hu.continuous hperiodic frequency component)) = _
  change _ = physicalH2CurlEnergyMultiplier frequency *
    vectorSpatialFourierCoeff u hu.continuous hperiodic frequency component
  unfold physicalH2CurlEnergyMultiplier
  push_cast
  ring

/-- Every completed-multiplier velocity component is absolutely summable on a strict-interior
slice. -/
theorem summable_norm_physicalH2CurlEnergyMultiplier_mul_openVelocity_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      ‖physicalH2CurlEnergyMultiplier frequency *
        openPeriodicVelocityFourierMode solution t frequency component‖ := by
  exact (periodicVectorSobolevThree_hasAbsolutelySummableComponents
      (openPhysicalH2MultiplierVelocityH3State solution t) component).congr
    (fun frequency ↦ by rw [openPhysicalH2MultiplierVelocityH3State_apply])

/-! ## Absolute summability of the complete raw address population -/

/-- One coordinate-resolved raw physical velocity-advection occurrence. -/
def completeOpenReceiverWeightedPhysicalH2VelocityCoordinateFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3)
    (address : CompleteTransportAddress) : ℂ :=
  openPeriodicVelocityFourierMode solution t address.1 coordinate *
    (openVelocityDirectionalDerivativeH3State
      solution t coordinate output).1 address.2 *
    (physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
      openPeriodicVelocityFourierMode solution t
        (completeTransportReceiver address) output)

/-- The native differentiated-velocity coordinates reconstruct one literal advective interaction
component. -/
theorem sum_velocity_mul_openVelocityDirectionalDerivative_eq_advectiveInteraction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (p q : SpatialFrequency) (output : Fin 3) :
    (∑ coordinate : Fin 3,
      openPeriodicVelocityFourierMode solution t p coordinate *
        (openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 q) =
      complexAdvectiveInteraction p q
        (openPeriodicVelocityFourierMode solution t p)
        (openPeriodicVelocityFourierMode solution t q) output := by
  unfold complexAdvectiveInteraction complexDot dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [openVelocityDirectionalDerivativeH3State_apply_eq_derivative]
  rw [periodicSobolevThreeDerivative_apply]
  rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
  simp only [complexFrequencyVector]
  ring

/-- The raw completed-multiplier face is exactly the finite coordinate/output sum of native
smooth derivative occurrences. -/
theorem receiverWeightedPhysicalH2VelocityAdvectionFace_eq_sum_coordinateFaces
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteTransportAddress) :
    receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address =
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        completeOpenReceiverWeightedPhysicalH2VelocityCoordinateFace
          solution t coordinate output address := by
  unfold receiverWeightedPhysicalH2VelocityAdvectionFace triadicEnergyFace
    complexDot dotProduct completeOpenReceiverWeightedPhysicalH2VelocityCoordinateFace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [← sum_velocity_mul_openVelocityDirectionalDerivative_eq_advectiveInteraction
    solution t address.1 address.2 output]
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  ring

/-- One completed-multiplier velocity component is bounded by the complete componentwise mass. -/
theorem norm_physicalH2CurlEnergyMultiplier_mul_openVelocity_component_le_fullMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) (component : Fin 3) :
    ‖physicalH2CurlEnergyMultiplier frequency *
        openPeriodicVelocityFourierMode solution t frequency component‖ ≤
      ∑' mode : SpatialFrequency, ∑ output : Fin 3,
        ‖physicalH2CurlEnergyMultiplier mode *
          openPeriodicVelocityFourierMode solution t mode output‖ := by
  have hpopulation : Summable fun mode : SpatialFrequency ↦ ∑ output : Fin 3,
      ‖physicalH2CurlEnergyMultiplier mode *
        openPeriodicVelocityFourierMode solution t mode output‖ := by
    apply summable_sum
    intro output _houtput
    exact summable_norm_physicalH2CurlEnergyMultiplier_mul_openVelocity_component
      solution t output
  have hcomponent :
      ‖physicalH2CurlEnergyMultiplier frequency *
          openPeriodicVelocityFourierMode solution t frequency component‖ ≤
        ∑ output : Fin 3,
          ‖physicalH2CurlEnergyMultiplier frequency *
            openPeriodicVelocityFourierMode solution t frequency output‖ := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun output : Fin 3 ↦
        ‖physicalH2CurlEnergyMultiplier frequency *
          openPeriodicVelocityFourierMode solution t frequency output‖)
      (fun output _houtput ↦ norm_nonneg _) (Finset.mem_univ component)
  have hsingle := hpopulation.sum_le_tsum {frequency}
    (fun mode _hmode ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  exact hcomponent.trans (by simpa using hsingle)

/-- The complete raw receiver-weighted physical velocity-advection population is absolutely
summable before any exchange or real receiver is applied. -/
theorem summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address‖ := by
  let mass : ℝ := ∑' mode : SpatialFrequency, ∑ output : Fin 3,
    ‖physicalH2CurlEnergyMultiplier mode *
      openPeriodicVelocityFourierMode solution t mode output‖
  have hcoordinates : Summable fun address : CompleteTransportAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenReceiverWeightedPhysicalH2VelocityCoordinateFace
          solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    have hvelocity :=
      summable_norm_openPeriodicVelocityFourierMode_component solution t coordinate
    have hderivative :=
      summable_norm_openVelocityDirectionalDerivativeH3State_component
        solution t coordinate output
    have hproduct : Summable fun address : CompleteTransportAddress ↦
        ‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖ :=
      hvelocity.mul_of_nonneg hderivative
        (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    have hmajorant := hproduct.mul_right mass
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hmajorant
    rw [completeOpenReceiverWeightedPhysicalH2VelocityCoordinateFace,
      norm_mul, norm_mul]
    calc
      (‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖) *
          ‖physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
            openPeriodicVelocityFourierMode solution t
              (completeTransportReceiver address) output‖ ≤
        (‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖) * mass := by
          apply mul_le_mul_of_nonneg_left
            (norm_physicalH2CurlEnergyMultiplier_mul_openVelocity_component_le_fullMass
              solution t (completeTransportReceiver address) output)
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      _ = _ := rfl
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hcoordinates
  rw [receiverWeightedPhysicalH2VelocityAdvectionFace_eq_sum_coordinateFaces]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _)

theorem summable_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address :=
  (summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
    solution t).of_norm

/-! ## Genuine cofinal exhaustion by common three-pin cubes -/

theorem physicalH2VelocityTriadAperture_mono :
    Monotone physicalH2VelocityTriadAperture := by
  intro inner outer hinner address haddress
  rw [mem_physicalH2VelocityTriadAperture_iff] at haddress ⊢
  exact ⟨frequencyCube_mono hinner haddress.1,
    frequencyCube_mono hinner haddress.2.1,
    frequencyCube_mono hinner haddress.2.2⟩

theorem exists_mem_physicalH2VelocityTriadAperture
    (address : CompleteTransportAddress) :
    ∃ radius : ℕ, address ∈ physicalH2VelocityTriadAperture radius := by
  obtain ⟨firstRadius, hfirst⟩ := exists_mem_frequencyCube address.1
  obtain ⟨secondRadius, hsecond⟩ := exists_mem_frequencyCube address.2
  obtain ⟨receiverRadius, hreceiver⟩ :=
    exists_mem_frequencyCube (completeTransportReceiver address)
  refine ⟨max (max firstRadius secondRadius) receiverRadius, ?_⟩
  rw [mem_physicalH2VelocityTriadAperture_iff]
  exact ⟨frequencyCube_mono
      ((Nat.le_max_left firstRadius secondRadius).trans (Nat.le_max_left _ _)) hfirst,
    frequencyCube_mono
      ((Nat.le_max_right firstRadius secondRadius).trans (Nat.le_max_left _ _)) hsecond,
    frequencyCube_mono (Nat.le_max_right _ _) hreceiver⟩

/-- Common three-pin cubes are cofinal in every finite population of complete ordered transport
addresses. -/
theorem tendsto_physicalH2VelocityTriadAperture_atTop :
    Tendsto physicalH2VelocityTriadAperture atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro population
  obtain ⟨radius, hradius⟩ :
      ∃ radius : ℕ, population ⊆ physicalH2VelocityTriadAperture radius := by
    classical
    induction population using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert address population haddress ih =>
        obtain ⟨populationRadius, hpopulation⟩ := ih
        obtain ⟨addressRadius, haddressRadius⟩ :=
          exists_mem_physicalH2VelocityTriadAperture address
        refine ⟨max populationRadius addressRadius, ?_⟩
        intro current hcurrent
        rw [Finset.mem_insert] at hcurrent
        rcases hcurrent with rfl | hcurrent
        · exact physicalH2VelocityTriadAperture_mono
            (Nat.le_max_right _ _) haddressRadius
        · exact physicalH2VelocityTriadAperture_mono
            (Nat.le_max_left _ _) (hpopulation hcurrent)
  exact Filter.eventually_atTop.2 ⟨radius, fun later hlater ↦
    hradius.trans (physicalH2VelocityTriadAperture_mono hlater)⟩

/-- Every absolutely summable complete address population is reconstructed by the common
three-pin cubes. -/
theorem tendsto_sum_physicalH2VelocityTriadAperture
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {population : CompleteTransportAddress → E}
    (hsummable : Summable population) :
    Tendsto
      (fun radius : ℕ ↦
        ∑ address ∈ physicalH2VelocityTriadAperture radius, population address)
      atTop (nhds (∑' address, population address)) := by
  exact hsummable.hasSum.comp tendsto_physicalH2VelocityTriadAperture_atTop

/-- The complete complex raw physical velocity-advection current before its real receiver. -/
def completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℂ :=
  ∑' address : CompleteTransportAddress,
    receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address

/-- The finite common-cube raw currents converge to the complete addressed raw population. -/
theorem tendsto_finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Tendsto
      (finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t)
      atTop
      (nhds (completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t)) := by
  exact tendsto_sum_physicalH2VelocityTriadAperture
    (summable_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t)

/-! ## Output-fibre identification with the actual advection coefficient -/

theorem complexDot_finset_sum_left
    {ι : Type*} (population : Finset ι) (source : ι → ComplexVector)
    (receiver : ComplexVector) :
    complexDot (∑ index ∈ population, source index) receiver =
      ∑ index ∈ population, complexDot (source index) receiver := by
  unfold complexDot dotProduct
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sum_pairCompatible_receiverWeightedPhysicalH2VelocityAdvectionFace_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : SpatialFrequency) (radius : ℕ) :
    (∑ parent ∈ pairCompatibleFrequencyAperture output radius,
      receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t)
        (outputParentTransportEquiv (output, parent))) =
      physicalH2CurlEnergyMultiplier (-output) *
        complexDot
          (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) output)
          (openPeriodicVelocityFourierMode solution t (-output)) := by
  have hreceiver (parent : SpatialFrequency) :
      completeTransportReceiver (outputParentTransportEquiv (output, parent)) = -output := by
    funext coordinate
    simp [completeTransportReceiver]
    ring
  unfold finiteAdvectiveCoefficient
  rw [complexDot_finset_sum_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parent _hparent
  unfold receiverWeightedPhysicalH2VelocityAdvectionFace
  simp only [outputParentTransportEquiv_apply_first,
    outputParentTransportEquiv_apply_second, transportedFrequencyAt]
  rw [hreceiver]
  rfl

/-- Every fixed output fibre of the complete raw address population is the completed physical
multiplier paired with the literal actual velocity-advection coefficient and closing mode. -/
theorem tsum_receiverWeightedPhysicalH2VelocityAdvectionFace_outputFiber_eq_actual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : SpatialFrequency) :
    (∑' parent : SpatialFrequency,
      receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t)
        (outputParentTransportEquiv (output, parent))) =
      physicalH2CurlEnergyMultiplier (-output) *
        complexDot (openActualAdvectionMode solution t output)
          (openPeriodicVelocityFourierMode solution t (-output)) := by
  have haddress :=
    summable_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t
  have hreindexed : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t)
        (outputParentTransportEquiv pair) :=
    haddress.comp_injective outputParentTransportEquiv.injective
  have hfiber : Summable fun parent : SpatialFrequency ↦
      receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t)
        (outputParentTransportEquiv (output, parent)) :=
    hreindexed.prod_factor output
  have hsum := hfiber.hasSum.comp
    (tendsto_pairCompatibleFrequencyAperture_atTop output)
  have hadvection :=
    tendsto_finiteOpenAdvectiveCoefficient_pairCompatible solution t output
  have hdot : Tendsto
      (fun radius : ℕ ↦
        complexDot
          (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) output)
          (openPeriodicVelocityFourierMode solution t (-output)))
      atTop
      (nhds (complexDot
        (vectorCoefficientAt
          (h3AdvectiveConvolution (openVelocityH3State solution t)
            (openVelocityH3State solution t)) output)
        (openPeriodicVelocityFourierMode solution t (-output)))) := by
    unfold complexDot dotProduct
    apply tendsto_finsetSum
    intro component _hcomponent
    exact ((tendsto_pi_nhds.1 hadvection component).mul_const
      (openPeriodicVelocityFourierMode solution t (-output) component))
  have hscaled : Tendsto
      (fun radius : ℕ ↦
        physicalH2CurlEnergyMultiplier (-output) *
          complexDot
            (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
              (openPeriodicVelocityFourierMode solution t)
              (openPeriodicVelocityFourierMode solution t) output)
            (openPeriodicVelocityFourierMode solution t (-output)))
      atTop
      (nhds (physicalH2CurlEnergyMultiplier (-output) *
        complexDot
          (vectorCoefficientAt
            (h3AdvectiveConvolution (openVelocityH3State solution t)
              (openVelocityH3State solution t)) output)
          (openPeriodicVelocityFourierMode solution t (-output)))) :=
    tendsto_const_nhds.mul hdot
  have hsumActual : Tendsto
      (fun radius : ℕ ↦
        ∑ parent ∈ pairCompatibleFrequencyAperture output radius,
          receiverWeightedPhysicalH2VelocityAdvectionFace
            (openPeriodicVelocityFourierMode solution t)
            (outputParentTransportEquiv (output, parent)))
      atTop
      (nhds (physicalH2CurlEnergyMultiplier (-output) *
        complexDot (openActualAdvectionMode solution t output)
          (openPeriodicVelocityFourierMode solution t (-output)))) := by
    rw [openActualAdvectionMode_eq_h3AdvectiveConvolution]
    apply Tendsto.congr' _ hscaled
    exact Filter.Eventually.of_forall fun radius ↦
      (sum_pairCompatible_receiverWeightedPhysicalH2VelocityAdvectionFace_eq
        solution t output radius).symm
  exact tendsto_nhds_unique hsum hsumActual

/-- Fubini over the absolutely summable complete address population retains the output and parent
occurrences and identifies every grouped fibre with the actual advection coefficient. -/
theorem completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_output_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t =
      ∑' output : SpatialFrequency,
        physicalH2CurlEnergyMultiplier (-output) *
          complexDot (openActualAdvectionMode solution t output)
            (openPeriodicVelocityFourierMode solution t (-output)) := by
  let face : CompleteTransportAddress → ℂ := fun address ↦
    receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address
  have hface : Summable face :=
    summable_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t
  have hreindexed : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      face (outputParentTransportEquiv pair) :=
    hface.comp_injective outputParentTransportEquiv.injective
  have hfiber (output : SpatialFrequency) : Summable fun parent : SpatialFrequency ↦
      face (outputParentTransportEquiv (output, parent)) :=
    hreindexed.prod_factor output
  have hprod := hreindexed.tsum_prod' hfiber
  unfold completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
  change (∑' address : CompleteTransportAddress, face address) = _
  calc
    (∑' address : CompleteTransportAddress, face address) =
        ∑' pair : SpatialFrequency × SpatialFrequency,
          face (outputParentTransportEquiv pair) :=
      (outputParentTransportEquiv.tsum_eq face).symm
    _ = ∑' output : SpatialFrequency, ∑' parent : SpatialFrequency,
        face (outputParentTransportEquiv (output, parent)) := hprod
    _ = _ := by
      apply tsum_congr
      intro output
      exact tsum_receiverWeightedPhysicalH2VelocityAdvectionFace_outputFiber_eq_actual
        solution t output

theorem summable_physicalH2VelocityActualOutputPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun output : SpatialFrequency ↦
      physicalH2CurlEnergyMultiplier (-output) *
        complexDot (openActualAdvectionMode solution t output)
          (openPeriodicVelocityFourierMode solution t (-output)) := by
  let face : CompleteTransportAddress → ℂ := fun address ↦
    receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address
  have hface : Summable face :=
    summable_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t
  have hreindexed : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      face (outputParentTransportEquiv pair) :=
    hface.comp_injective outputParentTransportEquiv.injective
  have houter : Summable fun output : SpatialFrequency ↦
      ∑' parent : SpatialFrequency, face (outputParentTransportEquiv (output, parent)) :=
    hreindexed.prod
  exact houter.congr fun output ↦
    tsum_receiverWeightedPhysicalH2VelocityAdvectionFace_outputFiber_eq_actual
      solution t output

/-! ## Complex-to-real receiver orientation -/

theorem physicalH2CurlEnergyMultiplier_neg (frequency : SpatialFrequency) :
    physicalH2CurlEnergyMultiplier (-frequency) =
      physicalH2CurlEnergyMultiplier frequency := by
  unfold physicalH2CurlEnergyMultiplier
  rw [torusStokesEigenvalue_neg]

theorem re_complexDot_actualAdvection_closingVelocity_eq_sourceReading
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    (complexDot (openActualAdvectionMode solution t frequency)
      (openPeriodicVelocityFourierMode solution t (-frequency))).re =
      sourceTestProductionReading
        (openPeriodicVelocityFourierMode solution t frequency)
        (openActualAdvectionMode solution t frequency) := by
  rw [openPeriodicVelocityFourierMode_neg_eq_conj]
  unfold complexDot dotProduct sourceTestProductionReading
  congr 1
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only
  ring

theorem neg_re_physicalH2VelocityActualOutputFace_eq_modeWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    -(physicalH2CurlEnergyMultiplier (-frequency) *
        complexDot (openActualAdvectionMode solution t frequency)
          (openPeriodicVelocityFourierMode solution t (-frequency))).re =
      homogeneousCoordinateH2ModeWork frequency
        (openPeriodicVelocityFourierMode solution t frequency)
        (openActualAdvectionMode solution t frequency) := by
  rw [physicalH2CurlEnergyMultiplier_neg]
  rw [homogeneousCoordinateH2ModeWork_eq_completedPhysicalMultiplier]
  rw [Complex.mul_re]
  have him : (physicalH2CurlEnergyMultiplier frequency).im = 0 := by
    simp [physicalH2CurlEnergyMultiplier]
  rw [him, zero_mul, sub_zero]
  rw [re_complexDot_actualAdvection_closingVelocity_eq_sourceReading]
  ring

/-- The declared physical-current receiver is negative real raw transport.  The sign comes from
the PDE convention in `homogeneousCoordinateH2ModeWork`, while Fourier reality supplies the
Hermitian test orientation. -/
theorem neg_re_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_velocityCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    -(completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t).re =
      completePhysicalH2VelocityCurrent solution t := by
  rw [completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_output_tsum]
  have houter := summable_physicalH2VelocityActualOutputPopulation solution t
  rw [Complex.re_tsum houter]
  rw [← tsum_neg]
  unfold completePhysicalH2VelocityCurrent
  apply tsum_congr
  intro frequency
  exact neg_re_physicalH2VelocityActualOutputFace_eq_modeWork solution t frequency

/-! ## Public cofinal source/current returns -/

/-- The negative-real raw current along common three-pin cubes converges to the actual complete
physical `H2` velocity-advection current. -/
theorem tendsto_neg_re_finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Tendsto
      (fun radius : ℕ ↦
        -(finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
          solution t radius).re)
      atTop (nhds (completePhysicalH2VelocityCurrent solution t)) := by
  have hraw :=
    tendsto_finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hraw
  have hneg := hre.neg
  rw [neg_re_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_velocityCurrent]
    at hneg
  exact hneg

/-- **[proved-derived; formal-checked] Cofinal completed-swing identity.**  One half of the real
finite completed physical velocity exchange current on the common three-pin cube converges to
the literal complete physical `H2` velocity-advection current.  Cancellation remains signed and
occurs before a norm. -/
theorem tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Tendsto
      (fun radius : ℕ ↦ (1 / 2 : ℝ) *
        (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re)
      atTop (nhds (completePhysicalH2VelocityCurrent solution t)) := by
  apply Tendsto.congr'
    (Filter.Eventually.of_forall fun radius ↦ ?_)
    (tendsto_neg_re_finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t)
  rw [finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged]
  have hreal : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by norm_num
  have himag : (-(1 / 2 : ℂ)).im = 0 := by norm_num
  rw [Complex.mul_re, hreal, himag]
  ring

/-- The same common-cube completed-swing exhaustion converges to the existing complete physical
vorticity-current chart. -/
theorem tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_to_physicalH2Current
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Tendsto
      (fun radius : ℕ ↦ (1 / 2 : ℝ) *
        (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re)
      atTop
      (nhds
        (Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin.completePhysicalH2Current
          solution t)) := by
  rw [completePhysicalH2Current_eq_velocityCurrent]
  exact tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t

section Audit

#print axioms openPhysicalH2MultiplierVelocityH3State_apply
#print axioms summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
#print axioms tendsto_physicalH2VelocityTriadAperture_atTop
#print axioms tsum_receiverWeightedPhysicalH2VelocityAdvectionFace_outputFiber_eq_actual
#print axioms neg_re_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_velocityCurrent
#print axioms tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent
#print axioms tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_to_physicalH2Current

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
