import ElementaryHolonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2JointWeightedSummability

/-!
# The complete physical H2 current as stretching plus exchanged transport

**[proved-derived; formal-checked]**  The derivative-weighted vorticity current is first kept as
a real Hermitian receiver.  Its complete interaction population splits into the symmetric
stretching face and the receiver-weighted transport face.  Absolute summability of both
unbounded `(1 + lambda)` populations permits the output/parent Fubini passage.  Exchanging the
transported and receiving pins then turns the negative transport work into one half of the real
part of the exact `H2` clocked pantographic swing.

The complex exchanged population is retained without an assertion that its total is real.  Only
its declared real production receiver enters the physical current.  No terminal estimate,
critical absorption, or continuation theorem is asserted here.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2JointWeightedSummability
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedReality

/-! ## Real receiver faces -/

/-- Symmetric Hermitian phase is exactly the complex chart of the real production reading. -/
theorem complexVectorSymmetricPhasePairing_eq_sourceTestProductionReading
    (left right : ComplexVector) :
    complexVectorSymmetricPhasePairing left right =
      (sourceTestProductionReading left right : ℂ) := by
  unfold complexVectorSymmetricPhasePairing
  change (1 / 2 : ℂ) *
      (complexVectorHermitianPairing left right +
        complexVectorHermitianPairing right left) =
    ((complexVectorHermitianPairing left right).re : ℂ)
  rw [complexVectorHermitianPairing_swap left right]
  rw [Complex.re_eq_add_conj]
  ring

/-- The complete derivative-weighted vorticity source current on one actual interior slice. -/
def completePhysicalH2Current
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' output : SpatialFrequency,
    sourceTestProductionReading
      (((1 + torusStokesEigenvalue output : ℝ) : ℂ) •
        openPeriodicVorticityFourierMode solution t output)
      (vorticityNonlinearMode solution t output)

/-- The complete real stretching current with the physical inhomogeneous `H2` output weight. -/
def completePhysicalH2WeightedStretchingCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' address : CompleteStretchingAddress,
    (1 + torusStokesEigenvalue address.1) *
      (completeOpenVorticityStretchingFace solution t address).re

/-- One exact exchanged transport swing on the actual closed Fourier triad. -/
def completePhysicalH2ExchangedTransportFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) : ℂ :=
  h2ExchangedTriadTransfer (completeTransportTriad address)
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVorticityFourierMode solution t address.2)
    (openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address))

/-- The exchanged transport population is observed only through its real physical receiver. -/
def completePhysicalH2ExchangedTransportCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' address : CompleteTransportAddress,
    (completePhysicalH2ExchangedTransportFace solution t address).re

/-! ## Summability and the fixed-output physical split -/

theorem summable_completePhysicalH2WeightedStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun address : CompleteStretchingAddress ↦
      (1 + torusStokesEigenvalue address.1) *
        (completeOpenVorticityStretchingFace solution t address).re := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityStretchingFace
      solution t)
  rw [Real.norm_eq_abs, abs_mul]
  have hweight : 0 ≤ 1 + torusStokesEigenvalue address.1 := by
    linarith [torusStokesEigenvalue_nonneg address.1]
  rw [abs_of_nonneg hweight]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hweight

private def completePhysicalH2ReceiverTransportPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) : ℝ :=
  (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
    (completeOpenVorticityTransportFace solution t address).re

private theorem summable_completePhysicalH2ReceiverTransportPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable (completePhysicalH2ReceiverTransportPopulation solution t) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityTransportFace
      solution t)
  unfold completePhysicalH2ReceiverTransportPopulation
  rw [Real.norm_eq_abs, abs_mul]
  have hweight :
      0 ≤ 1 + torusStokesEigenvalue (completeTransportReceiver address) := by
    linarith [torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  rw [abs_of_nonneg hweight]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hweight

private def completePhysicalH2TransportedPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) : ℝ :=
  (1 + torusStokesEigenvalue address.2) *
    (completeOpenVorticityTransportFace solution t address).re

private theorem summable_completePhysicalH2TransportedPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable (completePhysicalH2TransportedPopulation solution t) := by
  have hreceiver :=
    (summable_completePhysicalH2ReceiverTransportPopulation solution t).comp_injective
      completeTransportExchange.injective
  exact hreceiver.neg.congr (fun address ↦ by
    change -completePhysicalH2ReceiverTransportPopulation solution t
        (completeTransportExchange address) =
      completePhysicalH2TransportedPopulation solution t address
    unfold completePhysicalH2ReceiverTransportPopulation
      completePhysicalH2TransportedPopulation
    rw [completeTransportReceiver_exchange,
      completeOpenVorticityTransportFace_exchange]
    simp)

theorem completePhysicalH2ExchangedTransportFace_eq_populations
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) :
    (completePhysicalH2ExchangedTransportFace solution t address).re =
      completePhysicalH2TransportedPopulation solution t address -
        completePhysicalH2ReceiverTransportPopulation solution t address := by
  have hdivergence := openPeriodicVelocityFourierMode_divergenceFree
    solution t address.1
  let face := completeOpenVorticityTransportFace solution t address
  have hface : completePhysicalH2ExchangedTransportFace solution t address =
      ((((torusStokesEigenvalue address.2 -
        torusStokesEigenvalue (completeTransportReceiver address) : ℝ) : ℂ)) *
          face) := by
    unfold completePhysicalH2ExchangedTransportFace
    rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul
      (completeTransportTriad address)
      (openPeriodicVelocityFourierMode solution t address.1)
      (openPeriodicVorticityFourierMode solution t address.2)
      (openPeriodicVorticityFourierMode solution t
        (completeTransportReceiver address)) hdivergence]
    rfl
  rw [hface]
  unfold completePhysicalH2TransportedPopulation
    completePhysicalH2ReceiverTransportPopulation
  change
    (((((torusStokesEigenvalue address.2 -
      torusStokesEigenvalue (completeTransportReceiver address) : ℝ) : ℂ)) *
        face).re) =
      (1 + torusStokesEigenvalue address.2) * face.re -
        (1 + torusStokesEigenvalue (completeTransportReceiver address)) * face.re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem summable_completePhysicalH2ExchangedTransportPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      (completePhysicalH2ExchangedTransportFace solution t address).re := by
  exact ((summable_completePhysicalH2TransportedPopulation solution t).sub
    (summable_completePhysicalH2ReceiverTransportPopulation solution t)).congr
      (fun address ↦
        (completePhysicalH2ExchangedTransportFace_eq_populations
          solution t address).symm)

private theorem sourceTestProductionReading_eq_completeStretching_sub_transportAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    sourceTestProductionReading
        (openPeriodicVorticityFourierMode solution t output)
        (vorticityNonlinearMode solution t output) =
      (completeReceiverStretchingPhaseAtOutput solution t output).re -
        (completeReceiverTransportFirstPhaseAtOutput solution t output).re := by
  have hactual :=
    (continuous_complexVectorSymmetricPhasePairing_right
      (openPeriodicVorticityFourierMode solution t output)).continuousAt.tendsto.comp
        (tendsto_finiteOpenVorticityNonlinearCoefficient_pairCompatible
          solution t output)
  have hstretch := tendsto_pairCompatibleReceiverStretchingPhase solution t output
  have htransport := tendsto_pairCompatibleReceiverTransportPhase solution t output
  have hsplit : Tendsto
      (fun radius : ℕ ↦
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t output)
          (finiteOpenVorticityNonlinearCoefficient solution t
            (pairCompatibleFrequencyAperture output radius) output))
      atTop
      (nhds (completeReceiverStretchingPhaseAtOutput solution t output -
        (1 / 2 : ℂ) *
          (completeReceiverTransportFirstPhaseAtOutput solution t output +
            conj (completeReceiverTransportFirstPhaseAtOutput solution t output)))) := by
    apply Tendsto.congr' _ (hstretch.sub htransport)
    exact Filter.Eventually.of_forall fun radius ↦ by
      change
        complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t output)
            (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
              (openPeriodicVorticityFourierMode solution t)
              (openPeriodicVelocityFourierMode solution t) output) -
          complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t output)
            (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
              (openPeriodicVelocityFourierMode solution t)
              (openPeriodicVorticityFourierMode solution t) output) =
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t output)
          (finiteOpenVorticityNonlinearCoefficient solution t
            (pairCompatibleFrequencyAperture output radius) output)
      symm
      rw [finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
        solution t (pairCompatibleFrequencyAperture output radius) output
          (pairCompatibleFrequencyAperture_isTransportPaired output radius),
        complexVectorSymmetricPhasePairing_sub_right]
  have heq := tendsto_nhds_unique hactual hsplit
  have hre := congrArg Complex.re heq
  rw [complexVectorSymmetricPhasePairing_eq_sourceTestProductionReading] at hre
  calc
    sourceTestProductionReading
        (openPeriodicVorticityFourierMode solution t output)
        (vorticityNonlinearMode solution t output) =
      (completeReceiverStretchingPhaseAtOutput solution t output).re -
        (1 / 2 : ℝ) *
          ((completeReceiverTransportFirstPhaseAtOutput solution t output).re +
            (completeReceiverTransportFirstPhaseAtOutput solution t output).re) := by
              simpa using hre
    _ = (completeReceiverStretchingPhaseAtOutput solution t output).re -
        (completeReceiverTransportFirstPhaseAtOutput solution t output).re := by ring

/-! ## Global Fubini and exchange -/

private theorem completeReceiverStretchingPhaseAtOutput_re_eq_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    (completeReceiverStretchingPhaseAtOutput solution t output).re =
      ∑' parent : SpatialFrequency,
        (completeOpenVorticityStretchingFace solution t (output, parent)).re := by
  unfold completeReceiverStretchingPhaseAtOutput
  rw [Complex.re_tsum (Summable.of_norm
    (summable_norm_completeReceiverStretchingPhaseAtOutput solution t output))]

private theorem completeReceiverTransportFirstPhaseAtOutput_re_eq_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    (completeReceiverTransportFirstPhaseAtOutput solution t output).re =
      ∑' parent : SpatialFrequency,
        (completeOpenVorticityTransportFace solution t
          (parent, output - parent)).re := by
  unfold completeReceiverTransportFirstPhaseAtOutput
  rw [Complex.re_tsum (Summable.of_norm
    (summable_norm_completeReceiverTransportFirstPhaseAtOutput solution t output))]

set_option maxHeartbeats 1200000 in
private theorem completePhysicalH2Current_eq_weightedStretching_sub_receiverTransport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2Current solution t =
      completePhysicalH2WeightedStretchingCurrent solution t -
        ∑' address : CompleteTransportAddress,
          completePhysicalH2ReceiverTransportPopulation solution t address := by
  have hstretch := summable_completePhysicalH2WeightedStretchingPopulation solution t
  have htransport := summable_completePhysicalH2ReceiverTransportPopulation solution t
  have hstretchFiber (output : SpatialFrequency) : Summable fun parent ↦
      (1 + torusStokesEigenvalue output) *
        (completeOpenVorticityStretchingFace solution t (output, parent)).re := by
    exact hstretch.prod_factor output
  have htransportOutputParent : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      (1 + torusStokesEigenvalue pair.1) *
        (completeOpenVorticityTransportFace solution t
          (pair.2, pair.1 - pair.2)).re := by
    have hpull := htransport.comp_injective outputParentTransportEquiv.injective
    exact hpull.congr (fun pair ↦ by
      change completePhysicalH2ReceiverTransportPopulation solution t
          (outputParentTransportEquiv pair) =
        (1 + torusStokesEigenvalue pair.1) *
          (completeOpenVorticityTransportFace solution t
            (pair.2, pair.1 - pair.2)).re
      unfold completePhysicalH2ReceiverTransportPopulation
      change
        (1 + torusStokesEigenvalue
            (completeTransportReceiver (pair.2, pair.1 - pair.2))) *
            (completeOpenVorticityTransportFace solution t
              (pair.2, pair.1 - pair.2)).re =
          (1 + torusStokesEigenvalue pair.1) *
            (completeOpenVorticityTransportFace solution t
              (pair.2, pair.1 - pair.2)).re
      have hreceiver : completeTransportReceiver (pair.2, pair.1 - pair.2) = -pair.1 := by
        funext coordinate
        simp [completeTransportReceiver]
        ring
      rw [hreceiver, torusStokesEigenvalue_neg])
  have htransportFiber (output : SpatialFrequency) : Summable fun parent ↦
      (1 + torusStokesEigenvalue output) *
        (completeOpenVorticityTransportFace solution t
          (parent, output - parent)).re := by
    exact htransportOutputParent.prod_factor output
  have hstretchProd := hstretch.tsum_prod' hstretchFiber
  have htransportProd := htransportOutputParent.tsum_prod' htransportFiber
  have hstretchOuter : Summable fun output : SpatialFrequency ↦
      ∑' parent : SpatialFrequency,
        (1 + torusStokesEigenvalue output) *
          (completeOpenVorticityStretchingFace solution t (output, parent)).re :=
    hstretch.prod
  have htransportOuter : Summable fun output : SpatialFrequency ↦
      ∑' parent : SpatialFrequency,
        (1 + torusStokesEigenvalue output) *
          (completeOpenVorticityTransportFace solution t
            (parent, output - parent)).re :=
    htransportOutputParent.prod
  have htransportReindex :
      (∑' address : CompleteTransportAddress,
        completePhysicalH2ReceiverTransportPopulation solution t address) =
      ∑' pair : SpatialFrequency × SpatialFrequency,
        (1 + torusStokesEigenvalue pair.1) *
          (completeOpenVorticityTransportFace solution t
            (pair.2, pair.1 - pair.2)).re := by
    calc
      (∑' address : CompleteTransportAddress,
          completePhysicalH2ReceiverTransportPopulation solution t address) =
          ∑' pair : SpatialFrequency × SpatialFrequency,
            completePhysicalH2ReceiverTransportPopulation solution t
              (outputParentTransportEquiv pair) :=
        (outputParentTransportEquiv.tsum_eq
          (completePhysicalH2ReceiverTransportPopulation solution t)).symm
      _ = ∑' pair : SpatialFrequency × SpatialFrequency,
          (1 + torusStokesEigenvalue pair.1) *
            (completeOpenVorticityTransportFace solution t
              (pair.2, pair.1 - pair.2)).re := by
        apply tsum_congr
        intro pair
        change
          (1 + torusStokesEigenvalue
              (completeTransportReceiver (pair.2, pair.1 - pair.2))) *
              (completeOpenVorticityTransportFace solution t
                (pair.2, pair.1 - pair.2)).re =
            (1 + torusStokesEigenvalue pair.1) *
              (completeOpenVorticityTransportFace solution t
                (pair.2, pair.1 - pair.2)).re
        have hreceiver :
            completeTransportReceiver (pair.2, pair.1 - pair.2) = -pair.1 := by
          funext coordinate
          simp [completeTransportReceiver]
          ring
        rw [hreceiver, torusStokesEigenvalue_neg]
  unfold completePhysicalH2Current completePhysicalH2WeightedStretchingCurrent
  rw [htransportReindex, hstretchProd, htransportProd]
  rw [← hstretchOuter.tsum_sub htransportOuter]
  apply tsum_congr
  intro output
  rw [sourceTestProductionReading_real_smul_test,
    sourceTestProductionReading_eq_completeStretching_sub_transportAtOutput
      solution t output,
    completeReceiverStretchingPhaseAtOutput_re_eq_tsum,
    completeReceiverTransportFirstPhaseAtOutput_re_eq_tsum]
  rw [tsum_mul_left, tsum_mul_left]
  ring

private theorem tsum_receiverTransport_eq_neg_tsum_transported
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    (∑' address : CompleteTransportAddress,
      completePhysicalH2ReceiverTransportPopulation solution t address) =
      -(∑' address : CompleteTransportAddress,
        completePhysicalH2TransportedPopulation solution t address) := by
  have hreindex := completeTransportExchange.tsum_eq
    (completePhysicalH2ReceiverTransportPopulation solution t)
  rw [← hreindex]
  rw [← tsum_neg]
  apply tsum_congr
  intro address
  unfold completePhysicalH2ReceiverTransportPopulation
    completePhysicalH2TransportedPopulation
  rw [completeTransportReceiver_exchange,
    completeOpenVorticityTransportFace_exchange]
  simp

/-- **[proved-derived; formal-checked] Complete physical H2 interaction identity.**  The real
derivative-weighted vorticity current is the complete weighted stretching population plus one
half of the real exchanged transport swing.  No reality claim is made about the complex exchange
total itself. -/
theorem completePhysicalH2Current_eq_weightedStretching_add_half_exchangedTransport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2Current solution t =
      completePhysicalH2WeightedStretchingCurrent solution t +
        (1 / 2 : ℝ) * completePhysicalH2ExchangedTransportCurrent solution t := by
  rw [completePhysicalH2Current_eq_weightedStretching_sub_receiverTransport]
  have hexchange : completePhysicalH2ExchangedTransportCurrent solution t =
      (∑' address : CompleteTransportAddress,
        completePhysicalH2TransportedPopulation solution t address) -
      ∑' address : CompleteTransportAddress,
        completePhysicalH2ReceiverTransportPopulation solution t address := by
    unfold completePhysicalH2ExchangedTransportCurrent
    rw [← (summable_completePhysicalH2TransportedPopulation solution t).tsum_sub
      (summable_completePhysicalH2ReceiverTransportPopulation solution t)]
    apply tsum_congr
    intro address
    exact completePhysicalH2ExchangedTransportFace_eq_populations
      solution t address
  rw [hexchange, tsum_receiverTransport_eq_neg_tsum_transported solution t]
  ring

/-! ## Compact source and coordinate-current returns -/

theorem compactCofinalH2CurlCompleteAt_eq_completePhysicalH2Current
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalH2CurlCompleteAt solution ha hab hbT sourceTime =
      completePhysicalH2Current solution
        (compactInteriorTime ha hab hbT sourceTime) := by
  unfold compactCofinalH2CurlCompleteAt completePhysicalH2Current
  apply tsum_congr
  intro frequency
  rfl

theorem compactCofinalH2CurlCompleteAt_eq_weightedStretching_add_half_exchangedTransport
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalH2CurlCompleteAt solution ha hab hbT sourceTime =
      completePhysicalH2WeightedStretchingCurrent solution
          (compactInteriorTime ha hab hbT sourceTime) +
        (1 / 2 : ℝ) * completePhysicalH2ExchangedTransportCurrent solution
          (compactInteriorTime ha hab hbT sourceTime) := by
  rw [compactCofinalH2CurlCompleteAt_eq_completePhysicalH2Current]
  exact completePhysicalH2Current_eq_weightedStretching_add_half_exchangedTransport
    solution (compactInteriorTime ha hab hbT sourceTime)

/-- The same complete population is the literal coordinate `H2` nonlinear production current. -/
theorem coordinateH2NonlinearProductionCurrent_eq_weightedStretching_add_half_exchangedTransport
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    coordinateH2NonlinearProductionCurrent velocity
        (compactInteriorTime ha hab hbT sourceTime).1 =
      completePhysicalH2WeightedStretchingCurrent solution
          (compactInteriorTime ha hab hbT sourceTime) +
        (1 / 2 : ℝ) * completePhysicalH2ExchangedTransportCurrent solution
          (compactInteriorTime ha hab hbT sourceTime) := by
  rw [← compactCofinalH2CurlCompleteAt_eq_coordinateH2NonlinearProductionCurrent
    solution ha hab hbT sourceTime]
  exact compactCofinalH2CurlCompleteAt_eq_weightedStretching_add_half_exchangedTransport
    solution ha hab hbT sourceTime

section Audit

#print axioms completePhysicalH2Current_eq_weightedStretching_add_half_exchangedTransport
#print axioms compactCofinalH2CurlCompleteAt_eq_weightedStretching_add_half_exchangedTransport
#print axioms coordinateH2NonlinearProductionCurrent_eq_weightedStretching_add_half_exchangedTransport

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
