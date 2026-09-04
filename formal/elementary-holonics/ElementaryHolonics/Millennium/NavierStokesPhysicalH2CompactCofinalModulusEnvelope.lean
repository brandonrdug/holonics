import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CofinalModulusH3Occupation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization

/-!
# Compact cofinal modulus envelope interface

This module makes the remaining time-integrability interface for the complete physical-`H2`
exchanged-modulus population exact.  The receiver hypothesis is a concrete function

`M : CompleteTransportAddress → ℝ`

whose address population is summable and which bounds every compactly retracted exchanged-face
modulus uniformly in real time.  Under precisely that hypothesis, each addressed compact face is
continuous, the Weierstrass/Tannery `continuous_tsum` passage makes the complete modulus
population continuous, and compact interval integrability follows.

**[proved-derived; formal-checked]**  Supplying this derived integrability to the existing
conditional cofinal-modulus theorem returns its weighted-`H3` occupation conclusion.  No theorem
here asserts that such an envelope exists.  No source payment, cofinal running service,
summability construction, terminal estimate, continuation, or closure claim is made.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CompactCofinalModulusEnvelope

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalModulusH3Occupation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Continuous addressed compact faces -/

/-- The globally compacted velocity mode is exactly the admitted genuine-torus coefficient at
the compact interior time. -/
theorem compactPhysicalH2VelocityMode_eq_openPeriodicVelocityFourierMode
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (time : ℝ) :
    compactPhysicalH2VelocityMode solution ha hab hbT frequency time =
      openPeriodicVelocityFourierMode solution
        (compactInteriorTime ha hab hbT time) frequency := by
  ext component
  exact velocityModeComponent_eq_openPeriodicVelocityFourierMode
    solution (compactInteriorTime ha hab hbT time) frequency component

/-- One actual completed exchanged face, with all three mode occurrences compactly retracted, is
continuous on the full real clock. -/
theorem continuous_compactPhysicalH2VelocityExchangedTriadFace
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (address : CompleteTransportAddress) :
    Continuous (fun time ↦
      physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ compactPhysicalH2VelocityMode
          solution ha hab hbT frequency time) address) := by
  have hmode (frequency : SpatialFrequency) : Continuous
      (compactPhysicalH2VelocityMode solution ha hab hbT frequency) :=
    continuous_compactPhysicalH2VelocityMode
      solution ha hab hbT frequency
  have htriadic : Continuous (fun time ↦
      triadicEnergyFace address.1 address.2
        (compactPhysicalH2VelocityMode solution ha hab hbT address.1 time)
        (compactPhysicalH2VelocityMode solution ha hab hbT address.2 time)
        (compactPhysicalH2VelocityMode solution ha hab hbT
          (completeTransportReceiver address) time)) := by
    exact continuousOn_univ.mp
      (continuousOn_triadicEnergyFace address.1 address.2
      (hmode address.1).continuousOn (hmode address.2).continuousOn
      (hmode (completeTransportReceiver address)).continuousOn)
  have hfactorized : Continuous (fun time ↦
      physicalH2ExchangedTriadMultiplier address *
        triadicEnergyFace address.1 address.2
          (compactPhysicalH2VelocityMode solution ha hab hbT address.1 time)
          (compactPhysicalH2VelocityMode solution ha hab hbT address.2 time)
          (compactPhysicalH2VelocityMode solution ha hab hbT
            (completeTransportReceiver address) time)) :=
    continuous_const.mul htriadic
  apply hfactorized.congr
  intro time
  unfold physicalH2VelocityExchangedTriadFace
  rw [physicalH2ExchangedTriadTransfer_eq_factorized]
  · rfl
  · have hdivergence := openPeriodicVelocityFourierMode_divergenceFree
      solution (compactInteriorTime ha hab hbT time) address.1
    simpa only [compactPhysicalH2VelocityMode_eq_openPeriodicVelocityFourierMode
      solution ha hab hbT, completeTransportTriad] using hdivergence

/-! ## The exact summable-envelope interface -/

/-- A summable address envelope, uniform over the compactly retracted real clock, makes the
literal complete exchanged-modulus population globally continuous. -/
theorem continuous_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (M : CompleteTransportAddress → ℝ) (hM : Summable M)
    (henvelope : ∀ address time,
      ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution
          (compactInteriorTime ha hab hbT time)) address‖ ≤ M address) :
    Continuous
      (compactPhysicalH2CofinalExchangedModulusPopulation
        solution ha hab hbT) := by
  let compactFace : CompleteTransportAddress → ℝ → ℂ := fun address time ↦
    physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ compactPhysicalH2VelocityMode
        solution ha hab hbT frequency time) address
  have hcompactFace (address : CompleteTransportAddress) :
      Continuous (compactFace address) :=
    continuous_compactPhysicalH2VelocityExchangedTriadFace
      solution ha hab hbT address
  have hterms : ∀ address : CompleteTransportAddress,
      Continuous (fun time ↦ ‖compactFace address time‖) :=
    fun address ↦ (hcompactFace address).norm
  have hbound : ∀ address time,
      ‖(‖compactFace address time‖ : ℝ)‖ ≤ M address := by
    intro address time
    have hnamed := henvelope address time
    have hmodes :
        (fun frequency ↦ compactPhysicalH2VelocityMode
          solution ha hab hbT frequency time) =
          openPeriodicVelocityFourierMode solution
            (compactInteriorTime ha hab hbT time) := by
      funext frequency
      exact compactPhysicalH2VelocityMode_eq_openPeriodicVelocityFourierMode
        solution ha hab hbT frequency time
    simpa only [compactFace, hmodes, Real.norm_eq_abs, abs_norm] using hnamed
  have hsum : Continuous (fun time ↦
      ∑' address : CompleteTransportAddress, ‖compactFace address time‖) :=
    continuous_tsum hterms hM hbound
  unfold compactPhysicalH2CofinalExchangedModulusPopulation
    physicalH2CofinalExchangedModulusPopulation
  apply hsum.congr
  intro time
  apply tsum_congr
  intro address
  have hmodes :
      (fun frequency ↦ compactPhysicalH2VelocityMode
        solution ha hab hbT frequency time) =
        openPeriodicVelocityFourierMode solution
          (compactInteriorTime ha hab hbT time) := by
    funext frequency
    exact compactPhysicalH2VelocityMode_eq_openPeriodicVelocityFourierMode
      solution ha hab hbT frequency time
  rw [show compactFace address time =
      physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution
          (compactInteriorTime ha hab hbT time)) address by
    exact congrArg (fun modes ↦
      physicalH2VelocityExchangedTriadFace modes address) hmodes]

/-- The same explicit summable envelope discharges the compact interval-integrability boundary. -/
theorem intervalIntegrable_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (M : CompleteTransportAddress → ℝ) (hM : Summable M)
    (henvelope : ∀ address time,
      ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution
          (compactInteriorTime ha hab hbT time)) address‖ ≤ M address) :
    IntervalIntegrable
      (compactPhysicalH2CofinalExchangedModulusPopulation solution ha hab hbT)
      volume a b := by
  exact (continuous_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
    solution ha hab hbT M hM henvelope).intervalIntegrable a b

/-! ## Existing weighted-H3 occupation theorem under the exact envelope hypothesis -/

/-- The prior conditional weighted-`H3` occupation theorem with its compact integrability premise
discharged by the explicit summable address envelope above.  The envelope remains a hypothesis. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_compactCofinalEnvelope
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (M : CompleteTransportAddress → ℝ) (hM : Summable M)
    (henvelope : ∀ address time,
      ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution
          (compactInteriorTime ha hab hbT time)) address‖ ≤ M address) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((b - a) * periodicKineticEnergy velocity 0 +
        (3 / 2 : ℝ) * nu⁻¹ *
          (coordinateH2Energy velocity a +
            (1 / 2 : ℝ) *
              ∫ time in a..b,
                compactPhysicalH2CofinalExchangedModulusPopulation
                  solution ha hab hbT time)) := by
  exact
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_compactCofinalModulus
      solution hnu ha hab hbT
      (intervalIntegrable_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
        solution ha hab hbT M hM henvelope)

section Audit

#print axioms compactPhysicalH2VelocityMode_eq_openPeriodicVelocityFourierMode
#print axioms continuous_compactPhysicalH2VelocityExchangedTriadFace
#print axioms continuous_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
#print axioms intervalIntegrable_compactPhysicalH2CofinalExchangedModulusPopulation_of_envelope
#print axioms integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_compactCofinalEnvelope

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CompactCofinalModulusEnvelope
