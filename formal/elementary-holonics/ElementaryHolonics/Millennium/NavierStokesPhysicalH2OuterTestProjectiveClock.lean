import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticSignedPayment

/-!
# The projective clock of the time-varying physical-H2 outer test

**[proved-derived; formal-checked]** Fixing the inserted Hodge carrier leaves exactly two moving
velocity legs in every outer insertion covector.  Differentiation returns their two product-rule
jets.  Substitution of the actual pressure-free Fourier-mode equations separates those jets into
one nonlinear two-leg remainder and a signed Stokes return:

`outerTest' = nonlinearRemainder - outerTestClock * outerTest`.

The two-leg clock and the omitted inserted-carrier clock add exactly to the standing three-pin
clock.  The full reciprocal clock therefore partitions unity between them.  The outer Stokes term
is a genuine positive scalar damping in this fixed-carrier ODE, but it is only the outer-clock
share; a moving projective/Hodge carrier owes the complementary inserted-clock connection and its
own nonlinear jet.  The nonlinear outer remainder is retained explicitly.

The normalized principal outer covector has exact frequency degree three.  Feeding it the inner
quadratic source restores the already-proved degree-four quartic current.  Thus this differentiation
does not lower the comparable-sector obstruction and supplies no terminal estimate by itself.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2OuterTestProjectiveClock

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The two untouched time jets -/

/-- Product-rule current obtained by inserting a declared velocity jet into each of the two
outer legs not occupied by the fixed carrier. -/
def physicalH2OuterTestVelocityJetFace
    (velocityMode velocityJet : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector) : ℂ :=
  match leg with
  | .advecting =>
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2 inserted
            (velocityJet address.2)
            (velocityMode (completeTransportReceiver address)) +
          triadicEnergyFace address.1 address.2 inserted
            (velocityMode address.2)
            (velocityJet (completeTransportReceiver address)))
  | .transported =>
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2
            (velocityJet address.1) inserted
            (velocityMode (completeTransportReceiver address)) +
          triadicEnergyFace address.1 address.2
            (velocityMode address.1) inserted
            (velocityJet (completeTransportReceiver address)))
  | .receiver =>
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2
            (velocityJet address.1) (velocityMode address.2) inserted +
          triadicEnergyFace address.1 address.2
            (velocityMode address.1) (velocityJet address.2) inserted)

/-- Differentiating a fixed-carrier outer covector produces exactly the two untouched-leg jets. -/
theorem hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_fixedCarrier
    (velocityMode : ℝ → SpatialFrequency → ComplexVector)
    (velocityJet : SpatialFrequency → ComplexVector)
    (time : ℝ)
    (hvelocity : ∀ frequency,
      HasDerivAt (fun tau ↦ velocityMode tau frequency)
        (velocityJet frequency) time)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector) :
    HasDerivAt
      (fun tau ↦ physicalH2VelocityExchangedInsertionLegFace
        (velocityMode tau) address leg inserted)
      (physicalH2OuterTestVelocityJetFace
        (velocityMode time) velocityJet address leg inserted) time := by
  cases leg with
  | advecting =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        (hasDerivAt_const time inserted) (hvelocity address.2)
        (hvelocity (completeTransportReceiver address))
      simpa [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot] using
        hface.const_mul (physicalH2ExchangedTriadMultiplier address)
  | transported =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        (hvelocity address.1) (hasDerivAt_const time inserted)
        (hvelocity (completeTransportReceiver address))
      simpa [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot] using
        hface.const_mul (physicalH2ExchangedTriadMultiplier address)
  | receiver =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        (hvelocity address.1) (hvelocity address.2)
        (hasDerivAt_const time inserted)
      simpa [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot] using
        hface.const_mul (physicalH2ExchangedTriadMultiplier address)

/-! ## Actual Stokes substitution -/

/-- The sum of the two Stokes rates carried by the untouched outer legs. -/
def physicalH2OuterTestStokesClock
    (nu : ℝ) (address : CompleteTransportAddress) : PhysicalH2InsertionLeg → ℝ
  | .advecting => nu *
      (torusStokesEigenvalue address.2 +
        torusStokesEigenvalue (completeTransportReceiver address))
  | .transported => nu *
      (torusStokesEigenvalue address.1 +
        torusStokesEigenvalue (completeTransportReceiver address))
  | .receiver => nu *
      (torusStokesEigenvalue address.1 + torusStokesEigenvalue address.2)

/-- The complementary Stokes rate of the fixed inserted carrier. -/
def physicalH2InsertedCarrierStokesClock
    (nu : ℝ) (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) : ℝ :=
  nu * torusStokesEigenvalue (physicalH2InsertionFrequency address leg)

/-- Outer-test and inserted-carrier clocks rejoin the complete three-pin clock. -/
theorem physicalH2OuterTestStokesClock_add_inserted_eq_triadClock
    (nu : ℝ) (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    physicalH2OuterTestStokesClock nu address leg +
        physicalH2InsertedCarrierStokesClock nu address leg =
      physicalH2TriadStokesClock nu address := by
  cases leg <;>
    simp [physicalH2OuterTestStokesClock,
      physicalH2InsertedCarrierStokesClock, physicalH2TriadStokesClock] <;>
    ring

/-- The two nonlinear source insertions on the untouched legs. -/
def physicalH2OuterTestNonlinearRemainder
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector) : ℂ :=
  physicalH2OuterTestVelocityJetFace
    (fun frequency ↦ velocityMode velocity frequency time.1)
    (openProjectedVelocityNonlinearMode solution time)
    address leg inserted

/-- Substituting Stokes-plus-nonlinear jets into the two-leg product rule gives the exact signed
outer clock and leaves only the two nonlinear source insertions. -/
theorem physicalH2OuterTestVelocityJetFace_stokesLeray
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector) :
    physicalH2OuterTestVelocityJetFace
        (fun frequency ↦ velocityMode velocity frequency time.1)
        (fun frequency ↦
          (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
              velocityMode velocity frequency time.1 +
            openProjectedVelocityNonlinearMode solution time frequency))
        address leg inserted =
      physicalH2OuterTestNonlinearRemainder solution time address leg inserted -
        ((physicalH2OuterTestStokesClock nu address leg : ℝ) : ℂ) *
          physicalH2VelocityExchangedInsertionLegFace
            (fun frequency ↦ velocityMode velocity frequency time.1)
            address leg inserted := by
  cases leg <;>
    simp [physicalH2OuterTestVelocityJetFace,
      physicalH2OuterTestNonlinearRemainder,
      physicalH2OuterTestStokesClock,
      physicalH2VelocityExchangedInsertionLegFace,
      triadicEnergyFace, complexAdvectiveInteraction, complexDot,
      dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul] <;>
    ring

/-- **Exact outer-test projective clock.** The actual time-varying outer insertion covector on a
fixed carrier solves a two-leg damped scalar ODE with the complete nonlinear remainder retained. -/
theorem openPeriodicSolutionOn_hasDerivAt_outerInsertionLegFace_fixedCarrier
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector) :
    HasDerivAt
      (fun tau ↦ physicalH2VelocityExchangedInsertionLegFace
        (fun frequency ↦ velocityMode velocity frequency tau)
        address leg inserted)
      (physicalH2OuterTestNonlinearRemainder solution time address leg inserted -
        ((physicalH2OuterTestStokesClock nu address leg : ℝ) : ℂ) *
          physicalH2VelocityExchangedInsertionLegFace
            (fun frequency ↦ velocityMode velocity frequency time.1)
            address leg inserted) time.1 := by
  have hderiv := hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_fixedCarrier
    (fun tau frequency ↦ velocityMode velocity frequency tau)
    (fun frequency ↦
      (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
          velocityMode velocity frequency time.1 +
        openProjectedVelocityNonlinearMode solution time frequency))
    time.1
    (fun frequency ↦
      openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
        solution time frequency)
    address leg inserted
  rw [physicalH2OuterTestVelocityJetFace_stokesLeray
    solution time address leg inserted] at hderiv
  exact hderiv

/-! ## Reciprocal partition and sign -/

/-- The full reciprocal clock partitions unity between the outer test and its omitted inserted
carrier connection. -/
theorem reciprocalClock_mul_outer_add_inserted_eq_one
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) (leg : PhysicalH2InsertionLeg) :
    physicalH2TriadReciprocalClock nu address *
          ((physicalH2OuterTestStokesClock nu address leg : ℝ) : ℂ) +
        physicalH2TriadReciprocalClock nu address *
          ((physicalH2InsertedCarrierStokesClock nu address leg : ℝ) : ℂ) = 1 := by
  rw [← mul_add, ← Complex.ofReal_add]
  rw [physicalH2OuterTestStokesClock_add_inserted_eq_triadClock]
  exact physicalH2TriadReciprocalClock_mul_clock hnu address haddress

/-- The outer clock is nonnegative for nonnegative viscosity. -/
theorem physicalH2OuterTestStokesClock_nonneg
    {nu : ℝ} (hnu : 0 ≤ nu) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) :
    0 ≤ physicalH2OuterTestStokesClock nu address leg := by
  cases leg <;>
    exact mul_nonneg hnu (add_nonneg
      (torusStokesEigenvalue_nonneg _) (torusStokesEigenvalue_nonneg _))

/-- At a nonzero address, every outer test retains at least one nonzero untouched frequency, so
positive viscosity makes its two-leg clock strictly positive. -/
theorem physicalH2OuterTestStokesClock_pos
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) (leg : PhysicalH2InsertionLeg) :
    0 < physicalH2OuterTestStokesClock nu address leg := by
  cases leg with
  | advecting =>
      unfold physicalH2OuterTestStokesClock
      apply mul_pos hnu
      by_cases hq : address.2 = 0
      · have hp : address.1 ≠ 0 := by
          intro hp
          exact haddress (Prod.ext hp hq)
        have hr : completeTransportReceiver address ≠ 0 := by
          intro hr
          apply hp
          simpa [completeTransportReceiver, hq] using hr
        linarith [torusStokesEigenvalue_nonneg address.2,
          torusStokesEigenvalue_pos hr]
      · linarith [torusStokesEigenvalue_pos hq,
          torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  | transported =>
      unfold physicalH2OuterTestStokesClock
      apply mul_pos hnu
      by_cases hp : address.1 = 0
      · have hq : address.2 ≠ 0 := by
          intro hq
          exact haddress (Prod.ext hp hq)
        have hr : completeTransportReceiver address ≠ 0 := by
          intro hr
          apply hq
          simpa [completeTransportReceiver, hp] using hr
        linarith [torusStokesEigenvalue_nonneg address.1,
          torusStokesEigenvalue_pos hr]
      · linarith [torusStokesEigenvalue_pos hp,
          torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  | receiver =>
      unfold physicalH2OuterTestStokesClock
      apply mul_pos hnu
      by_cases hp : address.1 = 0
      · have hq : address.2 ≠ 0 := by
          intro hq
          exact haddress (Prod.ext hp hq)
        linarith [torusStokesEigenvalue_nonneg address.1,
          torusStokesEigenvalue_pos hq]
      · linarith [torusStokesEigenvalue_pos hp,
          torusStokesEigenvalue_nonneg address.2]

/-! ## Exact multiplier order of the outer covector -/

/-- Principal reciprocal-clock outer covector before the inner quadratic source enters. -/
def normalizedClockedPhysicalH2OuterInsertionCovector
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) : ℂ :=
  if address = (0, 0) then 0
  else
    ((physicalH2QuarticPrincipalExchangeSwing address /
      normalizedPhysicalH2TriadClockSquare address : ℝ) : ℂ) *
      normalizedPrincipalOuterInsertionFace address leg inserted
        outerAdvectingMode outerTransportedMode outerReceiverMode

/-- With the inserted Hodge carrier fixed, the normalized outer insertion face has degree one. -/
theorem normalizedPrincipalOuterInsertionFace_dilate_fixedCarrier
    (scale : ℤ) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) :
    normalizedPrincipalOuterInsertionFace
        (dilateCompleteTransportAddress scale address) leg inserted
        outerAdvectingMode outerTransportedMode outerReceiverMode =
      (scale : ℂ) * normalizedPrincipalOuterInsertionFace address leg inserted
        outerAdvectingMode outerTransportedMode outerReceiverMode := by
  cases leg <;>
    simp [normalizedPrincipalOuterInsertionFace, normalizedAdvectiveInteraction,
      dilateCompleteTransportAddress, complexDot,
      smul_dotProduct, smul_eq_mul] <;>
    ring

/-- **The fixed-carrier clocked principal outer covector has exact frequency degree three.** -/
theorem normalizedClockedPhysicalH2OuterInsertionCovector_dilate
    {scale : ℤ} (hscale : scale ≠ 0)
    {address : CompleteTransportAddress} (haddress : address ≠ (0, 0))
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) :
    normalizedClockedPhysicalH2OuterInsertionCovector
        (dilateCompleteTransportAddress scale address) leg inserted
        outerAdvectingMode outerTransportedMode outerReceiverMode =
      (scale : ℂ) ^ 3 *
        normalizedClockedPhysicalH2OuterInsertionCovector address leg inserted
          outerAdvectingMode outerTransportedMode outerReceiverMode := by
  have hdilated : dilateCompleteTransportAddress scale address ≠ (0, 0) :=
    dilateCompleteTransportAddress_ne_zero hscale haddress
  have hscaleReal : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale
  have hscaleComplex : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  have hclock : normalizedPhysicalH2TriadClockSquare address ≠ 0 :=
    (normalizedPhysicalH2TriadClockSquare_pos haddress).ne'
  unfold normalizedClockedPhysicalH2OuterInsertionCovector
  rw [if_neg hdilated, if_neg haddress,
    physicalH2QuarticPrincipalExchangeSwing_dilate,
    normalizedPhysicalH2TriadClockSquare_dilate,
    normalizedPrincipalOuterInsertionFace_dilate_fixedCarrier]
  push_cast
  field_simp

section Audit

#print axioms hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_fixedCarrier
#print axioms physicalH2OuterTestStokesClock_add_inserted_eq_triadClock
#print axioms physicalH2OuterTestVelocityJetFace_stokesLeray
#print axioms openPeriodicSolutionOn_hasDerivAt_outerInsertionLegFace_fixedCarrier
#print axioms reciprocalClock_mul_outer_add_inserted_eq_one
#print axioms physicalH2OuterTestStokesClock_pos
#print axioms normalizedClockedPhysicalH2OuterInsertionCovector_dilate

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2OuterTestProjectiveClock
