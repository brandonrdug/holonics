import ElementaryHolonics.Millennium.NavierStokesPhysicalH2OuterTestProjectiveClock
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment

/-!
# The combined physical-H2 projective outer clock

**[proved-derived; formal-checked]** This module composes two previously separate exact currents.
The actual outer insertion covector varies through the two untouched Navier--Stokes velocity modes,
while its inserted Hodge carrier follows the division-free Hermitian projective transport.  Their
literal product rule is

`B' = H + N - Ω_outer * B`.

Here `H` is the transported horizontal carrier current, `N` is exactly the two untouched-leg
nonlinear source variation, and `Ω_outer` is the positive two-leg Stokes clock at every nonzero
address and positive viscosity.  Integration retains both endpoint values and both unresolved
currents.  The Hermitian connection is totalized, so no nonvanishing-mode hypothesis is introduced
and the zero-mode fibre remains the full literal carrier jet.

No real-part or norm receiver is imposed.  Consequently the signed scalar generator below is not
promoted to coercivity, an estimate, terminal control, or a Navier--Stokes solution.
-/

noncomputable section

open Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterClock

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2OuterTestProjectiveClock
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The actual outer receiver and the transported inserted carrier -/

/-- The actual physical-H2 outer insertion covector as a continuous real-linear receiver. -/
def physicalH2OuterInsertionRealCLM
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    ComplexVector →L[ℝ] ℂ :=
  ⟨(physicalH2VelocityExchangedInsertionLegLinearMap
      velocityMode address leg).restrictScalars ℝ,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem physicalH2OuterInsertionRealCLM_apply
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector) :
    physicalH2OuterInsertionRealCLM velocityMode address leg inserted =
      physicalH2VelocityExchangedInsertionLegFace
        velocityMode address leg inserted := rfl

/-- The addressed boundary obtained by testing a projectively transported Hodge carrier with the
actual contemporaneous physical-H2 outer covector. -/
def physicalH2CombinedProjectiveOuterBoundary
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  physicalH2VelocityExchangedInsertionLegFace
    (fun outerFrequency ↦ velocityMode velocity outerFrequency time)
    address leg
    (nonzeroModeHodgeReconstruction frequency (transport time • mode time))

/-- The same boundary is literally the generic projective-Hodge boundary with the actual
physical-H2 outer receiver installed. -/
theorem physicalH2CombinedProjectiveOuterBoundary_eq_projectiveBoundary
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) :
    physicalH2CombinedProjectiveOuterBoundary
        velocity address leg frequency transport mode time =
      projectiveOuterHodgeBoundary frequency
        (fun clock ↦ physicalH2OuterInsertionRealCLM
          (fun outerFrequency ↦ velocityMode velocity outerFrequency clock)
          address leg)
        transport mode time := rfl

/-- The projectively horizontal carrier current through the actual outer covector. -/
def physicalH2CombinedProjectiveHorizontalContribution
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  physicalH2VelocityExchangedInsertionLegFace
    (fun outerFrequency ↦ velocityMode velocity outerFrequency time)
    address leg
    (nonzeroModeHodgeReconstruction frequency
      (transport time • ownModeHermitianHorizontalJet (mode time) (modeJet time)))

/-- The horizontal contribution is exactly the generic projective horizontal current after
installing the actual physical-H2 outer receiver. -/
theorem physicalH2CombinedProjectiveHorizontalContribution_eq_projectiveCurrent
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector) (time : ℝ) :
    physicalH2CombinedProjectiveHorizontalContribution
        velocity address leg frequency transport mode modeJet time =
      projectiveOuterHodgeHorizontalCurrent frequency
        (fun clock ↦ physicalH2OuterInsertionRealCLM
          (fun outerFrequency ↦ velocityMode velocity outerFrequency clock)
          address leg)
        transport mode modeJet time := rfl

/-! ## Exact moving-carrier product rule -/

/-- The algebraic joint between the fixed-carrier outer derivative and a moving inserted carrier.
It retains all three product-rule occurrences while grouping the two untouched jets together. -/
theorem hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_movingCarrier
    (outerMode : ℝ → SpatialFrequency → ComplexVector)
    (outerJet : SpatialFrequency → ComplexVector)
    (inserted : ℝ → ComplexVector) (insertedJet : ComplexVector)
    (time : ℝ)
    (houter : ∀ outerFrequency,
      HasDerivAt (fun clock ↦ outerMode clock outerFrequency)
        (outerJet outerFrequency) time)
    (hinserted : HasDerivAt inserted insertedJet time)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    HasDerivAt
      (fun clock ↦ physicalH2VelocityExchangedInsertionLegFace
        (outerMode clock) address leg (inserted clock))
      (physicalH2OuterTestVelocityJetFace
          (outerMode time) outerJet address leg (inserted time) +
        physicalH2VelocityExchangedInsertionLegFace
          (outerMode time) address leg insertedJet) time := by
  cases leg with
  | advecting =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        hinserted (houter address.2)
        (houter (completeTransportReceiver address))
      convert hface.const_mul (physicalH2ExchangedTriadMultiplier address) using 1
      all_goals try rfl
      all_goals
        simp [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot, add_comm,
        add_left_comm]
        all_goals try ring
  | transported =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        (houter address.1) hinserted
        (houter (completeTransportReceiver address))
      convert hface.const_mul (physicalH2ExchangedTriadMultiplier address) using 1
      all_goals try rfl
      all_goals
        simp [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot, add_comm,
        add_left_comm]
        all_goals try ring
  | receiver =>
      have hface := hasDerivAt_triadicEnergyFace address.1 address.2
        (houter address.1) (houter address.2) hinserted
      convert hface.const_mul (physicalH2ExchangedTriadMultiplier address) using 1
      all_goals try rfl
      all_goals
        simp [physicalH2VelocityExchangedInsertionLegFace,
        physicalH2OuterTestVelocityJetFace, triadicEnergyFace,
        complexAdvectiveInteraction, complexDot, add_comm]
        all_goals try ring

/-! ## The actual combined projective outer clock -/

/-- The two untouched-leg nonlinear source insertions evaluated on the transported Hodge
carrier. -/
def physicalH2CombinedProjectiveOuterNonlinearVariation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) : ℂ :=
  physicalH2OuterTestNonlinearRemainder solution time address leg
    (nonzeroModeHodgeReconstruction frequency
      (transport time.1 • mode time.1))

/-- The signed positive-rate outer Stokes share applied to the combined boundary. -/
def physicalH2CombinedProjectiveOuterStokesCurrent
    (nu : ℝ) (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  ((physicalH2OuterTestStokesClock nu address leg : ℝ) : ℂ) *
    physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time

/-- **Exact combined addressed clock law.** The transported Hodge carrier contributes its
horizontal current; the two untouched Navier--Stokes legs contribute their nonlinear variation
and the negative outer Stokes share.  The totalized Hermitian connection requires no nonzero-mode
hypothesis. -/
theorem openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector)
    (hmode : HasDerivAt mode (modeJet time.1) time.1)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time.1) (modeJet time.1) *
        transport time.1) time.1) :
    HasDerivAt
      (physicalH2CombinedProjectiveOuterBoundary
        velocity address leg frequency transport mode)
      (physicalH2CombinedProjectiveHorizontalContribution
          velocity address leg frequency transport mode modeJet time.1 +
        physicalH2CombinedProjectiveOuterNonlinearVariation
          solution time address leg frequency transport mode -
        physicalH2CombinedProjectiveOuterStokesCurrent
          nu velocity address leg frequency transport mode time.1) time.1 := by
  have hparallel := hasDerivAt_parallelTransport_mode
    mode (modeJet time.1) transport time.1 hmode htransport
  have hcarrier :=
    (nonzeroModeHodgeReconstructionRealCLM frequency).hasFDerivAt.comp_hasDerivAt
      time.1 hparallel
  have hcombined :=
    hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_movingCarrier
      (fun clock outerFrequency ↦ velocityMode velocity outerFrequency clock)
      (fun outerFrequency ↦
        (((-(nu * torusStokesEigenvalue outerFrequency) : ℝ) : ℂ) •
            velocityMode velocity outerFrequency time.1 +
          openProjectedVelocityNonlinearMode solution time outerFrequency))
      (fun clock ↦ nonzeroModeHodgeReconstruction frequency
        (transport clock • mode clock))
      (nonzeroModeHodgeReconstruction frequency
        (transport time.1 •
          ownModeHermitianHorizontalJet (mode time.1) (modeJet time.1)))
      time.1
      (fun outerFrequency ↦
        openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
          solution time outerFrequency)
      hcarrier address leg
  rw [physicalH2OuterTestVelocityJetFace_stokesLeray solution time address leg
    (nonzeroModeHodgeReconstruction frequency
      (transport time.1 • mode time.1))] at hcombined
  change HasDerivAt
    (fun clock ↦ physicalH2VelocityExchangedInsertionLegFace
      (fun outerFrequency ↦ velocityMode velocity outerFrequency clock)
      address leg
      (nonzeroModeHodgeReconstruction frequency
        (transport clock • mode clock))) _ time.1
  simpa [physicalH2CombinedProjectiveOuterBoundary,
    physicalH2CombinedProjectiveHorizontalContribution,
    physicalH2CombinedProjectiveOuterNonlinearVariation,
    physicalH2CombinedProjectiveOuterStokesCurrent,
    nonzeroModeHodgeReconstructionRealCLM_apply, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using hcombined

/-- At a zero-mode crossing the same addressed law retains the full literal carrier jet; the
transport derivative is zero and no division or nonvanishing premise is introduced. -/
theorem openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary_zeroCrossing
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector)
    (hzero : mode time.1 = 0)
    (hmode : HasDerivAt mode (modeJet time.1) time.1)
    (htransport : HasDerivAt transport 0 time.1) :
    HasDerivAt
      (physicalH2CombinedProjectiveOuterBoundary
        velocity address leg frequency transport mode)
      (physicalH2CombinedProjectiveHorizontalContribution
          velocity address leg frequency transport mode modeJet time.1 +
        physicalH2CombinedProjectiveOuterNonlinearVariation
          solution time address leg frequency transport mode -
        physicalH2CombinedProjectiveOuterStokesCurrent
          nu velocity address leg frequency transport mode time.1) time.1 := by
  apply openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary
    solution time address leg frequency transport mode modeJet hmode
  simpa [hzero] using htransport

/-! ## Exact boundary balance -/

/-- Extend the open-lifespan nonlinear variation by zero outside its declared domain solely to
give the interval integral a total real-time integrand.  Every theorem below restricts the whole
integration interval to the open lifespan. -/
def physicalH2CombinedProjectiveOuterNonlinearVariationOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  if htime : time ∈ Ioo 0 T then
    physicalH2CombinedProjectiveOuterNonlinearVariation solution
      ⟨time, htime⟩ address leg frequency transport mode
  else 0

theorem physicalH2CombinedProjectiveOuterNonlinearVariationOn_of_mem
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode : ℝ → ComplexVector) {time : ℝ} (htime : time ∈ Ioo 0 T) :
    physicalH2CombinedProjectiveOuterNonlinearVariationOn solution
        address leg frequency transport mode time =
      physicalH2CombinedProjectiveOuterNonlinearVariation solution
        ⟨time, htime⟩ address leg frequency transport mode := by
  simp [physicalH2CombinedProjectiveOuterNonlinearVariationOn, htime]

/-- **Integrated combined projective clock identity.** Endpoint difference plus the complete
positive-rate outer Stokes share equals the integrated horizontal carrier current plus the two
untouched-leg nonlinear variation.  All four terms remain visible. -/
theorem integral_combinedProjectiveOuter_boundary_add_stokes_eq_horizontal_add_nonlinear
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode modeJet : ℝ → ComplexVector) (a b : ℝ)
    (hinterval : uIcc a b ⊆ Ioo 0 T)
    (hmode : ∀ time ∈ uIcc a b,
      HasDerivAt mode (modeJet time) time)
    (htransport : ∀ time ∈ uIcc a b,
      HasDerivAt transport
        (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time)
    (hhorizontal : IntervalIntegrable
      (physicalH2CombinedProjectiveHorizontalContribution
        velocity address leg frequency transport mode modeJet)
      MeasureTheory.volume a b)
    (hnonlinear : IntervalIntegrable
      (physicalH2CombinedProjectiveOuterNonlinearVariationOn solution
        address leg frequency transport mode)
      MeasureTheory.volume a b)
    (hstokes : IntervalIntegrable
      (physicalH2CombinedProjectiveOuterStokesCurrent
        nu velocity address leg frequency transport mode)
      MeasureTheory.volume a b) :
    physicalH2CombinedProjectiveOuterBoundary
          velocity address leg frequency transport mode b -
        physicalH2CombinedProjectiveOuterBoundary
          velocity address leg frequency transport mode a +
        ∫ time in a..b,
          physicalH2CombinedProjectiveOuterStokesCurrent
            nu velocity address leg frequency transport mode time =
      (∫ time in a..b,
          physicalH2CombinedProjectiveHorizontalContribution
            velocity address leg frequency transport mode modeJet time) +
        ∫ time in a..b,
          physicalH2CombinedProjectiveOuterNonlinearVariationOn solution
            address leg frequency transport mode time := by
  have hderiv : ∀ time ∈ uIcc a b,
      HasDerivAt
        (physicalH2CombinedProjectiveOuterBoundary
          velocity address leg frequency transport mode)
        (physicalH2CombinedProjectiveHorizontalContribution
            velocity address leg frequency transport mode modeJet time +
          physicalH2CombinedProjectiveOuterNonlinearVariationOn solution
            address leg frequency transport mode time -
          physicalH2CombinedProjectiveOuterStokesCurrent
            nu velocity address leg frequency transport mode time) time := by
    intro time htime
    have hinterior := hinterval htime
    have hactual :=
      openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary
        solution ⟨time, hinterior⟩ address leg frequency transport mode modeJet
        (hmode time htime) (htransport time htime)
    simpa [physicalH2CombinedProjectiveOuterNonlinearVariationOn, hinterior] using hactual
  have hintegrable := (hhorizontal.add hnonlinear).sub hstokes
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable
  rw [intervalIntegral.integral_sub (hhorizontal.add hnonlinear) hstokes,
    intervalIntegral.integral_add hhorizontal hnonlinear] at hftc
  linear_combination -hftc

/-- The Stokes coefficient appearing in the integrated balance is strictly positive at every
nonzero address under positive viscosity. -/
theorem combinedProjectiveOuter_stokesCoefficient_pos
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) (leg : PhysicalH2InsertionLeg) :
    0 < physicalH2OuterTestStokesClock nu address leg :=
  physicalH2OuterTestStokesClock_pos hnu address haddress leg

section Audit

#print axioms physicalH2CombinedProjectiveOuterBoundary_eq_projectiveBoundary
#print axioms hasDerivAt_physicalH2VelocityExchangedInsertionLegFace_movingCarrier
#print axioms openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary
#print axioms openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary_zeroCrossing
#print axioms integral_combinedProjectiveOuter_boundary_add_stokes_eq_horizontal_add_nonlinear
#print axioms combinedProjectiveOuter_stokesCoefficient_pos

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterClock
