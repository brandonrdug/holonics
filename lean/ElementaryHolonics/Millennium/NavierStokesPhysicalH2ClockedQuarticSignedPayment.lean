import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase

/-!
# Receiver-transport commutator for the clocked physical-H2 quartic current

**[proved-derived; formal-checked]** The own-mode Hermitian `H2` covector kills the source-curl
phase, but the differentiated outer triad covector need not.  The missing signed current is
therefore their receiver-transport commutator:

`outer insertion covector ∘ Hodge - own-mode Hermitian H2 covector`.

This owner retains the outer address, insertion leg, inner advecting pin, time-varying velocity
test, own-mode receiver, Hodge passage, and zero-receiver fibre.  On the Hermitian phase the second
covector vanishes exactly, so the commutator is precisely the reopened outer source--test current.

The admitted nonzero witness then fires the proposed scalar-multiplier payment: no scalar swing
can transport the own-mode covector into the outer covector on every source curl, because the
former is zero on the retained witness phase while the latter is `-1`.  Hence an exact
future-blind payment cannot be obtained from the own-mode phase cancellation alone.  A further
time/outer-covector commutator estimate is required.

No norm estimate, viscosity absorption, terminal control, or continuation claim is made.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticSignedPayment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The two covectors and their exact difference -/

/-- The complex own-mode order-one-plus-order-two `H2` covector on one source curl. -/
def ownModeHermitianH2CurlCovector
    (output : SpatialFrequency) (ownVorticity sourceCurl : ComplexVector) : ℂ :=
  complexVectorHermitianPairing
    ((((1 + torusStokesEigenvalue output : ℝ) : ℂ)) • ownVorticity)
    sourceCurl

/-- The differentiated outer triad covector, rebased through Hodge to the same source-curl
carrier as the own-mode covector. -/
def outerInsertionHodgeCurlCovector
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (sourceCurl : ComplexVector) : ℂ :=
  physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
    (nonzeroModeHodgeReconstruction
      (physicalH2InsertionFrequency address leg) sourceCurl)

/-- The exact receiver-transport commutator.  Both summands have the same source-curl domain;
their difference measures the failure of own-mode phase orthogonality to commute with the outer
product-rule test. -/
def physicalH2ReceiverTransportCommutator
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (ownVorticity sourceCurl : ComplexVector) : ℂ :=
  outerInsertionHodgeCurlCovector velocityMode address leg sourceCurl -
    ownModeHermitianH2CurlCovector
      (physicalH2InsertionFrequency address leg) ownVorticity sourceCurl

/-- A real derivative weight crossing the first Hermitian argument scales the pairing by that
same real weight. -/
theorem ownModeHermitianH2CurlCovector_eq_weight_mul
    (output : SpatialFrequency) (receiver sourceCurl : ComplexVector) :
    ownModeHermitianH2CurlCovector output receiver sourceCurl =
      ((1 + torusStokesEigenvalue output : ℝ) : ℂ) *
        complexVectorHermitianPairing receiver sourceCurl := by
  unfold ownModeHermitianH2CurlCovector complexVectorHermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  ring

/-- The own-mode covector vanishes as a complex current, not merely after taking its real
production shadow. -/
theorem ownModeHermitianH2CurlCovector_modeHermitianPhase_eq_zero
    (output : SpatialFrequency) (receiver sourceCurl : ComplexVector) :
    ownModeHermitianH2CurlCovector output receiver
        (modeHermitianPhase receiver sourceCurl) = 0 := by
  rw [ownModeHermitianH2CurlCovector_eq_weight_mul,
    complexVectorHermitianPairing_modeHermitianPhase_eq_zero, mul_zero]

/-- On the exact Hermitian phase fibre the commutator is the reopened outer covector. -/
theorem physicalH2ReceiverTransportCommutator_modeHermitianPhase
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (ownVorticity sourceCurl : ComplexVector) :
    physicalH2ReceiverTransportCommutator velocityMode address leg ownVorticity
        (modeHermitianPhase ownVorticity sourceCurl) =
      outerInsertionHodgeCurlCovector velocityMode address leg
        (modeHermitianPhase ownVorticity sourceCurl) := by
  unfold physicalH2ReceiverTransportCommutator
  rw [ownModeHermitianH2CurlCovector_modeHermitianPhase_eq_zero, sub_zero]

/-! ## The clocked, fully addressed occurrence -/

/-- One time-varying finite clocked commutator occurrence.  `velocityMode time` supplies both the
outer covector and the own output-mode vorticity receiver; `alpha` retains the full inner joining
lineage. -/
def clockedPhysicalH2ReceiverTransportCommutatorOccurrenceAt
    (nu : ℝ) (velocityMode : ℝ → SpatialFrequency → ComplexVector) (time : ℝ)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (alpha : SpatialFrequency) : ℂ :=
  let output := physicalH2InsertionFrequency address leg
  let ownVorticity := physicalH2ModeVorticityReceiver (velocityMode time) output
  let sourceCurl := finitePhysicalH2ProjectedSourceCurlAtom
    (velocityMode time) output alpha
  physicalH2TriadReciprocalClock nu address *
    physicalH2ReceiverTransportCommutator (velocityMode time) address leg ownVorticity
      (modeHermitianPhase ownVorticity sourceCurl)

/-- The clocked commutator is exactly the outer Hodge test on the Hermitian phase, with no
discarded zero-receiver occurrence. -/
theorem clockedPhysicalH2ReceiverTransportCommutatorOccurrenceAt_eq_outerPhase
    (nu : ℝ) (velocityMode : ℝ → SpatialFrequency → ComplexVector) (time : ℝ)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (alpha : SpatialFrequency) :
    clockedPhysicalH2ReceiverTransportCommutatorOccurrenceAt
        nu velocityMode time address leg alpha =
      physicalH2TriadReciprocalClock nu address *
        outerInsertionHodgeCurlCovector (velocityMode time) address leg
          (finitePhysicalH2ProjectedSourceOwnModePhaseCurlAtom
            (velocityMode time) (physicalH2InsertionFrequency address leg) alpha) := by
  unfold clockedPhysicalH2ReceiverTransportCommutatorOccurrenceAt
    finitePhysicalH2ProjectedSourceOwnModePhaseCurlAtom
  dsimp only
  rw [physicalH2ReceiverTransportCommutator_modeHermitianPhase]

/-! ## Firing failure of scalar multiplier transport -/

/-- The normalized witness outer covector on the common source-curl carrier. -/
def modeReceiverRebaseWitnessOuterCurlCovector (sourceCurl : ComplexVector) : ℂ :=
  normalizedPrincipalOuterInsertionFace principalWitnessOuterAddress .advecting
    (nonzeroModeHodgeReconstruction modeReceiverRebaseWitnessOutput sourceCurl)
    principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
    principalWitnessOuterReceiverMode

/-- The corresponding own-mode Hermitian `H2` covector. -/
def modeReceiverRebaseWitnessOwnH2CurlCovector (sourceCurl : ComplexVector) : ℂ :=
  ownModeHermitianH2CurlCovector modeReceiverRebaseWitnessOutput
    modeReceiverRebaseWitnessOwnVorticity sourceCurl

/-- The witness lies in the radical of the own-mode covector. -/
theorem modeReceiverRebaseWitnessOwnH2CurlCovector_phase_eq_zero :
    modeReceiverRebaseWitnessOwnH2CurlCovector
        modeReceiverRebaseWitnessPhaseCurl = 0 := by
  unfold modeReceiverRebaseWitnessOwnH2CurlCovector
  rw [modeReceiverRebaseWitnessOwnVorticity_eq_zero]
  simp [ownModeHermitianH2CurlCovector, complexVectorHermitianPairing]

/-- The same retained phase is read nontrivially by the outer covector. -/
theorem modeReceiverRebaseWitnessOuterCurlCovector_phase_eq_neg_one :
    modeReceiverRebaseWitnessOuterCurlCovector
        modeReceiverRebaseWitnessPhaseCurl = -1 := by
  exact modeReceiverRebaseWitness_outerAdvectingPhase_eq_neg_one

/-- The receiver-transport commutator itself is the nonzero face `-1`. -/
theorem modeReceiverRebaseWitness_receiverTransportCommutator_eq_neg_one :
    modeReceiverRebaseWitnessOuterCurlCovector modeReceiverRebaseWitnessPhaseCurl -
        modeReceiverRebaseWitnessOwnH2CurlCovector modeReceiverRebaseWitnessPhaseCurl = -1 := by
  rw [modeReceiverRebaseWitnessOuterCurlCovector_phase_eq_neg_one,
    modeReceiverRebaseWitnessOwnH2CurlCovector_phase_eq_zero, sub_zero]

/-- **[counterexample; formal-checked]** No scalar multiplier swing transports the own-mode `H2`
covector into the differentiated outer covector on all source curls.  The obstruction fires on
the already-retained zero-own-vorticity phase fibre. -/
theorem no_scalar_multiplier_transports_ownModeH2Covector_to_outerCovector :
    ¬ ∃ multiplier : ℂ, ∀ sourceCurl : ComplexVector,
      modeReceiverRebaseWitnessOuterCurlCovector sourceCurl =
        multiplier * modeReceiverRebaseWitnessOwnH2CurlCovector sourceCurl := by
  rintro ⟨multiplier, htransport⟩
  have hwitness := htransport modeReceiverRebaseWitnessPhaseCurl
  rw [modeReceiverRebaseWitnessOuterCurlCovector_phase_eq_neg_one,
    modeReceiverRebaseWitnessOwnH2CurlCovector_phase_eq_zero, mul_zero] at hwitness
  norm_num at hwitness

section Audit

#print axioms ownModeHermitianH2CurlCovector_modeHermitianPhase_eq_zero
#print axioms physicalH2ReceiverTransportCommutator_modeHermitianPhase
#print axioms clockedPhysicalH2ReceiverTransportCommutatorOccurrenceAt_eq_outerPhase
#print axioms modeReceiverRebaseWitness_receiverTransportCommutator_eq_neg_one
#print axioms no_scalar_multiplier_transports_ownModeH2Covector_to_outerCovector

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticSignedPayment
