import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol

/-!
# Rebase of the physical-H2 phase split to its own Fourier-mode receiver

**[proved-derived; formal-checked]** A Fourier vorticity coefficient is generally complex, so
the bilinear direction projection used by the pointwise real-vorticity chart is not the
orthogonal projection for the Hermitian `H2` energy receiver.  This owner supplies the exact
Hermitian mode projection.  Its phase fibre is killed by the derivative-weighted one-mode `H2`
test before the reciprocal triad clock is opened.

The final witness records the precise reopening at the differentiated cubic current.  The
inserted output mode has zero velocity and hence zero own-mode vorticity test, while a nonzero
quadratic source curl occupies its entire Hermitian phase fibre.  Hodge reconstruction returns
the source velocity exactly, and the advancing outer insertion functional reads it as `-1`.
Thus direct mode-energy orthogonality does not pass through the three-leg product-rule pullback:
the outer test is a covector built from the other two triad modes, not the inserted mode's own
Hermitian energy covector.

No estimate, time integration, terminal control, or continuation claim is made.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The exact Hermitian receiver chart -/

/-- Complex amplitude of `source` along `receiver` for the actual Hermitian Fourier-energy
pairing.  Division is totalized; the zero receiver retains the whole source in the phase fibre. -/
def modeHermitianAlignedAmplitude
    (receiver source : ComplexVector) : ℂ :=
  complexVectorHermitianPairing receiver source /
    complexVectorHermitianPairing receiver receiver

/-- The part of one source curl which is Hermitian-orthogonal to its own Fourier-mode receiver. -/
def modeHermitianPhase
    (receiver source : ComplexVector) : ComplexVector :=
  source - modeHermitianAlignedAmplitude receiver source • receiver

/-- The Hermitian phase and aligned occurrence reconstruct the source without a choice of basis. -/
theorem modeHermitianPhase_add_aligned
    (receiver source : ComplexVector) :
    modeHermitianPhase receiver source +
        modeHermitianAlignedAmplitude receiver source • receiver = source := by
  simp [modeHermitianPhase]

private theorem complexVectorHermitianPairing_sub_smul
    (receiver source : ComplexVector) (amplitude : ℂ) :
    complexVectorHermitianPairing receiver (source - amplitude • receiver) =
      complexVectorHermitianPairing receiver source -
        amplitude * complexVectorHermitianPairing receiver receiver := by
  simp [complexVectorHermitianPairing, Fin.sum_univ_succ]
  ring

private theorem complexVectorEuclideanSquare_pos_of_ne_zero
    {receiver : ComplexVector} (hreceiver : receiver ≠ 0) :
    0 < complexVectorEuclideanSquare receiver := by
  have hfunction : (fun component : Fin 3 ↦ receiver component) ≠ 0 := by
    simpa only using hreceiver
  obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hfunction
  refine Finset.sum_pos' (fun index _hindex ↦ Complex.normSq_nonneg _) ?_
  exact ⟨component, Finset.mem_univ component, Complex.normSq_pos.mpr hcomponent⟩

private theorem complexVectorHermitianPairing_self_ne_zero_of_ne_zero
    {receiver : ComplexVector} (hreceiver : receiver ≠ 0) :
    complexVectorHermitianPairing receiver receiver ≠ 0 := by
  rw [complexVectorHermitianPairing_self_eq]
  exact Complex.ofReal_ne_zero.mpr
    (complexVectorEuclideanSquare_pos_of_ne_zero hreceiver).ne'

/-- Unlike the standing bilinear point-vorticity projection, this mode projection is exactly
orthogonal for the complex Hermitian Fourier receiver, including its zero chart. -/
theorem complexVectorHermitianPairing_modeHermitianPhase_eq_zero
    (receiver source : ComplexVector) :
    complexVectorHermitianPairing receiver
        (modeHermitianPhase receiver source) = 0 := by
  by_cases hreceiver : receiver = 0
  · subst receiver
    simp [modeHermitianPhase, modeHermitianAlignedAmplitude,
      complexVectorHermitianPairing]
  · rw [modeHermitianPhase, complexVectorHermitianPairing_sub_smul,
      modeHermitianAlignedAmplitude,
      div_mul_cancel₀ _
        (complexVectorHermitianPairing_self_ne_zero_of_ne_zero hreceiver),
      sub_self]

/-- The real `H2` production receiver therefore kills the Hermitian phase exactly. -/
theorem sourceTestProductionReading_modeHermitianPhase_eq_zero
    (receiver source : ComplexVector) :
    sourceTestProductionReading receiver
        (modeHermitianPhase receiver source) = 0 := by
  have hpair := complexVectorHermitianPairing_modeHermitianPhase_eq_zero receiver source
  exact congrArg Complex.re hpair

/-- The full order-one-plus-order-two vorticity test has the same zero phase reading. -/
theorem derivativeWeighted_modeHermitianPhase_eq_zero
    (frequency : SpatialFrequency) (receiver source : ComplexVector) :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) • receiver)
        (modeHermitianPhase receiver source) = 0 := by
  rw [sourceTestProductionReading_real_smul_test,
    sourceTestProductionReading_modeHermitianPhase_eq_zero, mul_zero]

/-- This is the sign used by the Navier--Stokes source orientation in the exact one-mode
order-one-plus-order-two bridge. -/
theorem derivativeWeighted_neg_modeHermitianPhase_eq_zero
    (frequency : SpatialFrequency) (receiver source : ComplexVector) :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) • receiver)
        (-modeHermitianPhase receiver source) = 0 := by
  rw [sourceTestProductionReading_neg_source,
    derivativeWeighted_modeHermitianPhase_eq_zero, neg_zero]

/-! ## Rebase to the inserted source output mode -/

/-- The own-mode vorticity receiver at the output occupied by an inserted velocity source. -/
def physicalH2ModeVorticityReceiver
    (velocityMode : SpatialFrequency → ComplexVector)
    (output : SpatialFrequency) : ComplexVector :=
  frequencyCurlMultiplier output (velocityMode output)

/-- Hermitian phase of one finite projected source curl relative to the output mode's own
vorticity coefficient. -/
def finitePhysicalH2ProjectedSourceOwnModePhaseCurlAtom
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  modeHermitianPhase
    (physicalH2ModeVorticityReceiver velocityMode output)
    (finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha)

/-- Before reciprocal-clock integration, every inserted source occurrence has zero phase reading
against the derivative-weighted `H2` test of its own output coefficient. -/
theorem derivativeWeighted_finiteProjectedSourceOwnModePhase_eq_zero
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue output : ℝ) : ℂ)) •
          physicalH2ModeVorticityReceiver velocityMode output)
        (finitePhysicalH2ProjectedSourceOwnModePhaseCurlAtom
          velocityMode output alpha) = 0 := by
  exact derivativeWeighted_modeHermitianPhase_eq_zero output _ _

/-! ## Exact reopening by an outer product-rule test -/

def modeReceiverRebaseWitnessOutput : SpatialFrequency :=
  physicalH2InsertionFrequency principalWitnessOuterAddress .advecting

def modeReceiverRebaseWitnessSourceMode : ComplexVector :=
  normalizedPrincipalProjectedSourceAtom
    modeReceiverRebaseWitnessOutput principalWitnessInnerAlpha
    principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode

def modeReceiverRebaseWitnessSourceCurl : ComplexVector :=
  frequencyCurlMultiplier modeReceiverRebaseWitnessOutput
    modeReceiverRebaseWitnessSourceMode

def modeReceiverRebaseWitnessOwnVorticity : ComplexVector :=
  frequencyCurlMultiplier modeReceiverRebaseWitnessOutput 0

def modeReceiverRebaseWitnessPhaseCurl : ComplexVector :=
  modeHermitianPhase modeReceiverRebaseWitnessOwnVorticity
    modeReceiverRebaseWitnessSourceCurl

@[simp]
theorem modeReceiverRebaseWitnessOwnVorticity_eq_zero :
    modeReceiverRebaseWitnessOwnVorticity = 0 := by
  ext component
  fin_cases component <;>
    simp [modeReceiverRebaseWitnessOwnVorticity, frequencyCurlMultiplier,
      complexCross, crossProduct]

/-- At an unoccupied velocity output, the nonzero source curl lies wholly in the own-mode phase
fibre. -/
theorem modeReceiverRebaseWitnessPhaseCurl_eq_sourceCurl :
    modeReceiverRebaseWitnessPhaseCurl = modeReceiverRebaseWitnessSourceCurl := by
  simp [modeReceiverRebaseWitnessPhaseCurl, modeHermitianPhase,
    modeHermitianAlignedAmplitude]

private theorem modeReceiverRebaseWitnessOutput_ne_zero :
    modeReceiverRebaseWitnessOutput ≠ 0 := by
  intro hzero
  have hcomponent := congrArg (fun frequency : SpatialFrequency ↦ frequency 0) hzero
  norm_num [modeReceiverRebaseWitnessOutput, principalWitnessOuterAddress,
    physicalH2InsertionFrequency] at hcomponent

private theorem modeReceiverRebaseWitnessSourceMode_divergenceFree :
    complexDot (complexFrequencyVector modeReceiverRebaseWitnessOutput)
        modeReceiverRebaseWitnessSourceMode = 0 := by
  exact complexDot_normalizedPrincipalProjectedSourceAtom_eq_zero _ _ _ _

/-- Hodge transport of the own-mode phase returns the same inserted velocity source exactly. -/
theorem nonzeroModeHodgeReconstruction_modeReceiverRebaseWitnessPhaseCurl :
    nonzeroModeHodgeReconstruction modeReceiverRebaseWitnessOutput
        modeReceiverRebaseWitnessPhaseCurl =
      modeReceiverRebaseWitnessSourceMode := by
  rw [modeReceiverRebaseWitnessPhaseCurl_eq_sourceCurl]
  exact nonzeroModeHodgeReconstruction_frequencyCurlMultiplier
    modeReceiverRebaseWitnessOutput_ne_zero _
    modeReceiverRebaseWitnessSourceMode_divergenceFree

/-- The phase is not a zero artefact: its Hodge reconstruction is the explicit nonzero `-e₂`
source of the principal witness. -/
theorem modeReceiverRebaseWitnessPhaseCurl_ne_zero :
    modeReceiverRebaseWitnessPhaseCurl ≠ 0 := by
  intro hzero
  have hlift := nonzeroModeHodgeReconstruction_modeReceiverRebaseWitnessPhaseCurl
  rw [hzero] at hlift
  simp [nonzeroModeHodgeReconstruction] at hlift
  have hsource : modeReceiverRebaseWitnessSourceMode =
      (![0, -1, 0] : ComplexVector) := by
    exact principalWitness_projectedSourceAtom
  rw [hsource] at hlift
  have hcomponent := congrFun hlift 1
  norm_num at hcomponent

/-- The direct derivative-weighted `H2` phase test is zero at the same occurrence. -/
theorem modeReceiverRebaseWitness_directH2Phase_eq_zero :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue modeReceiverRebaseWitnessOutput : ℝ) : ℂ)) •
          modeReceiverRebaseWitnessOwnVorticity)
        modeReceiverRebaseWitnessPhaseCurl = 0 := by
  exact derivativeWeighted_modeHermitianPhase_eq_zero
    modeReceiverRebaseWitnessOutput _ _

/-- **[counterexample; formal-checked]** The advancing product-rule leg reopens the exact phase
which the inserted mode's own `H2` receiver kills.  The outer covector supplied by the other two
triad modes reads the Hodge-lifted phase as `-1`. -/
theorem modeReceiverRebaseWitness_outerAdvectingPhase_eq_neg_one :
    normalizedPrincipalOuterInsertionFace principalWitnessOuterAddress .advecting
        (nonzeroModeHodgeReconstruction modeReceiverRebaseWitnessOutput
          modeReceiverRebaseWitnessPhaseCurl)
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode = -1 := by
  rw [nonzeroModeHodgeReconstruction_modeReceiverRebaseWitnessPhaseCurl]
  exact principalWitness_outerInsertionFace

/-- The zero direct receiver, nonzero retained phase, and nonzero outer reading are one exact
reconstruction fibre; none is inferred from a norm or terminal value. -/
theorem modeReceiverRebaseWitness_direct_zero_outer_nonzero :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue modeReceiverRebaseWitnessOutput : ℝ) : ℂ)) •
          modeReceiverRebaseWitnessOwnVorticity)
        modeReceiverRebaseWitnessPhaseCurl = 0 ∧
      modeReceiverRebaseWitnessPhaseCurl ≠ 0 ∧
      normalizedPrincipalOuterInsertionFace principalWitnessOuterAddress .advecting
          (nonzeroModeHodgeReconstruction modeReceiverRebaseWitnessOutput
            modeReceiverRebaseWitnessPhaseCurl)
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode = -1 := by
  exact ⟨modeReceiverRebaseWitness_directH2Phase_eq_zero,
    modeReceiverRebaseWitnessPhaseCurl_ne_zero,
    modeReceiverRebaseWitness_outerAdvectingPhase_eq_neg_one⟩

section Audit

#print axioms complexVectorHermitianPairing_modeHermitianPhase_eq_zero
#print axioms derivativeWeighted_finiteProjectedSourceOwnModePhase_eq_zero
#print axioms nonzeroModeHodgeReconstruction_modeReceiverRebaseWitnessPhaseCurl
#print axioms modeReceiverRebaseWitness_direct_zero_outer_nonzero

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
