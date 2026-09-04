import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionProjection

/-!
# Curl-phase join for the clocked physical-H2 quartic pullback

**[proved-derived; formal-checked]** The clocked quartic pullback inserts a finite
Leray-projected velocity source into one of three outer triad legs.  The direction-depletion
receiver instead splits the curl of that source.  This owner gives the exact missing incidence.

At every nonzero output frequency, Hodge reconstruction transports the aligned and
receiver-orthogonal curl fibres back to the inserted velocity source.  At the zero output no
inverse is opened: divergence freedom of the advecting input kills the quadratic source atom
itself.  The two transported fibres then rejoin the original clocked quartic population over one
outer address and over every finite outer selector.

No norm, absolute value, source-only phase estimate, cofinal passage, terminal control, or
Navier--Stokes closure claim is made.  The outer insertion functional remains present, so the
derivative-weighted test occurrence is not collapsed.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

/-! ## The Hodge transport as a linear passage -/

/-- Hodge reconstruction at one frequency, bundled as the exact complex-linear passage used by
the phase split.  Totalization at zero is inherited from the standing reconstruction owner. -/
def nonzeroModeHodgeReconstructionLinearMap
    (frequency : SpatialFrequency) : ComplexVector →ₗ[ℂ] ComplexVector where
  toFun := nonzeroModeHodgeReconstruction frequency
  map_add' left right := by
    unfold nonzeroModeHodgeReconstruction
    change _ • complexCross (complexFrequencyVector frequency) (left + right) = _
    rw [show complexCross (complexFrequencyVector frequency) (left + right) =
        complexCross (complexFrequencyVector frequency) left +
          complexCross (complexFrequencyVector frequency) right by
      exact (crossProduct (complexFrequencyVector frequency)).map_add left right]
    exact smul_add _ _ _
  map_smul' scale source := by
    unfold nonzeroModeHodgeReconstruction
    change _ • complexCross (complexFrequencyVector frequency) (scale • source) = _
    rw [show complexCross (complexFrequencyVector frequency) (scale • source) =
        scale • complexCross (complexFrequencyVector frequency) source by
      exact (crossProduct (complexFrequencyVector frequency)).map_smul scale source]
    simp only [RingHom.id_apply, smul_smul]
    rw [mul_comm]

@[simp]
theorem nonzeroModeHodgeReconstructionLinearMap_apply
    (frequency : SpatialFrequency) (source : ComplexVector) :
    nonzeroModeHodgeReconstructionLinearMap frequency source =
      nonzeroModeHodgeReconstruction frequency source := rfl

/-- The totalized Hodge chart is identically zero at the zero output frequency. -/
@[simp]
theorem nonzeroModeHodgeReconstruction_zero_frequency
    (source : ComplexVector) :
    nonzeroModeHodgeReconstruction 0 source = 0 := by
  unfold nonzeroModeHodgeReconstruction
  have hcross : complexCross (complexFrequencyVector 0) source = 0 := by
    ext component
    fin_cases component <;>
      simp [complexCross, complexFrequencyVector, crossProduct]
  rw [hcross, smul_zero]

/-! ## The finite source atom and its exact zero fibre -/

/-- Curl of one retained finite projected source atom. -/
def finitePhysicalH2ProjectedSourceCurlAtom
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  frequencyCurlMultiplier output
    (finitePhysicalH2ProjectedSourceAtom velocityMode output alpha)

/-- Every projected source atom lies in the transverse fibre of its output frequency. -/
theorem finitePhysicalH2ProjectedSourceAtom_divergenceFree
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) :
    complexDot (complexFrequencyVector output)
        (finitePhysicalH2ProjectedSourceAtom velocityMode output alpha) = 0 := by
  unfold finitePhysicalH2ProjectedSourceAtom
  rw [complexDot, dotProduct_neg]
  change -complexDot (complexFrequencyVector output)
      (lerayProjectMode output
        (complexAdvectiveInteraction alpha (transportedFrequencyAt output alpha)
          (velocityMode alpha) (velocityMode (transportedFrequencyAt output alpha)))) = 0
  rw [complexDot_lerayProjectMode_eq_zero]
  simp

/-- The nonzero output chart reconstructs the inserted velocity-source atom exactly from its
curl. -/
theorem nonzeroModeHodgeReconstruction_projectedSourceCurlAtom
    (velocityMode : SpatialFrequency → ComplexVector)
    {output : SpatialFrequency} (houtput : output ≠ 0)
    (alpha : SpatialFrequency) :
    nonzeroModeHodgeReconstruction output
        (finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha) =
      finitePhysicalH2ProjectedSourceAtom velocityMode output alpha := by
  exact nonzeroModeHodgeReconstruction_frequencyCurlMultiplier houtput _
    (finitePhysicalH2ProjectedSourceAtom_divergenceFree velocityMode output alpha)

/-- Under the actual divergence-free mode condition, an inner interaction with zero output
vanishes before any Hodge inverse is requested. -/
theorem finitePhysicalH2ProjectedSourceAtom_zero_output
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0)
    (alpha : SpatialFrequency) :
    finitePhysicalH2ProjectedSourceAtom velocityMode 0 alpha = 0 := by
  have htransported : transportedFrequencyAt 0 alpha = -alpha := by
    funext component
    simp [transportedFrequencyAt]
  have hdot :
      complexDot (complexFrequencyVector (-alpha)) (velocityMode alpha) = 0 := by
    have hfrequency :
        complexFrequencyVector (-alpha) = -complexFrequencyVector alpha := by
      funext component
      simp [complexFrequencyVector]
    rw [hfrequency, complexDot, neg_dotProduct]
    change -complexDot (complexFrequencyVector alpha) (velocityMode alpha) = 0
    rw [hdivergence alpha]
    simp
  have hinteraction :
      complexAdvectiveInteraction alpha (-alpha)
          (velocityMode alpha) (velocityMode (-alpha)) = 0 := by
    unfold complexAdvectiveInteraction
    rw [hdot]
    simp
  unfold finitePhysicalH2ProjectedSourceAtom
  rw [htransported]
  rw [hinteraction]
  simp

/-! ## Curl polar fibres and their Hodge lifts -/

/-- Receiver-orthogonal fibre of one finite projected source curl. -/
def finitePhysicalH2ProjectedSourceCurlPhaseAtom
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  receiverDirectionRemainder receiver
    (finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha)

/-- Receiver-aligned fibre of the same source curl. -/
def finitePhysicalH2ProjectedSourceCurlAlignedAtom
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  receiverAlignedAmplitude receiver
      (finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha) • receiver

/-- The two curl fibres retain the complete finite source curl, including the zero-receiver
chart. -/
theorem finitePhysicalH2ProjectedSourceCurlPhase_add_aligned
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) :
    finitePhysicalH2ProjectedSourceCurlPhaseAtom receiver velocityMode output alpha +
        finitePhysicalH2ProjectedSourceCurlAlignedAtom receiver velocityMode output alpha =
      finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha := by
  exact receiverDirectionRemainder_add_aligned receiver
    (finitePhysicalH2ProjectedSourceCurlAtom velocityMode output alpha)

/-- Hodge-lifted receiver-orthogonal velocity-source fibre. -/
def finitePhysicalH2ProjectedSourceHodgePhaseAtom
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  nonzeroModeHodgeReconstructionLinearMap output
    (finitePhysicalH2ProjectedSourceCurlPhaseAtom receiver velocityMode output alpha)

/-- Hodge-lifted receiver-aligned velocity-source fibre. -/
def finitePhysicalH2ProjectedSourceHodgeAlignedAtom
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  nonzeroModeHodgeReconstructionLinearMap output
    (finitePhysicalH2ProjectedSourceCurlAlignedAtom receiver velocityMode output alpha)

/-- For every nonzero output, the Hodge-lifted phase and aligned fibres rejoin the exact inserted
velocity-source atom. -/
theorem finitePhysicalH2ProjectedSourceHodgePhase_add_aligned_of_ne_zero
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    {output : SpatialFrequency} (houtput : output ≠ 0)
    (alpha : SpatialFrequency) :
    finitePhysicalH2ProjectedSourceHodgePhaseAtom receiver velocityMode output alpha +
        finitePhysicalH2ProjectedSourceHodgeAlignedAtom receiver velocityMode output alpha =
      finitePhysicalH2ProjectedSourceAtom velocityMode output alpha := by
  change
    nonzeroModeHodgeReconstructionLinearMap output
          (finitePhysicalH2ProjectedSourceCurlPhaseAtom receiver velocityMode output alpha) +
        nonzeroModeHodgeReconstructionLinearMap output
          (finitePhysicalH2ProjectedSourceCurlAlignedAtom receiver velocityMode output alpha) = _
  rw [← map_add,
    finitePhysicalH2ProjectedSourceCurlPhase_add_aligned receiver velocityMode output alpha]
  exact nonzeroModeHodgeReconstruction_projectedSourceCurlAtom velocityMode houtput alpha

/-- The total chart reattaches the zero-output fibre without opening a singular inverse. -/
theorem finitePhysicalH2ProjectedSourceHodgePhase_add_aligned
    (receiver : ComplexVector)
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0)
    (output alpha : SpatialFrequency) :
    finitePhysicalH2ProjectedSourceHodgePhaseAtom receiver velocityMode output alpha +
        finitePhysicalH2ProjectedSourceHodgeAlignedAtom receiver velocityMode output alpha =
      finitePhysicalH2ProjectedSourceAtom velocityMode output alpha := by
  by_cases houtput : output = 0
  · subst output
    rw [finitePhysicalH2ProjectedSourceAtom_zero_output velocityMode hdivergence alpha]
    simp [finitePhysicalH2ProjectedSourceHodgePhaseAtom,
      finitePhysicalH2ProjectedSourceHodgeAlignedAtom,
      nonzeroModeHodgeReconstructionLinearMap]
  · exact finitePhysicalH2ProjectedSourceHodgePhase_add_aligned_of_ne_zero
      receiver velocityMode houtput alpha

/-! ## Exact rejoin through the derivative-weighted outer test -/

/-- Clocked quartic contribution carried by the receiver-orthogonal curl fibre of one inner
source occurrence. -/
def clockedPhysicalH2QuarticCurlPhaseOccurrence
    (receiver : ComplexVector) (nu : ℝ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (alpha : SpatialFrequency) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
      (finitePhysicalH2ProjectedSourceHodgePhaseAtom receiver velocityMode
        (physicalH2InsertionFrequency address leg) alpha)

/-- Clocked companion contribution carried by the receiver-aligned curl fibre. -/
def clockedPhysicalH2QuarticCurlAlignedOccurrence
    (receiver : ComplexVector) (nu : ℝ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (alpha : SpatialFrequency) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
      (finitePhysicalH2ProjectedSourceHodgeAlignedAtom receiver velocityMode
        (physicalH2InsertionFrequency address leg) alpha)

/-- The outer insertion functional sees the two Hodge-lifted curl fibres as one exact source
occurrence.  This is the derivative-weighted test incidence absent from a source-polar-only
receiver. -/
theorem clockedPhysicalH2QuarticCurlPhase_add_aligned
    (receiver : ComplexVector) (nu : ℝ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (alpha : SpatialFrequency) :
    clockedPhysicalH2QuarticCurlPhaseOccurrence receiver nu velocityMode address leg alpha +
        clockedPhysicalH2QuarticCurlAlignedOccurrence receiver nu velocityMode address leg alpha =
      physicalH2TriadReciprocalClock nu address *
        physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
          (finitePhysicalH2ProjectedSourceAtom velocityMode
            (physicalH2InsertionFrequency address leg) alpha) := by
  unfold clockedPhysicalH2QuarticCurlPhaseOccurrence
    clockedPhysicalH2QuarticCurlAlignedOccurrence
  rw [← mul_add]
  change physicalH2TriadReciprocalClock nu address *
      (physicalH2VelocityExchangedInsertionLegLinearMap velocityMode address leg
          (finitePhysicalH2ProjectedSourceHodgePhaseAtom receiver velocityMode
            (physicalH2InsertionFrequency address leg) alpha) +
        physicalH2VelocityExchangedInsertionLegLinearMap velocityMode address leg
          (finitePhysicalH2ProjectedSourceHodgeAlignedAtom receiver velocityMode
            (physicalH2InsertionFrequency address leg) alpha)) = _
  rw [← map_add,
    finitePhysicalH2ProjectedSourceHodgePhase_add_aligned receiver velocityMode hdivergence]
  rfl

/-- Phase part of the complete inner population over one outer address. -/
def finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  ∑ leg : PhysicalH2InsertionLeg,
    ∑ alpha ∈ pairCompatibleFrequencyAperture
        (physicalH2InsertionFrequency address leg) innerRadius,
      clockedPhysicalH2QuarticCurlPhaseOccurrence
        receiver nu velocityMode address leg alpha

/-- Aligned companion over the same retained occurrence population. -/
def finiteClockedPhysicalH2QuarticCurlAlignedOuterAddressFiber
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  ∑ leg : PhysicalH2InsertionLeg,
    ∑ alpha ∈ pairCompatibleFrequencyAperture
        (physicalH2InsertionFrequency address leg) innerRadius,
      clockedPhysicalH2QuarticCurlAlignedOccurrence
        receiver nu velocityMode address leg alpha

/-- Addresswise exact phase-plus-aligned rejoin. -/
theorem finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber_add_aligned
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0)
    (address : CompleteTransportAddress) :
    finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber
        receiver nu innerRadius velocityMode address +
      finiteClockedPhysicalH2QuarticCurlAlignedOuterAddressFiber
        receiver nu innerRadius velocityMode address =
      finiteClockedPhysicalH2QuarticOuterAddressFiber
        nu innerRadius velocityMode address := by
  classical
  unfold finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber
    finiteClockedPhysicalH2QuarticCurlAlignedOuterAddressFiber
    finiteClockedPhysicalH2QuarticOuterAddressFiber
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leg _hleg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  exact clockedPhysicalH2QuarticCurlPhase_add_aligned
    receiver nu velocityMode hdivergence address leg alpha

/-- Phase current over an arbitrary finite outer selector. -/
def finiteClockedPhysicalH2QuarticCurlPhasePullbackOn
    (selected : Finset CompleteTransportAddress)
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ selected,
    finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber
      receiver nu innerRadius velocityMode address

/-- Aligned current over the same arbitrary finite outer selector. -/
def finiteClockedPhysicalH2QuarticCurlAlignedPullbackOn
    (selected : Finset CompleteTransportAddress)
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ selected,
    finiteClockedPhysicalH2QuarticCurlAlignedOuterAddressFiber
      receiver nu innerRadius velocityMode address

/-- **Exact clocked quartic curl-phase join.**  Every finite outer selector preserves the source
curl's aligned and receiver-orthogonal fibres through Hodge reconstruction and the actual outer
insertion test, and their sum is the standing quartic pullback on that selector. -/
theorem finiteClockedPhysicalH2QuarticCurlPhasePullbackOn_add_aligned
    (selected : Finset CompleteTransportAddress)
    (receiver : ComplexVector) (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    finiteClockedPhysicalH2QuarticCurlPhasePullbackOn
        selected receiver nu innerRadius velocityMode +
      finiteClockedPhysicalH2QuarticCurlAlignedPullbackOn
        selected receiver nu innerRadius velocityMode =
      finiteClockedPhysicalH2QuarticInteractionPullbackOn
        selected nu innerRadius velocityMode := by
  classical
  unfold finiteClockedPhysicalH2QuarticCurlPhasePullbackOn
    finiteClockedPhysicalH2QuarticCurlAlignedPullbackOn
    finiteClockedPhysicalH2QuarticInteractionPullbackOn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro address _haddress
  exact finiteClockedPhysicalH2QuarticCurlPhaseOuterAddressFiber_add_aligned
    receiver nu innerRadius velocityMode hdivergence address

section Audit

#print axioms finitePhysicalH2ProjectedSourceAtom_divergenceFree
#print axioms finitePhysicalH2ProjectedSourceAtom_zero_output
#print axioms finitePhysicalH2ProjectedSourceHodgePhase_add_aligned
#print axioms clockedPhysicalH2QuarticCurlPhase_add_aligned
#print axioms finiteClockedPhysicalH2QuarticCurlPhasePullbackOn_add_aligned

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin
