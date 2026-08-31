import ElementaryHolonics.Millennium.NavierStokesPairCompatibleApertureConvergence
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization

/-!
# Clocked physical-H2 quartic interaction pullback

**[proved-derived; formal-checked]** This owner exposes the finite two-vertex Fourier population
carried by the reciprocal-clock source current before any norm or real-part receiver is applied.
An outer ordered address retains its literally closed three-pin triad.  One of its three distinct
mode occurrences is selected as the insertion leg.  At that leg an oriented inner address retains
`alpha`, `beta`, and the joining equality `alpha + beta = k_leg`; the corresponding advective
interaction is passed through the exact Leray receiver, multiplied by the outer exchanged `H2`
multiplier, and guarded by the total reciprocal three-pin clock.

The main theorem reconstructs the existing `physicalH2VelocityExchangedSourceInsertion` exactly
over the finite outer and inner apertures.  Ordered outer addresses, the three insertion legs, and
all inner advecting pins remain separate summation occurrences.  The zero-clock address remains in
the population and contributes zero by the standing guarded-reciprocal law.  No cofinal passage,
absolute-value estimate, terminal control, or Navier--Stokes closure claim is made.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Outer and inner addressed incidences -/

/-- The three mode occurrences of the outer closed triad.  They are an occurrence index, not a
quotient: summing over this type retains the three product-rule insertions separately. -/
inductive PhysicalH2InsertionLeg where
  | advecting
  | transported
  | receiver
  deriving DecidableEq

instance : Fintype PhysicalH2InsertionLeg where
  elems := {.advecting, .transported, .receiver}
  complete leg := by
    cases leg <;> simp

/-- The frequency carried by a selected outer insertion occurrence. -/
def physicalH2InsertionFrequency
    (address : CompleteTransportAddress) : PhysicalH2InsertionLeg → SpatialFrequency
  | .advecting => address.1
  | .transported => address.2
  | .receiver => completeTransportReceiver address

@[simp]
theorem physicalH2InsertionFrequency_advecting (address : CompleteTransportAddress) :
    physicalH2InsertionFrequency address .advecting = address.1 := rfl

@[simp]
theorem physicalH2InsertionFrequency_transported (address : CompleteTransportAddress) :
    physicalH2InsertionFrequency address .transported = address.2 := rfl

@[simp]
theorem physicalH2InsertionFrequency_receiver (address : CompleteTransportAddress) :
    physicalH2InsertionFrequency address .receiver = completeTransportReceiver address := rfl

/-- Exchange fixes the advecting occurrence and swaps the transported and receiving occurrences. -/
def PhysicalH2InsertionLeg.exchange : PhysicalH2InsertionLeg → PhysicalH2InsertionLeg
  | .advecting => .advecting
  | .transported => .receiver
  | .receiver => .transported

@[simp]
theorem PhysicalH2InsertionLeg.exchange_exchange (leg : PhysicalH2InsertionLeg) :
    leg.exchange.exchange = leg := by
  cases leg <;> rfl

/-- The exchanged outer address and exchanged leg still select the same physical frequency
occurrence. -/
@[simp]
theorem physicalH2InsertionFrequency_exchange
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    physicalH2InsertionFrequency (completeTransportExchange address) leg.exchange =
      physicalH2InsertionFrequency address leg := by
  cases leg <;> simp [PhysicalH2InsertionLeg.exchange]

/-- Cyclic rotation transports an old advecting occurrence to the new receiver, an old
transported occurrence to the new advecting pin, and an old receiver to the new transported pin. -/
def PhysicalH2InsertionLeg.rotate : PhysicalH2InsertionLeg → PhysicalH2InsertionLeg
  | .advecting => .receiver
  | .transported => .advecting
  | .receiver => .transported

/-- Select one of the three ordered frequencies of an arbitrary closed outer triad. -/
def addressedTriadInsertionFrequency
    (triad : AddressedClosedFourierTriad) : PhysicalH2InsertionLeg → SpatialFrequency
  | .advecting => triad.advecting
  | .transported => triad.transported
  | .receiver => triad.receiver

/-- Cyclic rotation preserves each physical outer occurrence while changing its role. -/
@[simp]
theorem addressedTriadInsertionFrequency_rotate
    (triad : AddressedClosedFourierTriad) (leg : PhysicalH2InsertionLeg) :
    addressedTriadInsertionFrequency triad.rotate leg.rotate =
      addressedTriadInsertionFrequency triad leg := by
  cases leg <;> rfl

/-- The complete outer address presents the same three frequencies as its closed-triad face. -/
@[simp]
theorem addressedTriadInsertionFrequency_completeTransportTriad
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    addressedTriadInsertionFrequency (completeTransportTriad address) leg =
      physicalH2InsertionFrequency address leg := by
  cases leg <;> rfl

/-- Reality reverses every oriented outer frequency while retaining the two ordered address
pins. -/
def physicalH2RealityAddress (address : CompleteTransportAddress) :
    CompleteTransportAddress :=
  (-address.1, -address.2)

@[simp]
theorem completeTransportReceiver_realityAddress (address : CompleteTransportAddress) :
    completeTransportReceiver (physicalH2RealityAddress address) =
      -completeTransportReceiver address := by
  funext component
  simp [physicalH2RealityAddress, completeTransportReceiver]
  ring

@[simp]
theorem physicalH2InsertionFrequency_reality
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    physicalH2InsertionFrequency (physicalH2RealityAddress address) leg =
      -physicalH2InsertionFrequency address leg := by
  cases leg with
  | advecting => simp [physicalH2RealityAddress]
  | transported => simp [physicalH2RealityAddress]
  | receiver => exact completeTransportReceiver_realityAddress address

/-- Membership in a coordinate cube is invariant under frequency reversal. -/
theorem neg_mem_frequencyCube_iff_local
    (frequency : SpatialFrequency) (radius : ℕ) :
    -frequency ∈ frequencyCube radius ↔ frequency ∈ frequencyCube radius := by
  rw [mem_frequencyCube_iff, mem_frequencyCube_iff]
  constructor
  · intro h component
    have hc := h component
    simp only [Pi.neg_apply] at hc
    omega
  · intro h component
    have hc := h component
    simp only [Pi.neg_apply]
    omega

/-- The complete finite outer cube retains the reality-reflected occurrence. -/
theorem physicalH2RealityAddress_mem_velocityTriadAperture_iff
    (outerRadius : ℕ) (address : CompleteTransportAddress) :
    physicalH2RealityAddress address ∈ physicalH2VelocityTriadAperture outerRadius ↔
      address ∈ physicalH2VelocityTriadAperture outerRadius := by
  rw [mem_physicalH2VelocityTriadAperture_iff,
    mem_physicalH2VelocityTriadAperture_iff]
  change
    -address.1 ∈ frequencyCube outerRadius ∧
        -address.2 ∈ frequencyCube outerRadius ∧
        completeTransportReceiver (physicalH2RealityAddress address) ∈
          frequencyCube outerRadius ↔
      address.1 ∈ frequencyCube outerRadius ∧
        address.2 ∈ frequencyCube outerRadius ∧
        completeTransportReceiver address ∈ frequencyCube outerRadius
  rw [completeTransportReceiver_realityAddress,
    neg_mem_frequencyCube_iff_local, neg_mem_frequencyCube_iff_local,
    neg_mem_frequencyCube_iff_local]

/-- An inner convolution address retains both oriented parents and their exact joining equality. -/
structure OrientedInnerConvolutionAddress (output : SpatialFrequency) where
  alpha : SpatialFrequency
  beta : SpatialFrequency
  joined : alpha + beta = output

/-- The actual inner address determined by its advecting pin `alpha`; its transported pin remains
visible as `output - alpha`. -/
def orientedInnerConvolutionAddress
    (output alpha : SpatialFrequency) : OrientedInnerConvolutionAddress output where
  alpha := alpha
  beta := transportedFrequencyAt output alpha
  joined := advecting_add_transportedFrequencyAt output alpha

@[simp]
theorem orientedInnerConvolutionAddress_alpha
    (output alpha : SpatialFrequency) :
    (orientedInnerConvolutionAddress output alpha).alpha = alpha := rfl

@[simp]
theorem orientedInnerConvolutionAddress_beta
    (output alpha : SpatialFrequency) :
    (orientedInnerConvolutionAddress output alpha).beta =
      transportedFrequencyAt output alpha := rfl

/-- Reality reverses both oriented inner parents and lands over the reversed output. -/
def OrientedInnerConvolutionAddress.reality
    {output : SpatialFrequency} (inner : OrientedInnerConvolutionAddress output) :
    OrientedInnerConvolutionAddress (-output) where
  alpha := -inner.alpha
  beta := -inner.beta
  joined := by
    rw [← neg_add, inner.joined]

/-- One finite pullback occurrence.  Proof fields retain membership in both apertures; no address
is reconstructed from a quotient or from a terminal receiver value. -/
structure FiniteClockedPhysicalH2QuarticOccurrence
    (outerRadius innerRadius : ℕ) where
  outerAddress : CompleteTransportAddress
  outer_mem : outerAddress ∈ physicalH2VelocityTriadAperture outerRadius
  insertionLeg : PhysicalH2InsertionLeg
  innerAlpha : SpatialFrequency
  inner_mem : innerAlpha ∈ pairCompatibleFrequencyAperture
    (physicalH2InsertionFrequency outerAddress insertionLeg) innerRadius

/-- The literal outer closed triad carried by an occurrence. -/
def FiniteClockedPhysicalH2QuarticOccurrence.outerTriad
    {outerRadius innerRadius : ℕ}
    (occurrence : FiniteClockedPhysicalH2QuarticOccurrence outerRadius innerRadius) :
    AddressedClosedFourierTriad :=
  completeTransportTriad occurrence.outerAddress

/-- The literal oriented inner address carried by an occurrence. -/
def FiniteClockedPhysicalH2QuarticOccurrence.innerAddress
    {outerRadius innerRadius : ℕ}
    (occurrence : FiniteClockedPhysicalH2QuarticOccurrence outerRadius innerRadius) :
    OrientedInnerConvolutionAddress
      (physicalH2InsertionFrequency occurrence.outerAddress occurrence.insertionLeg) :=
  orientedInnerConvolutionAddress
    (physicalH2InsertionFrequency occurrence.outerAddress occurrence.insertionLeg)
    occurrence.innerAlpha

/-- The three insertion occurrences have exact multiplicity three. -/
theorem physicalH2InsertionLeg_card : Fintype.card PhysicalH2InsertionLeg = 3 := by
  decide

/-! ## The two local vertices -/

/-- One oriented inner quadratic interaction after the signed Leray insertion passage. -/
def finitePhysicalH2ProjectedSourceAtom
    (velocityMode : SpatialFrequency → ComplexVector)
    (output alpha : SpatialFrequency) : ComplexVector :=
  -lerayProjectMode output
    (complexAdvectiveInteraction alpha (transportedFrequencyAt output alpha)
      (velocityMode alpha) (velocityMode (transportedFrequencyAt output alpha)))

/-- The finite source mode obtained by summing the complete oriented inner occurrence population
at one output frequency. -/
def finitePhysicalH2ProjectedSourceMode
    (innerRadius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (output : SpatialFrequency) : ComplexVector :=
  ∑ alpha ∈ pairCompatibleFrequencyAperture output innerRadius,
    finitePhysicalH2ProjectedSourceAtom velocityMode output alpha

/-- The inner pullback is exactly the signed Leray projection of the existing finite advective
coefficient. -/
theorem finitePhysicalH2ProjectedSourceMode_eq_neg_leray_finiteAdvectiveCoefficient
    (innerRadius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (output : SpatialFrequency) :
    finitePhysicalH2ProjectedSourceMode innerRadius velocityMode output =
      -lerayProjectMode output
        (finiteAdvectiveCoefficient
          (pairCompatibleFrequencyAperture output innerRadius)
          velocityMode velocityMode output) := by
  classical
  unfold finitePhysicalH2ProjectedSourceMode finitePhysicalH2ProjectedSourceAtom
    finiteAdvectiveCoefficient
  change
    (∑ alpha ∈ pairCompatibleFrequencyAperture output innerRadius,
      -(lerayProjectModeLinearMap output)
        (complexAdvectiveInteraction alpha (transportedFrequencyAt output alpha)
          (velocityMode alpha) (velocityMode (transportedFrequencyAt output alpha)))) =
      -(lerayProjectModeLinearMap output)
        (∑ alpha ∈ pairCompatibleFrequencyAperture output innerRadius,
          complexAdvectiveInteraction alpha (transportedFrequencyAt output alpha)
            (velocityMode alpha) (velocityMode (transportedFrequencyAt output alpha)))
  rw [map_sum]
  simp only [Finset.sum_neg_distrib]

/-- Insert one vector at one selected outer leg and apply the completed exchanged `H2`
multiplier. -/
def physicalH2VelocityExchangedInsertionLegFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    PhysicalH2InsertionLeg → ComplexVector → ℂ
  | .advecting, inserted =>
      physicalH2ExchangedTriadMultiplier address *
        triadicEnergyFace address.1 address.2 inserted
          (velocityMode address.2)
          (velocityMode (completeTransportReceiver address))
  | .transported, inserted =>
      physicalH2ExchangedTriadMultiplier address *
        triadicEnergyFace address.1 address.2
          (velocityMode address.1) inserted
          (velocityMode (completeTransportReceiver address))
  | .receiver, inserted =>
      physicalH2ExchangedTriadMultiplier address *
        triadicEnergyFace address.1 address.2
          (velocityMode address.1) (velocityMode address.2) inserted

/-- Complex-linearity of one selected outer insertion leg. -/
def physicalH2VelocityExchangedInsertionLegLinearMap
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    ComplexVector →ₗ[ℂ] ℂ where
  toFun := physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
  map_add' left right := by
    cases leg with
    | advecting =>
        have hinteraction :
            complexAdvectiveInteraction address.1 address.2 (left + right)
                (velocityMode address.2) =
              complexAdvectiveInteraction address.1 address.2 left
                  (velocityMode address.2) +
                complexAdvectiveInteraction address.1 address.2 right
                  (velocityMode address.2) := by
          have hmap := congrArg
            (fun operator : ComplexVector →L[ℂ] ComplexVector =>
              operator (velocityMode address.2))
            ((complexAdvectiveInteractionBilinearLinearMap address.1 address.2).map_add
              left right)
          change
            complexAdvectiveInteraction address.1 address.2 (left + right)
                (velocityMode address.2) =
              complexAdvectiveInteraction address.1 address.2 left
                  (velocityMode address.2) +
                complexAdvectiveInteraction address.1 address.2 right
                  (velocityMode address.2) at hmap
          exact hmap
        have hdot :
            complexDot
                (complexAdvectiveInteraction address.1 address.2 left
                    (velocityMode address.2) +
                  complexAdvectiveInteraction address.1 address.2 right
                    (velocityMode address.2))
                (velocityMode (completeTransportReceiver address)) =
              complexDot
                  (complexAdvectiveInteraction address.1 address.2 left
                    (velocityMode address.2))
                  (velocityMode (completeTransportReceiver address)) +
                complexDot
                  (complexAdvectiveInteraction address.1 address.2 right
                    (velocityMode address.2))
                  (velocityMode (completeTransportReceiver address)) := by
          have hmap := congrArg
            (fun receiver : ComplexVector →L[ℂ] ℂ =>
              receiver (velocityMode (completeTransportReceiver address)))
            (complexDotBilinearLinearMap.map_add
              (complexAdvectiveInteraction address.1 address.2 left
                (velocityMode address.2))
              (complexAdvectiveInteraction address.1 address.2 right
                (velocityMode address.2)))
          change
            complexDot
                (complexAdvectiveInteraction address.1 address.2 left
                    (velocityMode address.2) +
                  complexAdvectiveInteraction address.1 address.2 right
                    (velocityMode address.2))
                (velocityMode (completeTransportReceiver address)) =
              complexDot
                  (complexAdvectiveInteraction address.1 address.2 left
                    (velocityMode address.2))
                  (velocityMode (completeTransportReceiver address)) +
                complexDot
                  (complexAdvectiveInteraction address.1 address.2 right
                    (velocityMode address.2))
                  (velocityMode (completeTransportReceiver address)) at hmap
          exact hmap
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hinteraction, hdot]
        ring
    | transported =>
        have hinteraction :
            complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) (left + right) =
              complexAdvectiveInteraction address.1 address.2
                  (velocityMode address.1) left +
                complexAdvectiveInteraction address.1 address.2
                  (velocityMode address.1) right := by
          exact (complexAdvectiveInteractionRightLinearMap
            address.1 address.2 (velocityMode address.1)).map_add left right
        have hdot :
            complexDot
                (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) left +
                  complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) right)
                (velocityMode (completeTransportReceiver address)) =
              complexDot
                  (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) left)
                  (velocityMode (completeTransportReceiver address)) +
                complexDot
                  (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) right)
                  (velocityMode (completeTransportReceiver address)) := by
          have hmap := congrArg
            (fun receiver : ComplexVector →L[ℂ] ℂ =>
              receiver (velocityMode (completeTransportReceiver address)))
            (complexDotBilinearLinearMap.map_add
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) left)
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) right))
          change
            complexDot
                (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) left +
                  complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) right)
                (velocityMode (completeTransportReceiver address)) =
              complexDot
                  (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) left)
                  (velocityMode (completeTransportReceiver address)) +
                complexDot
                  (complexAdvectiveInteraction address.1 address.2
                    (velocityMode address.1) right)
                  (velocityMode (completeTransportReceiver address)) at hmap
          exact hmap
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hinteraction, hdot]
        ring
    | receiver =>
        have hdot := (complexDotRightLinearMap
          (complexAdvectiveInteraction address.1 address.2
            (velocityMode address.1) (velocityMode address.2))).map_add left right
        change
          complexDot
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) (velocityMode address.2)) (left + right) =
            complexDot
                (complexAdvectiveInteraction address.1 address.2
                  (velocityMode address.1) (velocityMode address.2)) left +
              complexDot
                (complexAdvectiveInteraction address.1 address.2
                  (velocityMode address.1) (velocityMode address.2)) right at hdot
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hdot]
        ring
  map_smul' scale inserted := by
    cases leg with
    | advecting =>
        have hinteraction :
            complexAdvectiveInteraction address.1 address.2 (scale • inserted)
                (velocityMode address.2) =
              scale • complexAdvectiveInteraction address.1 address.2 inserted
                (velocityMode address.2) := by
          have hmap := congrArg
            (fun operator : ComplexVector →L[ℂ] ComplexVector =>
              operator (velocityMode address.2))
            ((complexAdvectiveInteractionBilinearLinearMap address.1 address.2).map_smul
              scale inserted)
          change
            complexAdvectiveInteraction address.1 address.2 (scale • inserted)
                (velocityMode address.2) =
              scale • complexAdvectiveInteraction address.1 address.2 inserted
                (velocityMode address.2) at hmap
          exact hmap
        have hdot := complexDotBilinearLinearMap.map_smul scale
          (complexAdvectiveInteraction address.1 address.2 inserted
            (velocityMode address.2))
        have hdot' := congrArg
          (fun receiver : ComplexVector →L[ℂ] ℂ =>
            receiver (velocityMode (completeTransportReceiver address))) hdot
        change
          complexDot
              (scale • complexAdvectiveInteraction address.1 address.2 inserted
                (velocityMode address.2))
              (velocityMode (completeTransportReceiver address)) =
            scale • complexDot
              (complexAdvectiveInteraction address.1 address.2 inserted
                (velocityMode address.2))
              (velocityMode (completeTransportReceiver address)) at hdot'
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hinteraction, hdot']
        simp only [RingHom.id_apply, smul_eq_mul]
        ring
    | transported =>
        have hinteraction := (complexAdvectiveInteractionRightLinearMap
          address.1 address.2 (velocityMode address.1)).map_smul scale inserted
        change
          complexAdvectiveInteraction address.1 address.2
              (velocityMode address.1) (scale • inserted) =
            scale • complexAdvectiveInteraction address.1 address.2
              (velocityMode address.1) inserted at hinteraction
        have hdot := complexDotBilinearLinearMap.map_smul scale
          (complexAdvectiveInteraction address.1 address.2
            (velocityMode address.1) inserted)
        have hdot' := congrArg
          (fun receiver : ComplexVector →L[ℂ] ℂ =>
            receiver (velocityMode (completeTransportReceiver address))) hdot
        change
          complexDot
              (scale • complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) inserted)
              (velocityMode (completeTransportReceiver address)) =
            scale • complexDot
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) inserted)
              (velocityMode (completeTransportReceiver address)) at hdot'
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hinteraction, hdot']
        simp only [RingHom.id_apply, smul_eq_mul]
        ring
    | receiver =>
        have hdot := (complexDotRightLinearMap
          (complexAdvectiveInteraction address.1 address.2
            (velocityMode address.1) (velocityMode address.2))).map_smul scale inserted
        change
          complexDot
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) (velocityMode address.2)) (scale • inserted) =
            scale • complexDot
              (complexAdvectiveInteraction address.1 address.2
                (velocityMode address.1) (velocityMode address.2)) inserted at hdot
        simp only [physicalH2VelocityExchangedInsertionLegFace, triadicEnergyFace]
        rw [hdot]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring

@[simp]
theorem physicalH2VelocityExchangedInsertionLegLinearMap_apply
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector) :
    physicalH2VelocityExchangedInsertionLegLinearMap velocityMode address leg inserted =
      physicalH2VelocityExchangedInsertionLegFace velocityMode address leg inserted := rfl

/-- The three indexed outer leg faces reconstruct the standing source-insertion owner exactly. -/
theorem sum_physicalH2VelocityExchangedInsertionLegFace_eq_sourceInsertion
    (velocityMode sourceMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    (∑ leg : PhysicalH2InsertionLeg,
      physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
        (sourceMode (physicalH2InsertionFrequency address leg))) =
      physicalH2VelocityExchangedSourceInsertion velocityMode sourceMode address := by
  classical
  rw [show (Finset.univ : Finset PhysicalH2InsertionLeg) =
      {.advecting, .transported, .receiver} by decide]
  simp [physicalH2VelocityExchangedInsertionLegFace,
    physicalH2VelocityExchangedSourceInsertion]
  ring

/-- Linearity at each selected outer leg preserves every inner occurrence until the sum rejoins
the finite source mode. -/
theorem sum_physicalH2VelocityExchangedInsertionLegFace
    {ι : Type*} (population : Finset ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ι → ComplexVector) :
    (∑ index ∈ population,
      physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
        (inserted index)) =
      physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
        (∑ index ∈ population, inserted index) := by
  classical
  change
    (∑ index ∈ population,
      physicalH2VelocityExchangedInsertionLegLinearMap velocityMode address leg
        (inserted index)) =
      physicalH2VelocityExchangedInsertionLegLinearMap velocityMode address leg
        (∑ index ∈ population, inserted index)
  rw [map_sum]

/-! ## The finite clocked pullback and its exact rejoin -/

/-- The complete quartic fibre over one retained outer address.  This is the theorem-friendly
projection for later shell/grade selectors: filtering outer addresses never collapses the three
leg or inner-address populations inside the selected fibre. -/
def finiteClockedPhysicalH2QuarticOuterAddressFiber
    (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  ∑ leg : PhysicalH2InsertionLeg,
    ∑ alpha ∈ pairCompatibleFrequencyAperture
        (physicalH2InsertionFrequency address leg) innerRadius,
      physicalH2TriadReciprocalClock nu address *
        physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
          (finitePhysicalH2ProjectedSourceAtom velocityMode
            (physicalH2InsertionFrequency address leg) alpha)

/-- The exact finite two-vertex population.  The nested sums are the outer ordered address, the
three distinct insertion legs, and the oriented inner advecting pin.  The transported inner pin is
retained by `transportedFrequencyAt`, and its joining equality is
`advecting_add_transportedFrequencyAt`. -/
def finiteClockedPhysicalH2QuarticInteractionPullback
    (nu : ℝ) (outerRadius innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture outerRadius,
    finiteClockedPhysicalH2QuarticOuterAddressFiber
      nu innerRadius velocityMode address

/-- An arbitrary finite outer-address selector.  A later high-grade predicate can instantiate
`selected` without changing the exact local fibre or the main rejoin theorem. -/
def finiteClockedPhysicalH2QuarticInteractionPullbackOn
    (selected : Finset CompleteTransportAddress)
    (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ selected,
    finiteClockedPhysicalH2QuarticOuterAddressFiber
      nu innerRadius velocityMode address

theorem finiteClockedPhysicalH2QuarticInteractionPullback_eq_on_outerAperture
    (nu : ℝ) (outerRadius innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteClockedPhysicalH2QuarticInteractionPullback
        nu outerRadius innerRadius velocityMode =
      finiteClockedPhysicalH2QuarticInteractionPullbackOn
        (physicalH2VelocityTriadAperture outerRadius)
        nu innerRadius velocityMode := rfl

/-- The same finite population after its inner pullback and cyclic insertion-leg fibres have
rejoined the standing source-insertion owner. -/
def finiteClockedPhysicalH2SourceInsertionCurrent
    (nu : ℝ) (outerRadius innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture outerRadius,
    physicalH2TriadReciprocalClock nu address *
      physicalH2VelocityExchangedSourceInsertion velocityMode
        (finitePhysicalH2ProjectedSourceMode innerRadius velocityMode) address

/-- Addresswise rejoin.  This preserves the outer address as a selector key for later shell or
grade tails. -/
theorem finiteClockedPhysicalH2QuarticOuterAddressFiber_eq_sourceInsertion
    (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    finiteClockedPhysicalH2QuarticOuterAddressFiber
        nu innerRadius velocityMode address =
      physicalH2TriadReciprocalClock nu address *
        physicalH2VelocityExchangedSourceInsertion velocityMode
          (finitePhysicalH2ProjectedSourceMode innerRadius velocityMode) address := by
  classical
  unfold finiteClockedPhysicalH2QuarticOuterAddressFiber
  rw [← sum_physicalH2VelocityExchangedInsertionLegFace_eq_sourceInsertion]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leg _hleg
  rw [← Finset.mul_sum]
  rw [sum_physicalH2VelocityExchangedInsertionLegFace]
  rfl

/-- Every finite outer selector enjoys the same exact rejoin, independently of how that selector
is later presented as a cube, shell, or grade predicate. -/
theorem finiteClockedPhysicalH2QuarticInteractionPullbackOn_eq_sourceInsertion
    (selected : Finset CompleteTransportAddress)
    (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteClockedPhysicalH2QuarticInteractionPullbackOn
        selected nu innerRadius velocityMode =
      ∑ address ∈ selected,
        physicalH2TriadReciprocalClock nu address *
          physicalH2VelocityExchangedSourceInsertion velocityMode
            (finitePhysicalH2ProjectedSourceMode innerRadius velocityMode) address := by
  unfold finiteClockedPhysicalH2QuarticInteractionPullbackOn
  apply Finset.sum_congr rfl
  intro address _haddress
  exact finiteClockedPhysicalH2QuarticOuterAddressFiber_eq_sourceInsertion
    nu innerRadius velocityMode address

/-- **Exact finite clocked physical-H2 quartic pullback.**  The oriented two-vertex occurrence
population is definitionally finite and rejoins the existing exchanged source insertion without
discarding the zero clock, taking absolute values, or identifying exchanged/reality/cyclic
occurrences. -/
theorem finiteClockedPhysicalH2QuarticInteractionPullback_eq_sourceInsertion
    (nu : ℝ) (outerRadius innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteClockedPhysicalH2QuarticInteractionPullback
        nu outerRadius innerRadius velocityMode =
      finiteClockedPhysicalH2SourceInsertionCurrent
        nu outerRadius innerRadius velocityMode := by
  classical
  unfold finiteClockedPhysicalH2QuarticInteractionPullback
    finiteClockedPhysicalH2SourceInsertionCurrent
  apply Finset.sum_congr rfl
  intro address _haddress
  exact finiteClockedPhysicalH2QuarticOuterAddressFiber_eq_sourceInsertion
    nu innerRadius velocityMode address

/-- The guarded reciprocal retains the unique clock-zero address as a zero quartic fibre. -/
@[simp]
theorem finiteClockedPhysicalH2QuarticInteractionPullback_zero_outerAddress
    (nu : ℝ) (innerRadius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteClockedPhysicalH2QuarticOuterAddressFiber
      nu innerRadius velocityMode (0, 0) = 0 := by
  simp [finiteClockedPhysicalH2QuarticOuterAddressFiber]

section Audit

#print axioms physicalH2InsertionFrequency_exchange
#print axioms addressedTriadInsertionFrequency_rotate
#print axioms physicalH2RealityAddress_mem_velocityTriadAperture_iff
#print axioms finitePhysicalH2ProjectedSourceMode_eq_neg_leray_finiteAdvectiveCoefficient
#print axioms sum_physicalH2VelocityExchangedInsertionLegFace_eq_sourceInsertion
#print axioms finiteClockedPhysicalH2QuarticOuterAddressFiber_eq_sourceInsertion
#print axioms finiteClockedPhysicalH2QuarticInteractionPullback_eq_sourceInsertion

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
