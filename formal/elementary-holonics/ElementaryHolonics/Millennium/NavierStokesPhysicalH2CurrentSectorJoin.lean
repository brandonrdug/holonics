import ElementaryHolonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition

/-!
# Exact dyadic-sector join of the complete physical H2 current

**[proved-derived; formal-checked]** The complete real exchanged-transport and weighted-
stretching populations are retained through their exact closed-triad address charts and split
into the three unique-minimum dyadic-grade sectors and the comparable remainder. Existing
absolute summability carries the signed `tsum` partition before any norm receiver.

The complex exchanged transport face is invariant under exchanging its transported and receiving
pins: both the Stokes multiplier difference and the oriented triadic face reverse sign. Exact
reindexing therefore identifies the transported-low and receiver-low real sector currents. The
literal physical `H2` current consequently has exact eight-sector and seven-term presentations.
No estimate, absorption, or continuation statement is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentSectorJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Exchanged-transport sector currents -/

def completePhysicalH2AdvectingLowExchangedTransportCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // AdvectingLowSector triad},
    (completePhysicalH2ExchangedTransportFace solution t
      (completeTransportAddressEquivTriad.symm sector.1)).re

def completePhysicalH2TransportedLowExchangedTransportCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // TransportedLowSector triad},
    (completePhysicalH2ExchangedTransportFace solution t
      (completeTransportAddressEquivTriad.symm sector.1)).re

def completePhysicalH2ReceiverLowExchangedTransportCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // ReceiverLowSector triad},
    (completePhysicalH2ExchangedTransportFace solution t
      (completeTransportAddressEquivTriad.symm sector.1)).re

def completePhysicalH2ComparableExchangedTransportCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // ComparableSector triad},
    (completePhysicalH2ExchangedTransportFace solution t
      (completeTransportAddressEquivTriad.symm sector.1)).re

/-! ## Weighted-stretching sector currents -/

def completePhysicalH2AdvectingLowWeightedStretchingCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // AdvectingLowSector triad},
    let address := completeStretchingAddressEquivTriad.symm sector.1
    (1 + torusStokesEigenvalue address.1) *
      (completeOpenVorticityStretchingFace solution t address).re

def completePhysicalH2TransportedLowWeightedStretchingCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // TransportedLowSector triad},
    let address := completeStretchingAddressEquivTriad.symm sector.1
    (1 + torusStokesEigenvalue address.1) *
      (completeOpenVorticityStretchingFace solution t address).re

def completePhysicalH2ReceiverLowWeightedStretchingCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // ReceiverLowSector triad},
    let address := completeStretchingAddressEquivTriad.symm sector.1
    (1 + torusStokesEigenvalue address.1) *
      (completeOpenVorticityStretchingFace solution t address).re

def completePhysicalH2ComparableWeightedStretchingCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' sector : {triad // ComparableSector triad},
    let address := completeStretchingAddressEquivTriad.symm sector.1
    (1 + torusStokesEigenvalue address.1) *
      (completeOpenVorticityStretchingFace solution t address).re

/-! ## Real signed partitions from the exact complex proof chart -/

private theorem real_tsum_completeTransportAddress_eq_fourSectors
    (face : CompleteTransportAddress → ℝ) (hface : Summable face) :
    (∑' address : CompleteTransportAddress, face address) =
      (∑' sector : {triad // AdvectingLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // TransportedLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // ReceiverLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      ∑' sector : {triad // ComparableSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1) := by
  let complexFace : CompleteTransportAddress → ℂ :=
    fun address ↦ (face address : ℂ)
  have hcomplexFace : Summable complexFace :=
    Complex.ofRealCLM.summable hface
  have hpartition := tsum_completeTransportAddress_eq_fourSectors
    complexFace hcomplexFace
  have hadvecting : Summable
      (fun sector : {triad // AdvectingLowSector triad} ↦
        face (completeTransportAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeTransportAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have htransported : Summable
      (fun sector : {triad // TransportedLowSector triad} ↦
        face (completeTransportAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeTransportAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have hreceiver : Summable
      (fun sector : {triad // ReceiverLowSector triad} ↦
        face (completeTransportAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeTransportAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have hcomparable : Summable
      (fun sector : {triad // ComparableSector triad} ↦
        face (completeTransportAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeTransportAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  apply Complex.ofReal_injective
  change Complex.ofRealCLM (∑' address : CompleteTransportAddress, face address) =
    Complex.ofRealCLM
      ((∑' sector : {triad // AdvectingLowSector triad},
          face (completeTransportAddressEquivTriad.symm sector.1)) +
        (∑' sector : {triad // TransportedLowSector triad},
          face (completeTransportAddressEquivTriad.symm sector.1)) +
        (∑' sector : {triad // ReceiverLowSector triad},
          face (completeTransportAddressEquivTriad.symm sector.1)) +
        ∑' sector : {triad // ComparableSector triad},
          face (completeTransportAddressEquivTriad.symm sector.1))
  simp only [map_add]
  rw [Complex.ofRealCLM.map_tsum hface,
    Complex.ofRealCLM.map_tsum hadvecting,
    Complex.ofRealCLM.map_tsum htransported,
    Complex.ofRealCLM.map_tsum hreceiver,
    Complex.ofRealCLM.map_tsum hcomparable]
  simpa only [complexFace, Complex.ofRealCLM_apply, map_add] using hpartition

private theorem real_tsum_completeStretchingAddress_eq_fourSectors
    (face : CompleteStretchingAddress → ℝ) (hface : Summable face) :
    (∑' address : CompleteStretchingAddress, face address) =
      (∑' sector : {triad // AdvectingLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // TransportedLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // ReceiverLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      ∑' sector : {triad // ComparableSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1) := by
  let complexFace : CompleteStretchingAddress → ℂ :=
    fun address ↦ (face address : ℂ)
  have hcomplexFace : Summable complexFace :=
    Complex.ofRealCLM.summable hface
  have hpartition := tsum_completeStretchingAddress_eq_fourSectors
    complexFace hcomplexFace
  have hadvecting : Summable
      (fun sector : {triad // AdvectingLowSector triad} ↦
        face (completeStretchingAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeStretchingAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have htransported : Summable
      (fun sector : {triad // TransportedLowSector triad} ↦
        face (completeStretchingAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeStretchingAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have hreceiver : Summable
      (fun sector : {triad // ReceiverLowSector triad} ↦
        face (completeStretchingAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeStretchingAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  have hcomparable : Summable
      (fun sector : {triad // ComparableSector triad} ↦
        face (completeStretchingAddressEquivTriad.symm sector.1)) :=
    hface.comp_injective
      (completeStretchingAddressEquivTriad.symm.injective.comp Subtype.val_injective)
  apply Complex.ofReal_injective
  change Complex.ofRealCLM (∑' address : CompleteStretchingAddress, face address) =
    Complex.ofRealCLM
      ((∑' sector : {triad // AdvectingLowSector triad},
          face (completeStretchingAddressEquivTriad.symm sector.1)) +
        (∑' sector : {triad // TransportedLowSector triad},
          face (completeStretchingAddressEquivTriad.symm sector.1)) +
        (∑' sector : {triad // ReceiverLowSector triad},
          face (completeStretchingAddressEquivTriad.symm sector.1)) +
        ∑' sector : {triad // ComparableSector triad},
          face (completeStretchingAddressEquivTriad.symm sector.1))
  simp only [map_add]
  rw [Complex.ofRealCLM.map_tsum hface,
    Complex.ofRealCLM.map_tsum hadvecting,
    Complex.ofRealCLM.map_tsum htransported,
    Complex.ofRealCLM.map_tsum hreceiver,
    Complex.ofRealCLM.map_tsum hcomparable]
  simpa only [complexFace, Complex.ofRealCLM_apply, map_add] using hpartition

theorem completePhysicalH2ExchangedTransportCurrent_eq_fourSectors
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2ExchangedTransportCurrent solution t =
      completePhysicalH2AdvectingLowExchangedTransportCurrent solution t +
      completePhysicalH2TransportedLowExchangedTransportCurrent solution t +
      completePhysicalH2ReceiverLowExchangedTransportCurrent solution t +
      completePhysicalH2ComparableExchangedTransportCurrent solution t := by
  unfold completePhysicalH2ExchangedTransportCurrent
    completePhysicalH2AdvectingLowExchangedTransportCurrent
    completePhysicalH2TransportedLowExchangedTransportCurrent
    completePhysicalH2ReceiverLowExchangedTransportCurrent
    completePhysicalH2ComparableExchangedTransportCurrent
  exact real_tsum_completeTransportAddress_eq_fourSectors _
    (summable_completePhysicalH2ExchangedTransportPopulation solution t)

theorem completePhysicalH2WeightedStretchingCurrent_eq_fourSectors
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2WeightedStretchingCurrent solution t =
      completePhysicalH2AdvectingLowWeightedStretchingCurrent solution t +
      completePhysicalH2TransportedLowWeightedStretchingCurrent solution t +
      completePhysicalH2ReceiverLowWeightedStretchingCurrent solution t +
      completePhysicalH2ComparableWeightedStretchingCurrent solution t := by
  unfold completePhysicalH2WeightedStretchingCurrent
    completePhysicalH2AdvectingLowWeightedStretchingCurrent
    completePhysicalH2TransportedLowWeightedStretchingCurrent
    completePhysicalH2ReceiverLowWeightedStretchingCurrent
    completePhysicalH2ComparableWeightedStretchingCurrent
  exact real_tsum_completeStretchingAddress_eq_fourSectors _
    (summable_completePhysicalH2WeightedStretchingPopulation solution t)

/-! ## Exact transport exchange -/

theorem completePhysicalH2ExchangedTransportFace_exchange
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress) :
    completePhysicalH2ExchangedTransportFace solution t
        (completeTransportExchange address) =
      completePhysicalH2ExchangedTransportFace solution t address := by
  have hdivergence := openPeriodicVelocityFourierMode_divergenceFree
    solution t address.1
  have hfaceExchange :=
    completeOpenVorticityTransportFace_exchange solution t address
  unfold completePhysicalH2ExchangedTransportFace
  rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul]
  · rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul]
    · simp only [completeTransportTriad, completeTransportExchange_first,
        completeTransportExchange_second, completeTransportReceiver_exchange]
      unfold completeOpenVorticityTransportFace at hfaceExchange
      simp only [completeTransportExchange_first, completeTransportExchange_second,
        completeTransportReceiver_exchange] at hfaceExchange
      rw [hfaceExchange]
      push_cast
      ring
    · simpa [completeTransportTriad] using hdivergence
  · simpa [completeTransportTriad] using hdivergence

def completeTransportTriadExchangeEquiv :
    AddressedClosedFourierTriad ≃ AddressedClosedFourierTriad :=
  completeTransportAddressEquivTriad.symm.trans
    (completeTransportExchange.trans completeTransportAddressEquivTriad)

theorem completeTransportTriadExchange_transportedLow_iff_receiverLow
    (triad : AddressedClosedFourierTriad) :
    TransportedLowSector (completeTransportTriadExchangeEquiv triad) ↔
      ReceiverLowSector triad := by
  let address := completeTransportAddressEquivTriad.symm triad
  have hsector := completeTransportExchange_transportedLow_iff_receiverLow address
  calc
    TransportedLowSector (completeTransportTriadExchangeEquiv triad) ↔
        TransportedLowSector
          (completeTransportTriad
            (completeTransportExchange (completeTransportAddressEquivTriad.symm triad))) := by
      rfl
    _ ↔ ReceiverLowSector
        (completeTransportTriad (completeTransportAddressEquivTriad.symm triad)) := hsector
    _ ↔ ReceiverLowSector triad := by
      rw [show completeTransportTriad (completeTransportAddressEquivTriad.symm triad) =
          triad from completeTransportAddressEquivTriad.apply_symm_apply triad]

def receiverLowExchangeEquivTransportedLow :
    {triad : AddressedClosedFourierTriad // ReceiverLowSector triad} ≃
      {triad : AddressedClosedFourierTriad // TransportedLowSector triad} :=
  completeTransportTriadExchangeEquiv.subtypeEquiv fun triad ↦
    (completeTransportTriadExchange_transportedLow_iff_receiverLow triad).symm

theorem completePhysicalH2TransportedLowExchangedTransportCurrent_eq_receiverLow
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2TransportedLowExchangedTransportCurrent solution t =
      completePhysicalH2ReceiverLowExchangedTransportCurrent solution t := by
  unfold completePhysicalH2TransportedLowExchangedTransportCurrent
    completePhysicalH2ReceiverLowExchangedTransportCurrent
  calc
    (∑' sector : {triad // TransportedLowSector triad},
        (completePhysicalH2ExchangedTransportFace solution t
          (completeTransportAddressEquivTriad.symm sector.1)).re) =
      ∑' sector : {triad // ReceiverLowSector triad},
        (completePhysicalH2ExchangedTransportFace solution t
          (completeTransportAddressEquivTriad.symm
            (receiverLowExchangeEquivTransportedLow sector).1)).re :=
      (receiverLowExchangeEquivTransportedLow.tsum_eq
        (fun sector ↦
          (completePhysicalH2ExchangedTransportFace solution t
            (completeTransportAddressEquivTriad.symm sector.1)).re)).symm
    _ = ∑' sector : {triad // ReceiverLowSector triad},
        (completePhysicalH2ExchangedTransportFace solution t
          (completeTransportAddressEquivTriad.symm sector.1)).re := by
      apply tsum_congr
      intro sector
      have hexchange := completePhysicalH2ExchangedTransportFace_exchange
        solution t (completeTransportAddressEquivTriad.symm sector.1)
      have hre := congrArg Complex.re hexchange
      change
        (completePhysicalH2ExchangedTransportFace solution t
          (completeTransportAddressEquivTriad.symm
            (completeTransportAddressEquivTriad
              (completeTransportExchange
                (completeTransportAddressEquivTriad.symm sector.1))))).re =
          (completePhysicalH2ExchangedTransportFace solution t
            (completeTransportAddressEquivTriad.symm sector.1)).re
      rw [completeTransportAddressEquivTriad.symm_apply_apply]
      exact hre

/-! ## The literal physical H2 current in eight and seven sector terms -/

theorem completePhysicalH2Current_eq_eightSectorCurrents
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2Current solution t =
      completePhysicalH2AdvectingLowWeightedStretchingCurrent solution t +
      completePhysicalH2TransportedLowWeightedStretchingCurrent solution t +
      completePhysicalH2ReceiverLowWeightedStretchingCurrent solution t +
      completePhysicalH2ComparableWeightedStretchingCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2AdvectingLowExchangedTransportCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2TransportedLowExchangedTransportCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2ReceiverLowExchangedTransportCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2ComparableExchangedTransportCurrent solution t := by
  rw [completePhysicalH2Current_eq_weightedStretching_add_half_exchangedTransport,
    completePhysicalH2WeightedStretchingCurrent_eq_fourSectors,
    completePhysicalH2ExchangedTransportCurrent_eq_fourSectors]
  ring

theorem completePhysicalH2Current_eq_sevenSectorCurrents
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2Current solution t =
      completePhysicalH2AdvectingLowWeightedStretchingCurrent solution t +
      completePhysicalH2TransportedLowWeightedStretchingCurrent solution t +
      completePhysicalH2ReceiverLowWeightedStretchingCurrent solution t +
      completePhysicalH2ComparableWeightedStretchingCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2AdvectingLowExchangedTransportCurrent solution t +
      completePhysicalH2TransportedLowExchangedTransportCurrent solution t +
      (1 / 2 : ℝ) * completePhysicalH2ComparableExchangedTransportCurrent solution t := by
  rw [completePhysicalH2Current_eq_eightSectorCurrents,
    completePhysicalH2TransportedLowExchangedTransportCurrent_eq_receiverLow]
  ring

section Audit

#print axioms completePhysicalH2ExchangedTransportCurrent_eq_fourSectors
#print axioms completePhysicalH2WeightedStretchingCurrent_eq_fourSectors
#print axioms completePhysicalH2ExchangedTransportFace_exchange
#print axioms completePhysicalH2TransportedLowExchangedTransportCurrent_eq_receiverLow
#print axioms completePhysicalH2Current_eq_eightSectorCurrents
#print axioms completePhysicalH2Current_eq_sevenSectorCurrents

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentSectorJoin
