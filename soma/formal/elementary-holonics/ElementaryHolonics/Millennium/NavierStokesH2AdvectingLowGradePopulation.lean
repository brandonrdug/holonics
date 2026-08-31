import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurrentSectorJoin

/-!
# Exact grade population of the advecting-low physical H2 sector

**[proved-derived; formal-checked]** The complete advecting-low transport population is
reindexed, with full address multiplicity, by the least dyadic grade of its advecting pin and the
maximum grade of its two high pins.  Grade zero is retained as the actual low-frequency cube; it
is not represented by an invented predecessor shell.  Triad closure makes the two high grades
equal or adjacent, and all signed sums are transported through the grade equivalence before any
norm receiver is applied.

This file is geometric and measure-theoretic bookkeeping only.  It introduces no face-mass,
terminal-control, or regularity estimate.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradePopulation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentSectorJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

abbrev CompleteAdvectingLowAddress :=
  {address : CompleteTransportAddress //
    AdvectingLowSector (completeTransportTriad address)}

def CompleteAdvectingLowGradeFiber (lowGrade highGrade : ℕ) :=
  {address : CompleteAdvectingLowAddress //
    advectingGrade (completeTransportTriad address.1) = lowGrade ∧
      max
        (transportedGrade (completeTransportTriad address.1))
        (receiverGrade (completeTransportTriad address.1)) = highGrade}

def completeAdvectingLowGradeEquiv :
    CompleteAdvectingLowAddress ≃
      Σ lowGrade : ℕ, Σ highGrade : ℕ,
        CompleteAdvectingLowGradeFiber lowGrade highGrade where
  toFun := fun address ↦
    ⟨advectingGrade (completeTransportTriad address.1),
      ⟨max
          (transportedGrade (completeTransportTriad address.1))
          (receiverGrade (completeTransportTriad address.1)),
        ⟨address, rfl, rfl⟩⟩⟩
  invFun := fun graded ↦ graded.2.2.1
  left_inv := by
    intro address
    rfl
  right_inv := by
    rintro ⟨lowGrade, highGrade, address, hlow, hhigh⟩
    subst lowGrade
    subst highGrade
    rfl

/-- The address-side population used by the grade decomposition and the closed-triad-side
population used by the physical sector current are the same occurrences with both boundary maps
retained. -/
def completeAdvectingLowAddressEquivTriad :
    CompleteAdvectingLowAddress ≃
      {triad : AddressedClosedFourierTriad // AdvectingLowSector triad} :=
  completeTransportAddressEquivTriad.subtypeEquiv fun _address ↦ Iff.rfl

theorem CompleteAdvectingLowGradeFiber.low_lt_high
    {lowGrade highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber lowGrade highGrade) :
    lowGrade < highGrade := by
  let triad := completeTransportTriad address.1.1
  have hsector : AdvectingLowSector triad := address.1.2
  have hlow : advectingGrade triad = lowGrade := address.2.1
  have hhigh :
      max (transportedGrade triad) (receiverGrade triad) = highGrade := address.2.2
  calc
    lowGrade = advectingGrade triad := hlow.symm
    _ < transportedGrade triad := hsector.1
    _ ≤ max (transportedGrade triad) (receiverGrade triad) := Nat.le_max_left _ _
    _ = highGrade := hhigh

theorem CompleteAdvectingLowGradeFiber.advecting_mem_gradeCube
    {lowGrade highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber lowGrade highGrade) :
    (completeTransportTriad address.1.1).advecting ∈
      frequencyCube (dyadicRadius lowGrade) := by
  let triad := completeTransportTriad address.1.1
  have hlow : frequencyDyadicGrade triad.advecting = lowGrade := address.2.1
  rw [← frequencyDyadicGrade_le_iff_mem]
  change frequencyDyadicGrade triad.advecting ≤ lowGrade
  exact hlow.le

theorem CompleteAdvectingLowGradeFiber.transported_mem_highCube
    {lowGrade highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber lowGrade highGrade) :
    (completeTransportTriad address.1.1).transported ∈
      frequencyCube (dyadicRadius highGrade) := by
  let triad := completeTransportTriad address.1.1
  have hhigh :
      max (transportedGrade triad) (receiverGrade triad) = highGrade := address.2.2
  rw [← frequencyDyadicGrade_le_iff_mem]
  change transportedGrade triad ≤ highGrade
  exact hhigh ▸ Nat.le_max_left _ _

theorem CompleteAdvectingLowGradeFiber.receiver_mem_highCube
    {lowGrade highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber lowGrade highGrade) :
    (completeTransportTriad address.1.1).receiver ∈
      frequencyCube (dyadicRadius highGrade) := by
  let triad := completeTransportTriad address.1.1
  have hhigh :
      max (transportedGrade triad) (receiverGrade triad) = highGrade := address.2.2
  rw [← frequencyDyadicGrade_le_iff_mem]
  change receiverGrade triad ≤ highGrade
  exact hhigh ▸ Nat.le_max_right _ _

theorem CompleteAdvectingLowGradeFiber.highGrade_pattern
    {lowGrade highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber lowGrade highGrade) :
    let triad := completeTransportTriad address.1.1
    (transportedGrade triad = highGrade ∧ receiverGrade triad = highGrade) ∨
      (transportedGrade triad = highGrade ∧ receiverGrade triad + 1 = highGrade) ∨
      (receiverGrade triad = highGrade ∧ transportedGrade triad + 1 = highGrade) := by
  let triad := completeTransportTriad address.1.1
  change
    (transportedGrade triad = highGrade ∧ receiverGrade triad = highGrade) ∨
      (transportedGrade triad = highGrade ∧ receiverGrade triad + 1 = highGrade) ∨
      (receiverGrade triad = highGrade ∧ transportedGrade triad + 1 = highGrade)
  have hsector : AdvectingLowSector triad := address.1.2
  have hhigh :
      max (transportedGrade triad) (receiverGrade triad) = highGrade := address.2.2
  have hprox := advectingLowSector_highGrades_proximate hsector
  by_cases hle : transportedGrade triad ≤ receiverGrade triad
  · have hreceiver : receiverGrade triad = highGrade := by
      rw [Nat.max_eq_right hle] at hhigh
      exact hhigh
    by_cases heq : transportedGrade triad = receiverGrade triad
    · exact Or.inl ⟨heq.trans hreceiver, hreceiver⟩
    · exact Or.inr (Or.inr ⟨hreceiver, by omega⟩)
  · have hreverse : receiverGrade triad ≤ transportedGrade triad := Nat.le_of_not_ge hle
    have htransported : transportedGrade triad = highGrade := by
      rw [Nat.max_eq_left hreverse] at hhigh
      exact hhigh
    by_cases heq : receiverGrade triad = transportedGrade triad
    · exact Or.inl ⟨htransported, heq.trans htransported⟩
    · exact Or.inr (Or.inl ⟨htransported, by omega⟩)

theorem CompleteAdvectingLowGradeFiber.gradeZero_geometry
    {highGrade : ℕ}
    (address : CompleteAdvectingLowGradeFiber 0 highGrade) :
    0 < highGrade ∧
      (completeTransportTriad address.1.1).advecting ∈ lowFrequencyModes ∧
      (completeTransportTriad address.1.1).transported ∈
        frequencyCube (dyadicRadius highGrade) ∧
      (completeTransportTriad address.1.1).receiver ∈
        frequencyCube (dyadicRadius highGrade) := by
  let triad := completeTransportTriad address.1.1
  have hpositive := address.low_lt_high
  have hlow : frequencyDyadicGrade triad.advecting = 0 := address.2.1
  exact ⟨hpositive,
    (frequencyDyadicGrade_eq_zero_iff triad.advecting).mp hlow,
    address.transported_mem_highCube,
    address.receiver_mem_highCube⟩

theorem CompleteAdvectingLowGradeFiber.successor_geometry
    {lowLevel highLevel : ℕ}
    (address : CompleteAdvectingLowGradeFiber (lowLevel + 1) (highLevel + 1)) :
    lowLevel + 1 ≤ highLevel ∧
      (completeTransportTriad address.1.1).advecting ∈ dyadicFrequencyShell lowLevel ∧
      (completeTransportTriad address.1.1).transported ∈
        frequencyCube (dyadicRadius (highLevel + 1)) ∧
      (completeTransportTriad address.1.1).receiver ∈
        frequencyCube (dyadicRadius (highLevel + 1)) := by
  let triad := completeTransportTriad address.1.1
  have hlt := address.low_lt_high
  have hlow : frequencyDyadicGrade triad.advecting = lowLevel + 1 := address.2.1
  exact ⟨by omega,
    (frequencyDyadicGrade_eq_succ_iff triad.advecting lowLevel).mp hlow,
    address.transported_mem_highCube,
    address.receiver_mem_highCube⟩

theorem tsum_completeAdvectingLow_eq_tsum_gradeFiber
    (face : CompleteAdvectingLowAddress → ℂ) (hface : Summable face) :
    (∑' address : CompleteAdvectingLowAddress, face address) =
      ∑' lowGrade : ℕ, ∑' highGrade : ℕ,
        ∑' address : CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face address.1 := by
  let reindex := completeAdvectingLowGradeEquiv
  have hreindexed : Summable (fun graded ↦ face (reindex.symm graded)) :=
    (reindex.symm.summable_iff).mpr hface
  calc
    (∑' address : CompleteAdvectingLowAddress, face address) =
        ∑' graded : Σ lowGrade : ℕ, Σ highGrade : ℕ,
          CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face (reindex.symm graded) :=
      (reindex.symm.tsum_eq face).symm
    _ = ∑' lowGrade : ℕ,
        ∑' graded : Σ highGrade : ℕ,
          CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face (reindex.symm ⟨lowGrade, graded⟩) := hreindexed.tsum_sigma
    _ = ∑' lowGrade : ℕ, ∑' highGrade : ℕ,
        ∑' address : CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face address.1 := by
      apply tsum_congr
      intro lowGrade
      rw [(hreindexed.sigma_factor lowGrade).tsum_sigma]
      rfl

private theorem real_tsum_completeAdvectingLow_eq_tsum_gradeFiber
    (face : CompleteAdvectingLowAddress → ℝ) (hface : Summable face) :
    (∑' address : CompleteAdvectingLowAddress, face address) =
      ∑' lowGrade : ℕ, ∑' highGrade : ℕ,
        ∑' address : CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face address.1 := by
  let reindex := completeAdvectingLowGradeEquiv
  have hreindexed : Summable (fun graded ↦ face (reindex.symm graded)) :=
    (reindex.symm.summable_iff).mpr hface
  calc
    (∑' address : CompleteAdvectingLowAddress, face address) =
        ∑' graded : Σ lowGrade : ℕ, Σ highGrade : ℕ,
          CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face (reindex.symm graded) :=
      (reindex.symm.tsum_eq face).symm
    _ = ∑' lowGrade : ℕ,
        ∑' graded : Σ highGrade : ℕ,
          CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face (reindex.symm ⟨lowGrade, graded⟩) := hreindexed.tsum_sigma
    _ = ∑' lowGrade : ℕ, ∑' highGrade : ℕ,
        ∑' address : CompleteAdvectingLowGradeFiber lowGrade highGrade,
          face address.1 := by
      apply tsum_congr
      intro lowGrade
      rw [(hreindexed.sigma_factor lowGrade).tsum_sigma]
      rfl

/-! ## The actual physical sector in the grade chart -/

/-- The actual advecting-low exchanged-transport current is the signed nested sum of its exact
least-grade address fibres.  This is the physical-current specialization of the population
equivalence, still before a norm or face-mass receiver. -/
theorem completePhysicalH2AdvectingLowExchangedTransportCurrent_eq_gradeFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    completePhysicalH2AdvectingLowExchangedTransportCurrent solution t =
      ∑' lowGrade : ℕ, ∑' highGrade : ℕ,
        ∑' address : CompleteAdvectingLowGradeFiber lowGrade highGrade,
          (completePhysicalH2ExchangedTransportFace solution t address.1.1).re := by
  let face : CompleteAdvectingLowAddress → ℝ := fun address ↦
    (completePhysicalH2ExchangedTransportFace solution t address.1).re
  have hface : Summable face :=
    (summable_completePhysicalH2ExchangedTransportPopulation solution t).comp_injective
      Subtype.val_injective
  have haddress :
      completePhysicalH2AdvectingLowExchangedTransportCurrent solution t =
        ∑' address : CompleteAdvectingLowAddress, face address := by
    unfold completePhysicalH2AdvectingLowExchangedTransportCurrent
    let sectorFace : {triad : AddressedClosedFourierTriad // AdvectingLowSector triad} → ℝ :=
      fun sector ↦
        (completePhysicalH2ExchangedTransportFace solution t
          (completeTransportAddressEquivTriad.symm sector.1)).re
    calc
      (∑' sector : {triad : AddressedClosedFourierTriad // AdvectingLowSector triad},
          (completePhysicalH2ExchangedTransportFace solution t
            (completeTransportAddressEquivTriad.symm sector.1)).re) =
          ∑' sector, sectorFace sector := rfl
      _ = ∑' address : CompleteAdvectingLowAddress,
          sectorFace (completeAdvectingLowAddressEquivTriad address) :=
        (completeAdvectingLowAddressEquivTriad.tsum_eq sectorFace).symm
      _ = ∑' address : CompleteAdvectingLowAddress, face address := by
        apply tsum_congr
        intro address
        change
          (completePhysicalH2ExchangedTransportFace solution t
            (completeTransportAddressEquivTriad.symm
              (completeTransportAddressEquivTriad address.1))).re = _
        rw [completeTransportAddressEquivTriad.symm_apply_apply]
  rw [haddress]
  simpa only [face] using
    (real_tsum_completeAdvectingLow_eq_tsum_gradeFiber face hface)

section Audit

#print axioms completeAdvectingLowGradeEquiv
#print axioms CompleteAdvectingLowGradeFiber.low_lt_high
#print axioms CompleteAdvectingLowGradeFiber.highGrade_pattern
#print axioms CompleteAdvectingLowGradeFiber.gradeZero_geometry
#print axioms CompleteAdvectingLowGradeFiber.successor_geometry
#print axioms tsum_completeAdvectingLow_eq_tsum_gradeFiber
#print axioms completePhysicalH2AdvectingLowExchangedTransportCurrent_eq_gradeFiber

end Audit

end Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradePopulation
