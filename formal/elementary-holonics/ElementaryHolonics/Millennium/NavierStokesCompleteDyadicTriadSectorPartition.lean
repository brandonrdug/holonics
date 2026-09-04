import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin

/-!
# Complete dyadic sector partition of the physical H2 triad population

**[proved-derived; formal-checked]** Every spatial lattice frequency has a least dyadic cube
grade. Grade zero is the retained unit low-frequency cube, while successor grade `n + 1` is
exactly sharp shell `n`. The complete transport and stretching address populations are both
equivalent to the same addressed closed-triad carrier; in the stretching chart the Hermitian
output is retained as the receiving pin at the negated output frequency.

The three pins partition into four exact and disjoint sectors: each possible unique minimum-grade pin and
the complement in which no pin is a unique minimum. Closure forces the two high pins in each
unique-low sector to differ by at most one grade, and every pair in the complement to differ by at
most one grade. A nested sum-type equivalence retains complete address multiplicity and supplies a
signed `tsum` decomposition before any norm receiver. No nonlinear estimate is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition

open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Least dyadic grade -/

theorem exists_mem_dyadicFrequencyCube (frequency : SpatialFrequency) :
    ∃ level : ℕ, frequency ∈ frequencyCube (dyadicRadius level) := by
  obtain ⟨radius, hfrequency⟩ := exists_mem_frequencyCube frequency
  have hgrowth : Tendsto dyadicRadius atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have heventual : ∀ᶠ level in atTop, radius ≤ dyadicRadius level :=
    hgrowth.eventually (eventually_ge_atTop radius)
  obtain ⟨level, hlevel⟩ := Filter.eventually_atTop.1 heventual
  exact ⟨level, frequencyCube_mono (hlevel level le_rfl) hfrequency⟩

def frequencyDyadicGrade (frequency : SpatialFrequency) : ℕ :=
  Nat.find (exists_mem_dyadicFrequencyCube frequency)

theorem frequencyDyadicGrade_mem (frequency : SpatialFrequency) :
    frequency ∈ frequencyCube (dyadicRadius (frequencyDyadicGrade frequency)) :=
  Nat.find_spec (exists_mem_dyadicFrequencyCube frequency)

theorem frequencyDyadicGrade_le_iff_mem
    (frequency : SpatialFrequency) (level : ℕ) :
    frequencyDyadicGrade frequency ≤ level ↔
      frequency ∈ frequencyCube (dyadicRadius level) := by
  constructor
  · intro hlevel
    exact frequencyCube_mono
      (Nat.pow_le_pow_right (by norm_num) hlevel)
      (frequencyDyadicGrade_mem frequency)
  · intro hfrequency
    exact Nat.find_min' (exists_mem_dyadicFrequencyCube frequency) hfrequency

theorem frequencyDyadicGrade_eq_zero_iff (frequency : SpatialFrequency) :
    frequencyDyadicGrade frequency = 0 ↔ frequency ∈ lowFrequencyModes := by
  rw [← Nat.le_zero]
  simpa only [lowFrequencyModes, dyadicRadius, pow_zero] using
    frequencyDyadicGrade_le_iff_mem frequency 0

theorem frequencyDyadicGrade_eq_succ_iff
    (frequency : SpatialFrequency) (level : ℕ) :
    frequencyDyadicGrade frequency = level + 1 ↔
      frequency ∈ dyadicFrequencyShell level := by
  rw [mem_dyadicFrequencyShell_iff]
  constructor
  · intro hgrade
    constructor
    · exact (frequencyDyadicGrade_le_iff_mem frequency (level + 1)).mp (by omega)
    · intro hinner
      have hle := (frequencyDyadicGrade_le_iff_mem frequency level).mpr hinner
      omega
  · rintro ⟨houter, hinner⟩
    have hle := (frequencyDyadicGrade_le_iff_mem frequency (level + 1)).mpr houter
    have hnle : ¬frequencyDyadicGrade frequency ≤ level := by
      intro hgrade
      exact hinner ((frequencyDyadicGrade_le_iff_mem frequency level).mp hgrade)
    omega

theorem neg_mem_frequencyCube_iff
    (frequency : SpatialFrequency) (radius : ℕ) :
    -frequency ∈ frequencyCube radius ↔ frequency ∈ frequencyCube radius := by
  rw [mem_frequencyCube_iff, mem_frequencyCube_iff]
  constructor
  · intro h coordinate
    have hc := h coordinate
    simp only [Pi.neg_apply] at hc
    omega
  · intro h coordinate
    have hc := h coordinate
    simp only [Pi.neg_apply]
    omega

@[simp]
theorem frequencyDyadicGrade_neg (frequency : SpatialFrequency) :
    frequencyDyadicGrade (-frequency) = frequencyDyadicGrade frequency := by
  apply Nat.le_antisymm
  · rw [frequencyDyadicGrade_le_iff_mem, neg_mem_frequencyCube_iff]
    exact frequencyDyadicGrade_mem frequency
  · rw [frequencyDyadicGrade_le_iff_mem]
    have hneg := frequencyDyadicGrade_mem (-frequency)
    have hdoubleNeg :=
      (neg_mem_frequencyCube_iff (-frequency)
        (dyadicRadius (frequencyDyadicGrade (-frequency)))).mpr hneg
    simpa using hdoubleNeg

theorem frequencyDyadicGrade_add_le_max_add_one
    (left right : SpatialFrequency) :
    frequencyDyadicGrade (left + right) ≤
      max (frequencyDyadicGrade left) (frequencyDyadicGrade right) + 1 := by
  let level := max (frequencyDyadicGrade left) (frequencyDyadicGrade right)
  have hleft : left ∈ frequencyCube (dyadicRadius level) :=
    frequencyCube_mono
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))
      (frequencyDyadicGrade_mem left)
  have hright : right ∈ frequencyCube (dyadicRadius level) :=
    frequencyCube_mono
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _))
      (frequencyDyadicGrade_mem right)
  have hadd := add_mem_frequencyCube_two_mul (dyadicRadius level) hleft hright
  apply (frequencyDyadicGrade_le_iff_mem (left + right) (level + 1)).mpr
  simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hadd

/-! ## Complete address charts -/

private theorem addressedClosedFourierTriad_eq_of_pins_eq
    {left right : AddressedClosedFourierTriad}
    (hadvecting : left.advecting = right.advecting)
    (htransported : left.transported = right.transported)
    (hreceiver : left.receiver = right.receiver) :
    left = right := by
  cases left
  cases right
  simp_all

def completeTransportAddressEquivTriad :
    CompleteTransportAddress ≃ AddressedClosedFourierTriad where
  toFun := completeTransportTriad
  invFun := fun triad ↦ (triad.advecting, triad.transported)
  left_inv := by intro address; rfl
  right_inv := by
    intro triad
    apply addressedClosedFourierTriad_eq_of_pins_eq
    · rfl
    · rfl
    · apply funext
      intro coordinate
      have hclosed := congrFun triad.closed coordinate
      simp only [Pi.add_apply, Pi.zero_apply] at hclosed
      change -triad.advecting coordinate - triad.transported coordinate =
        triad.receiver coordinate
      omega

def completeStretchingAddressEquivTriad :
    CompleteStretchingAddress ≃ AddressedClosedFourierTriad where
  toFun := fun address ↦
    { advecting := address.2
      transported := address.1 - address.2
      receiver := -address.1
      closed := by abel }
  invFun := fun triad ↦ (-triad.receiver, triad.advecting)
  left_inv := by
    intro address
    apply Prod.ext
    · simp
    · rfl
  right_inv := by
    intro triad
    apply addressedClosedFourierTriad_eq_of_pins_eq
    · rfl
    · apply funext
      intro coordinate
      have hclosed := congrFun triad.closed coordinate
      simp only [Pi.add_apply, Pi.zero_apply] at hclosed
      change -triad.receiver coordinate - triad.advecting coordinate =
        triad.transported coordinate
      omega
    · simp

/-! ## Four exact sectors -/

def advectingGrade (triad : AddressedClosedFourierTriad) : ℕ :=
  frequencyDyadicGrade triad.advecting

def transportedGrade (triad : AddressedClosedFourierTriad) : ℕ :=
  frequencyDyadicGrade triad.transported

def receiverGrade (triad : AddressedClosedFourierTriad) : ℕ :=
  frequencyDyadicGrade triad.receiver

def AdvectingLowSector (triad : AddressedClosedFourierTriad) : Prop :=
  advectingGrade triad < transportedGrade triad ∧
    advectingGrade triad < receiverGrade triad

def TransportedLowSector (triad : AddressedClosedFourierTriad) : Prop :=
  transportedGrade triad < advectingGrade triad ∧
    transportedGrade triad < receiverGrade triad

def ReceiverLowSector (triad : AddressedClosedFourierTriad) : Prop :=
  receiverGrade triad < advectingGrade triad ∧
    receiverGrade triad < transportedGrade triad

def ComparableSector (triad : AddressedClosedFourierTriad) : Prop :=
  ¬AdvectingLowSector triad ∧
    ¬TransportedLowSector triad ∧
      ¬ReceiverLowSector triad

theorem advectingLow_not_transportedLow
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) : ¬TransportedLowSector triad := by
  intro hother
  exact Nat.lt_asymm hsector.1 hother.1

theorem advectingLow_not_receiverLow
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) : ¬ReceiverLowSector triad := by
  intro hother
  exact Nat.lt_asymm hsector.2 hother.1

theorem transportedLow_not_receiverLow
    {triad : AddressedClosedFourierTriad}
    (hsector : TransportedLowSector triad) : ¬ReceiverLowSector triad := by
  intro hother
  exact Nat.lt_asymm hsector.2 hother.2

theorem advectingLow_not_comparable
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) : ¬ComparableSector triad := by
  intro hother
  exact hother.1 hsector

theorem transportedLow_not_comparable
    {triad : AddressedClosedFourierTriad}
    (hsector : TransportedLowSector triad) : ¬ComparableSector triad := by
  intro hother
  exact hother.2.1 hsector

theorem receiverLow_not_comparable
    {triad : AddressedClosedFourierTriad}
    (hsector : ReceiverLowSector triad) : ¬ComparableSector triad := by
  intro hother
  exact hother.2.2 hsector

theorem triadSector_exhaustive (triad : AddressedClosedFourierTriad) :
    AdvectingLowSector triad ∨ TransportedLowSector triad ∨
      ReceiverLowSector triad ∨ ComparableSector triad := by
  by_cases ha : AdvectingLowSector triad
  · exact Or.inl ha
  by_cases ht : TransportedLowSector triad
  · exact Or.inr (Or.inl ht)
  by_cases hr : ReceiverLowSector triad
  · exact Or.inr (Or.inr (Or.inl hr))
  exact Or.inr (Or.inr (Or.inr ⟨ha, ht, hr⟩))

/-! ## Closure proximity -/

theorem advectingGrade_le_max_other_add_one
    (triad : AddressedClosedFourierTriad) :
    advectingGrade triad ≤ max (transportedGrade triad) (receiverGrade triad) + 1 := by
  have hsum : -(triad.transported + triad.receiver) = triad.advecting := by
    apply funext
    intro coordinate
    have hclosed := congrFun triad.closed coordinate
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hclosed ⊢
    omega
  unfold advectingGrade
  rw [← hsum, frequencyDyadicGrade_neg]
  exact frequencyDyadicGrade_add_le_max_add_one triad.transported triad.receiver

theorem transportedGrade_le_max_other_add_one
    (triad : AddressedClosedFourierTriad) :
    transportedGrade triad ≤ max (advectingGrade triad) (receiverGrade triad) + 1 := by
  have hsum : -(triad.advecting + triad.receiver) = triad.transported := by
    apply funext
    intro coordinate
    have hclosed := congrFun triad.closed coordinate
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hclosed ⊢
    omega
  unfold transportedGrade
  rw [← hsum, frequencyDyadicGrade_neg]
  exact frequencyDyadicGrade_add_le_max_add_one triad.advecting triad.receiver

theorem receiverGrade_le_max_other_add_one
    (triad : AddressedClosedFourierTriad) :
    receiverGrade triad ≤ max (advectingGrade triad) (transportedGrade triad) + 1 := by
  have hsum : -(triad.advecting + triad.transported) = triad.receiver := by
    apply funext
    intro coordinate
    have hclosed := congrFun triad.closed coordinate
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hclosed ⊢
    omega
  unfold receiverGrade
  rw [← hsum, frequencyDyadicGrade_neg]
  exact frequencyDyadicGrade_add_le_max_add_one triad.advecting triad.transported

theorem advectingLowSector_highGrades_proximate
    {triad : AddressedClosedFourierTriad} (hsector : AdvectingLowSector triad) :
    transportedGrade triad ≤ receiverGrade triad + 1 ∧
      receiverGrade triad ≤ transportedGrade triad + 1 := by
  constructor
  · have h := transportedGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right (Nat.le_of_lt hsector.2)] at h
    exact h
  · have h := receiverGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right (Nat.le_of_lt hsector.1)] at h
    exact h

theorem transportedLowSector_highGrades_proximate
    {triad : AddressedClosedFourierTriad} (hsector : TransportedLowSector triad) :
    advectingGrade triad ≤ receiverGrade triad + 1 ∧
      receiverGrade triad ≤ advectingGrade triad + 1 := by
  constructor
  · have h := advectingGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right (Nat.le_of_lt hsector.2)] at h
    exact h
  · have h := receiverGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left (Nat.le_of_lt hsector.1)] at h
    exact h

theorem receiverLowSector_highGrades_proximate
    {triad : AddressedClosedFourierTriad} (hsector : ReceiverLowSector triad) :
    advectingGrade triad ≤ transportedGrade triad + 1 ∧
      transportedGrade triad ≤ advectingGrade triad + 1 := by
  constructor
  · have h := advectingGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left (Nat.le_of_lt hsector.2)] at h
    exact h
  · have h := transportedGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left (Nat.le_of_lt hsector.1)] at h
    exact h

theorem comparableSector_gradeDiameter_le_one
    {triad : AddressedClosedFourierTriad} (hsector : ComparableSector triad) :
    advectingGrade triad ≤ transportedGrade triad + 1 ∧
      transportedGrade triad ≤ advectingGrade triad + 1 ∧
      advectingGrade triad ≤ receiverGrade triad + 1 ∧
      receiverGrade triad ≤ advectingGrade triad + 1 ∧
      transportedGrade triad ≤ receiverGrade triad + 1 ∧
      receiverGrade triad ≤ transportedGrade triad + 1 := by
  have hat : advectingGrade triad ≤ transportedGrade triad + 1 := by
    by_contra hnot
    have hta : transportedGrade triad < advectingGrade triad := by omega
    have hntr : ¬transportedGrade triad < receiverGrade triad := by
      intro htr
      exact hsector.2.1 ⟨hta, htr⟩
    have hrt : receiverGrade triad ≤ transportedGrade triad := Nat.le_of_not_gt hntr
    have hbound := advectingGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left hrt] at hbound
    omega
  have hta : transportedGrade triad ≤ advectingGrade triad + 1 := by
    by_contra hnot
    have hat' : advectingGrade triad < transportedGrade triad := by omega
    have hnar : ¬advectingGrade triad < receiverGrade triad := by
      intro har
      exact hsector.1 ⟨hat', har⟩
    have hra : receiverGrade triad ≤ advectingGrade triad := Nat.le_of_not_gt hnar
    have hbound := transportedGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left hra] at hbound
    omega
  have har : advectingGrade triad ≤ receiverGrade triad + 1 := by
    by_contra hnot
    have hra : receiverGrade triad < advectingGrade triad := by omega
    have hnrt : ¬receiverGrade triad < transportedGrade triad := by
      intro hrt
      exact hsector.2.2 ⟨hra, hrt⟩
    have htr : transportedGrade triad ≤ receiverGrade triad := Nat.le_of_not_gt hnrt
    have hbound := advectingGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right htr] at hbound
    omega
  have hra : receiverGrade triad ≤ advectingGrade triad + 1 := by
    by_contra hnot
    have har' : advectingGrade triad < receiverGrade triad := by omega
    have hnat : ¬advectingGrade triad < transportedGrade triad := by
      intro hat'
      exact hsector.1 ⟨hat', har'⟩
    have hta' : transportedGrade triad ≤ advectingGrade triad := Nat.le_of_not_gt hnat
    have hbound := receiverGrade_le_max_other_add_one triad
    rw [Nat.max_eq_left hta'] at hbound
    omega
  have htr : transportedGrade triad ≤ receiverGrade triad + 1 := by
    by_contra hnot
    have hrt : receiverGrade triad < transportedGrade triad := by omega
    have hnra : ¬receiverGrade triad < advectingGrade triad := by
      intro hra'
      exact hsector.2.2 ⟨hra', hrt⟩
    have har' : advectingGrade triad ≤ receiverGrade triad := Nat.le_of_not_gt hnra
    have hbound := transportedGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right har'] at hbound
    omega
  have hrt : receiverGrade triad ≤ transportedGrade triad + 1 := by
    by_contra hnot
    have htr' : transportedGrade triad < receiverGrade triad := by omega
    have hnta : ¬transportedGrade triad < advectingGrade triad := by
      intro hta'
      exact hsector.2.1 ⟨hta', htr'⟩
    have hat' : advectingGrade triad ≤ transportedGrade triad := Nat.le_of_not_gt hnta
    have hbound := receiverGrade_le_max_other_add_one triad
    rw [Nat.max_eq_right hat'] at hbound
    omega
  exact ⟨hat, hta, har, hra, htr, hrt⟩

/-! ## Exact reconstruction and signed sums -/

abbrev CompleteDyadicTriadSectors :=
  {triad : AddressedClosedFourierTriad // AdvectingLowSector triad} ⊕
    ({triad : AddressedClosedFourierTriad // TransportedLowSector triad} ⊕
      ({triad : AddressedClosedFourierTriad // ReceiverLowSector triad} ⊕
        {triad : AddressedClosedFourierTriad // ComparableSector triad}))

def sectorTriad : CompleteDyadicTriadSectors → AddressedClosedFourierTriad
  | Sum.inl triad => triad.1
  | Sum.inr (Sum.inl triad) => triad.1
  | Sum.inr (Sum.inr (Sum.inl triad)) => triad.1
  | Sum.inr (Sum.inr (Sum.inr triad)) => triad.1

def triadSector (triad : AddressedClosedFourierTriad) : CompleteDyadicTriadSectors :=
  by
    classical
    exact
      if ha : AdvectingLowSector triad then Sum.inl ⟨triad, ha⟩
      else if ht : TransportedLowSector triad then Sum.inr (Sum.inl ⟨triad, ht⟩)
      else if hr : ReceiverLowSector triad then Sum.inr (Sum.inr (Sum.inl ⟨triad, hr⟩))
      else Sum.inr (Sum.inr (Sum.inr ⟨triad, ha, ht, hr⟩))

def triadSectorEquiv : AddressedClosedFourierTriad ≃ CompleteDyadicTriadSectors where
  toFun := triadSector
  invFun := sectorTriad
  left_inv := by
    intro triad
    simp only [triadSector]
    split_ifs <;> rfl
  right_inv := by
    intro sector
    rcases sector with advecting | rest
    · have ha := advecting.2
      simp [triadSector, sectorTriad, ha]
    · rcases rest with transported | rest
      · have ht := transported.2
        have ha := fun h ↦ advectingLow_not_transportedLow h ht
        change triadSector transported.1 = Sum.inr (Sum.inl transported)
        simp only [triadSector, dif_neg ha, dif_pos ht]
      · rcases rest with receiver | comparable
        · have hr := receiver.2
          have ha := fun h ↦ advectingLow_not_receiverLow h hr
          have ht := fun h ↦ transportedLow_not_receiverLow h hr
          change triadSector receiver.1 = Sum.inr (Sum.inr (Sum.inl receiver))
          simp only [triadSector, dif_neg ha, dif_neg ht, dif_pos hr]
        · rcases comparable.2 with ⟨ha, ht, hr⟩
          simp [triadSector, sectorTriad, ha, ht, hr]

def completeTransportAddressSectorEquiv :
    CompleteTransportAddress ≃ CompleteDyadicTriadSectors :=
  completeTransportAddressEquivTriad.trans triadSectorEquiv

def completeStretchingAddressSectorEquiv :
    CompleteStretchingAddress ≃ CompleteDyadicTriadSectors :=
  completeStretchingAddressEquivTriad.trans triadSectorEquiv

private theorem tsum_sum_type
    {left right : Type} (face : left ⊕ right → ℂ) (hface : Summable face) :
    (∑' address : left ⊕ right, face address) =
      (∑' address : left, face (.inl address)) +
        ∑' address : right, face (.inr address) := by
  let reindex := Equiv.sumEquivSigmaBool left right
  have hsigma :
      Summable (fun address : (side : Bool) × bif side then right else left ↦
        face (reindex.symm address)) := by
    have hreindex := (reindex.symm.summable_iff).mpr hface
    simpa [Function.comp_def] using hreindex
  calc
    (∑' address : left ⊕ right, face address) =
        ∑' address : (side : Bool) × bif side then right else left,
          face (reindex.symm address) := by
      exact (reindex.symm.tsum_eq face).symm
    _ = ∑' side : Bool, ∑' address : bif side then right else left,
        face (reindex.symm ⟨side, address⟩) := hsigma.tsum_sigma
    _ = (∑' address : left, face (.inl address)) +
        ∑' address : right, face (.inr address) := by
      rw [tsum_fintype, Fintype.sum_bool]
      simp only [reindex, Equiv.sumEquivSigmaBool, Equiv.symm_mk, Equiv.coe_fn_mk]
      change (∑' address : right, face (.inr address)) +
          (∑' address : left, face (.inl address)) = _
      rw [add_comm]

theorem tsum_closedTriad_eq_fourSectors
    (face : AddressedClosedFourierTriad → ℂ) (hface : Summable face) :
    (∑' triad : AddressedClosedFourierTriad, face triad) =
      (∑' triad : {triad // AdvectingLowSector triad}, face triad.1) +
      (∑' triad : {triad // TransportedLowSector triad}, face triad.1) +
      (∑' triad : {triad // ReceiverLowSector triad}, face triad.1) +
      ∑' triad : {triad // ComparableSector triad}, face triad.1 := by
  let sectorFace : CompleteDyadicTriadSectors → ℂ :=
    fun sector ↦ face (sectorTriad sector)
  have hsectorFace : Summable sectorFace := by
    apply (triadSectorEquiv.summable_iff).mp
    apply hface.congr
    intro triad
    change face triad = face (triadSectorEquiv.symm (triadSectorEquiv triad))
    exact congrArg face (triadSectorEquiv.symm_apply_apply triad).symm
  have hrestOne : Summable (fun sector ↦ sectorFace (Sum.inr sector)) :=
    hsectorFace.comp_injective Sum.inr_injective
  have hrestTwo :
      Summable (fun sector ↦ sectorFace (Sum.inr (Sum.inr sector))) :=
    hrestOne.comp_injective Sum.inr_injective
  have hsplitOne := tsum_sum_type sectorFace hsectorFace
  have hsplitTwo :=
    tsum_sum_type (fun sector ↦ sectorFace (Sum.inr sector)) hrestOne
  have hsplitThree :=
    tsum_sum_type (fun sector ↦ sectorFace (Sum.inr (Sum.inr sector))) hrestTwo
  calc
    (∑' triad : AddressedClosedFourierTriad, face triad) =
        ∑' sector : CompleteDyadicTriadSectors, sectorFace sector := by
      rw [← triadSectorEquiv.tsum_eq sectorFace]
      apply tsum_congr
      intro triad
      change face triad = face (triadSectorEquiv.symm (triadSectorEquiv triad))
      exact congrArg face (triadSectorEquiv.symm_apply_apply triad).symm
    _ = (∑' triad : {triad // AdvectingLowSector triad}, face triad.1) +
        (∑' triad : {triad // TransportedLowSector triad}, face triad.1) +
        (∑' triad : {triad // ReceiverLowSector triad}, face triad.1) +
        ∑' triad : {triad // ComparableSector triad}, face triad.1 := by
      rw [hsplitOne, hsplitTwo, hsplitThree]
      simp only [sectorFace, sectorTriad]
      abel

theorem tsum_completeTransportAddress_eq_fourSectors
    (face : CompleteTransportAddress → ℂ) (hface : Summable face) :
    (∑' address : CompleteTransportAddress, face address) =
      (∑' sector : {triad // AdvectingLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // TransportedLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // ReceiverLowSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1)) +
      ∑' sector : {triad // ComparableSector triad},
        face (completeTransportAddressEquivTriad.symm sector.1) := by
  have htriad : Summable
      (fun triad ↦ face (completeTransportAddressEquivTriad.symm triad)) := by
    exact (completeTransportAddressEquivTriad.symm.summable_iff).mpr hface
  calc
    (∑' address : CompleteTransportAddress, face address) =
        ∑' triad : AddressedClosedFourierTriad,
          face (completeTransportAddressEquivTriad.symm triad) :=
      (completeTransportAddressEquivTriad.symm.tsum_eq face).symm
    _ = _ := tsum_closedTriad_eq_fourSectors _ htriad

theorem tsum_completeStretchingAddress_eq_fourSectors
    (face : CompleteStretchingAddress → ℂ) (hface : Summable face) :
    (∑' address : CompleteStretchingAddress, face address) =
      (∑' sector : {triad // AdvectingLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // TransportedLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      (∑' sector : {triad // ReceiverLowSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1)) +
      ∑' sector : {triad // ComparableSector triad},
        face (completeStretchingAddressEquivTriad.symm sector.1) := by
  have htriad : Summable
      (fun triad ↦ face (completeStretchingAddressEquivTriad.symm triad)) := by
    exact (completeStretchingAddressEquivTriad.symm.summable_iff).mpr hface
  calc
    (∑' address : CompleteStretchingAddress, face address) =
        ∑' triad : AddressedClosedFourierTriad,
          face (completeStretchingAddressEquivTriad.symm triad) :=
      (completeStretchingAddressEquivTriad.symm.tsum_eq face).symm
    _ = _ := tsum_closedTriad_eq_fourSectors _ htriad

/-! ## Transport exchange laws -/

@[simp]
theorem completeTransportTriad_exchange_advecting
    (address : CompleteTransportAddress) :
    (completeTransportTriad (completeTransportExchange address)).advecting =
      (completeTransportTriad address).advecting := rfl

@[simp]
theorem completeTransportTriad_exchange_transported
    (address : CompleteTransportAddress) :
    (completeTransportTriad (completeTransportExchange address)).transported =
      (completeTransportTriad address).receiver := rfl

@[simp]
theorem completeTransportTriad_exchange_receiver
    (address : CompleteTransportAddress) :
    (completeTransportTriad (completeTransportExchange address)).receiver =
      (completeTransportTriad address).transported := by
  exact completeTransportReceiver_exchange address

theorem completeTransportExchange_advectingLow_iff
    (address : CompleteTransportAddress) :
    AdvectingLowSector (completeTransportTriad (completeTransportExchange address)) ↔
      AdvectingLowSector (completeTransportTriad address) := by
  simp only [AdvectingLowSector, advectingGrade, transportedGrade, receiverGrade,
    completeTransportTriad_exchange_advecting, completeTransportTriad_exchange_transported,
    completeTransportTriad_exchange_receiver]
  constructor <;> rintro ⟨hleft, hright⟩ <;> exact ⟨hright, hleft⟩

theorem completeTransportExchange_transportedLow_iff_receiverLow
    (address : CompleteTransportAddress) :
    TransportedLowSector (completeTransportTriad (completeTransportExchange address)) ↔
      ReceiverLowSector (completeTransportTriad address) := by
  simp only [TransportedLowSector, ReceiverLowSector, advectingGrade, transportedGrade,
    receiverGrade, completeTransportTriad_exchange_advecting,
    completeTransportTriad_exchange_transported, completeTransportTriad_exchange_receiver]

theorem completeTransportExchange_receiverLow_iff_transportedLow
    (address : CompleteTransportAddress) :
    ReceiverLowSector (completeTransportTriad (completeTransportExchange address)) ↔
      TransportedLowSector (completeTransportTriad address) := by
  simp only [TransportedLowSector, ReceiverLowSector, advectingGrade, transportedGrade,
    receiverGrade, completeTransportTriad_exchange_advecting,
    completeTransportTriad_exchange_transported, completeTransportTriad_exchange_receiver]

theorem completeTransportExchange_comparable_iff
    (address : CompleteTransportAddress) :
    ComparableSector (completeTransportTriad (completeTransportExchange address)) ↔
      ComparableSector (completeTransportTriad address) := by
  unfold ComparableSector
  rw [completeTransportExchange_advectingLow_iff,
    completeTransportExchange_transportedLow_iff_receiverLow,
    completeTransportExchange_receiverLow_iff_transportedLow]
  aesop

section Audit

#print axioms frequencyDyadicGrade_eq_zero_iff
#print axioms frequencyDyadicGrade_eq_succ_iff
#print axioms completeTransportAddressEquivTriad
#print axioms completeStretchingAddressEquivTriad
#print axioms advectingLowSector_highGrades_proximate
#print axioms transportedLowSector_highGrades_proximate
#print axioms receiverLowSector_highGrades_proximate
#print axioms comparableSector_gradeDiameter_le_one
#print axioms triadSectorEquiv
#print axioms tsum_closedTriad_eq_fourSectors
#print axioms tsum_completeTransportAddress_eq_fourSectors
#print axioms tsum_completeStretchingAddress_eq_fourSectors
#print axioms completeTransportExchange_comparable_iff

end Audit

end Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
