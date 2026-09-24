import ElementaryHolonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
import ElementaryHolonics.Millennium.NavierStokesH2LowVelocitySliceConversion

/-!
# The physical H2 comparable residue by exact grade fibres

**[proved-derived; formal-checked]**  The comparable part of the literal common-cube physical
`H2` current is decomposed before norms by the maximum of its three least dyadic grades.  On each
such fibre every pin has either the maximum grade or its immediate predecessor.  This is the
critical comparable-scale geometry: unlike a unique-low sector, it supplies no small low/high
ratio.

For an open `H3` solution the norm population on the complete comparable fibres is nevertheless
an actual summable kernel.  Every finite common-cube comparable current is bounded by the sum of
the finitely occupied grade kernels and hence by one radius-independent complete kernel.  The
bound uses the already proved absolute summability of the literal completed-multiplier velocity
faces; it does not postulate a shell majorant or assert cancellation.  The remaining analytic
boundary is a quantitative comparison of this complete kernel with the viscous `H3` dissipation
receiver strong enough for absorption.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableResidueBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The exact comparable grade -/

/-- Maximum least-dyadic grade of the three pins.  This is a receiver coordinate on the closed
triad, not an identification of its three pin occurrences. -/
def comparableTopGrade (triad : AddressedClosedFourierTriad) : ℕ :=
  max (advectingGrade triad) (max (transportedGrade triad) (receiverGrade triad))

theorem comparableSector_pinGrades_le_top
    {triad : AddressedClosedFourierTriad} (_hsector : ComparableSector triad) :
    advectingGrade triad ≤ comparableTopGrade triad ∧
      transportedGrade triad ≤ comparableTopGrade triad ∧
      receiverGrade triad ≤ comparableTopGrade triad := by
  unfold comparableTopGrade
  exact ⟨Nat.le_max_left _ _,
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _),
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)⟩

/-- Every comparable pin lies at most one grade below the maximum. -/
theorem comparableSector_top_le_pinGrades_add_one
    {triad : AddressedClosedFourierTriad} (hsector : ComparableSector triad) :
    comparableTopGrade triad ≤ advectingGrade triad + 1 ∧
      comparableTopGrade triad ≤ transportedGrade triad + 1 ∧
      comparableTopGrade triad ≤ receiverGrade triad + 1 := by
  rcases comparableSector_gradeDiameter_le_one hsector with
    ⟨hat, hta, har, hra, htr, hrt⟩
  unfold comparableTopGrade
  constructor
  · exact max_le (Nat.le_add_right _ _) (max_le hta hra)
  constructor
  · exact max_le hat (max_le (Nat.le_add_right _ _) hrt)
  · exact max_le har (max_le htr (Nat.le_add_right _ _))

/-- The two adjacent grade slices carrying one comparable maximum-grade fibre. -/
def comparableGradePinSlice (topGrade : ℕ) : Finset SpatialFrequency :=
  frequencyDyadicGradeSlice topGrade ∪ frequencyDyadicPredecessorSlice topGrade

theorem comparableSector_pin_mem_topSlice
    {triad : AddressedClosedFourierTriad} (hsector : ComparableSector triad) :
    triad.advecting ∈ comparableGradePinSlice (comparableTopGrade triad) ∧
      triad.transported ∈ comparableGradePinSlice (comparableTopGrade triad) ∧
      triad.receiver ∈ comparableGradePinSlice (comparableTopGrade triad) := by
  rcases comparableSector_pinGrades_le_top hsector with ⟨ha, ht, hr⟩
  rcases comparableSector_top_le_pinGrades_add_one hsector with ⟨ha', ht', hr'⟩
  have pin_mem (frequency : SpatialFrequency) (hgrade : frequencyDyadicGrade frequency ≤
      comparableTopGrade triad) (htop : comparableTopGrade triad ≤
        frequencyDyadicGrade frequency + 1) :
      frequency ∈ comparableGradePinSlice (comparableTopGrade triad) := by
    unfold comparableGradePinSlice
    rw [Finset.mem_union]
    by_cases heq : frequencyDyadicGrade frequency = comparableTopGrade triad
    · exact Or.inl ((mem_frequencyDyadicGradeSlice_iff _ _).mpr heq)
    · right
      apply (mem_frequencyDyadicPredecessorSlice_iff _ _).mpr
      omega
  exact ⟨pin_mem triad.advecting ha ha',
    pin_mem triad.transported ht ht', pin_mem triad.receiver hr hr'⟩

/-! ## Signed finite grade decomposition -/

/-- The occupied maximum-grade coordinates of the actual finite comparable aperture. -/
def finitePhysicalH2ComparableGradeSet (radius : ℕ) : Finset ℕ := by
  classical
  exact (finitePhysicalH2ComparableAperture radius).image fun address ↦
    comparableTopGrade (completeTransportTriad address)

/-- One exact signed maximum-grade fibre of the finite comparable current. -/
def finitePhysicalH2ComparableGradeCurrent
    (radius topGrade : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ := by
  classical
  exact ∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
      (fun address ↦ comparableTopGrade (completeTransportTriad address) = topGrade),
    physicalH2VelocityExchangedTriadFace velocityMode address

/-- Exact grade decomposition of the finite signed comparable current, before any norm. -/
theorem finitePhysicalH2ComparableCurrent_eq_sum_gradeCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2ComparableCurrent radius velocityMode =
      ∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        finitePhysicalH2ComparableGradeCurrent radius topGrade velocityMode := by
  classical
  unfold finitePhysicalH2ComparableCurrent finitePhysicalH2ComparableGradeCurrent
    finitePhysicalH2ComparableGradeSet
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro address haddress
  have hgrade : comparableTopGrade (completeTransportTriad address) ∈
      (finitePhysicalH2ComparableAperture radius).image
        (fun other ↦ comparableTopGrade (completeTransportTriad other)) :=
    Finset.mem_image.mpr ⟨address, haddress, rfl⟩
  rw [Finset.sum_eq_single
    (comparableTopGrade (completeTransportTriad address))]
  · simp
  · intro other hother hne
    simp only [ite_eq_right_iff]
    intro heq
    exact (hne heq.symm).elim
  · exact fun hnot ↦ (hnot hgrade).elim

/-! ## Exact exchange retained on every grade fibre -/

@[simp]
theorem comparableTopGrade_exchange (address : CompleteTransportAddress) :
    comparableTopGrade (completeTransportTriad (completeTransportExchange address)) =
      comparableTopGrade (completeTransportTriad address) := by
  simp only [comparableTopGrade, advectingGrade, transportedGrade, receiverGrade,
    completeTransportTriad_exchange_advecting,
    completeTransportTriad_exchange_transported,
    completeTransportTriad_exchange_receiver]
  rw [max_comm (frequencyDyadicGrade (completeTransportTriad address).receiver)]

theorem completeTransportExchange_mem_finitePhysicalH2ComparableGradeAperture_iff
    (radius topGrade : ℕ) (address : CompleteTransportAddress) :
    completeTransportExchange address ∈
        (finitePhysicalH2ComparableAperture radius).filter
          (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade) ↔
      address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦
          comparableTopGrade (completeTransportTriad current) = topGrade) := by
  unfold finitePhysicalH2ComparableAperture
  simp only [Finset.mem_filter,
    completeTransportExchange_mem_physicalH2VelocityTriadAperture_iff,
    completeTransportExchange_comparable_iff, comparableTopGrade_exchange]

/-- Exchange reindexes one exact comparable grade fibre without taking a norm. -/
theorem sum_finitePhysicalH2ComparableGradeAperture_exchange
    {M : Type*} [AddCommMonoid M] (radius topGrade : ℕ)
    (face : CompleteTransportAddress → M) :
    (∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
        face (completeTransportExchange address)) =
      ∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
        face address := by
  exact Finset.sum_equiv completeTransportExchange
    (fun address ↦
      (completeTransportExchange_mem_finitePhysicalH2ComparableGradeAperture_iff
        radius topGrade address).symm)
    (fun _address _haddress ↦ rfl)

/-- Receiver-weighted half of one exact comparable grade current. -/
def finiteReceiverWeightedPhysicalH2ComparableGradeCurrent
    (radius topGrade : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ := by
  classical
  exact ∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
      (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
    receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode address

/-- The signed exchange identity survives the comparable restriction and the exact grade
restriction: the receiver-weighted current is negative one half of the completed current. -/
theorem finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_eq_neg_half_exchanged
    (radius topGrade : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    finiteReceiverWeightedPhysicalH2ComparableGradeCurrent
        radius topGrade velocityMode =
      -(1 / 2 : ℂ) *
        finitePhysicalH2ComparableGradeCurrent radius topGrade velocityMode := by
  classical
  let aperture := (finitePhysicalH2ComparableAperture radius).filter
    (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade)
  have htransport :
      (∑ address ∈ aperture,
          transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address) =
        -(∑ address ∈ aperture,
          receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode address) := by
    have hreindex := sum_finitePhysicalH2ComparableGradeAperture_exchange
      radius topGrade (receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode)
    change (∑ address ∈ aperture,
        receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode
          (completeTransportExchange address)) = _ at hreindex
    rw [← hreindex, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro address haddress
    rw [receiverWeightedPhysicalH2VelocityAdvectionFace_exchange]
    · simp
    · exact hdivergence address.1
        ((mem_physicalH2VelocityTriadAperture_iff radius address).mp
          ((Finset.mem_filter.mp (Finset.mem_filter.mp haddress).1).1)).1
  have hexchange :
      finitePhysicalH2ComparableGradeCurrent radius topGrade velocityMode =
        (∑ address ∈ aperture,
          transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address) -
        ∑ address ∈ aperture,
          receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode address := by
    unfold finitePhysicalH2ComparableGradeCurrent
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro address haddress
    exact physicalH2VelocityExchangedTriadFace_eq_transported_sub_receiver
      velocityMode address
      (hdivergence address.1
        ((mem_physicalH2VelocityTriadAperture_iff radius address).mp
          ((Finset.mem_filter.mp (Finset.mem_filter.mp haddress).1).1)).1)
  unfold finiteReceiverWeightedPhysicalH2ComparableGradeCurrent
  rw [hexchange, htransport]
  ring

/-! ## Complete comparable grade population -/

abbrev PhysicalH2ComparableAddress :=
  {address : CompleteTransportAddress //
    ComparableSector (completeTransportTriad address)}

abbrev PhysicalH2ComparableGradeAddress (topGrade : ℕ) :=
  {address : PhysicalH2ComparableAddress //
    comparableTopGrade (completeTransportTriad address.1) = topGrade}

/-- Comparable addresses are exactly the sigma population of their maximum-grade fibres. -/
def physicalH2ComparableGradeEquiv :
    PhysicalH2ComparableAddress ≃
      Σ topGrade : ℕ, PhysicalH2ComparableGradeAddress topGrade where
  toFun address := ⟨comparableTopGrade (completeTransportTriad address.1),
    ⟨address, rfl⟩⟩
  invFun graded := graded.2.1
  left_inv := by intro address; rfl
  right_inv := by
    rintro ⟨topGrade, address, hgrade⟩
    subst topGrade
    rfl

/-- The actual complete receiver-weighted norm population on one comparable maximum-grade
fibre.  Exact exchange turns this into the completed-current bound with the visible factor two. -/
def physicalH2ComparableGradeKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Set.Ioo 0 T) (topGrade : ℕ) : ℝ :=
  ∑' address : PhysicalH2ComparableGradeAddress topGrade,
    ‖receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address.1.1‖

theorem physicalH2ComparableGradeKernel_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (topGrade : ℕ) :
    0 ≤ physicalH2ComparableGradeKernel solution t topGrade := by
  exact tsum_nonneg fun _ ↦ norm_nonneg _

/-- Absolute summability of the literal receiver-weighted open `H3` population descends to every
comparable maximum-grade fibre. -/
theorem summable_norm_receiverWeightedPhysicalH2ComparableGradeFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (topGrade : ℕ) :
    Summable fun address : PhysicalH2ComparableGradeAddress topGrade ↦
      ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address.1.1‖ := by
  have hfull :=
    summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t
  exact (hfull.subtype
    {address : CompleteTransportAddress |
      ComparableSector (completeTransportTriad address)}).subtype
        {address : PhysicalH2ComparableAddress |
          comparableTopGrade (completeTransportTriad address.1) = topGrade}

/-- The maximum-grade kernel is itself summable.  This is an unconditional consequence of the
actual open-solution `H3` population, rather than a summability premise attached to an invented
shell sequence. -/
theorem summable_physicalH2ComparableGradeKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable (physicalH2ComparableGradeKernel solution t) := by
  let face : PhysicalH2ComparableAddress → ℝ := fun address ↦
    ‖receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address.1‖
  have hface : Summable face :=
    (summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
      solution t).subtype
        {address : CompleteTransportAddress |
          ComparableSector (completeTransportTriad address)}
  let reindex := physicalH2ComparableGradeEquiv
  have hreindexed : Summable (fun graded ↦ face (reindex.symm graded)) :=
    (reindex.symm.summable_iff).mpr hface
  change Summable (fun topGrade : ℕ ↦
    ∑' address : PhysicalH2ComparableGradeAddress topGrade,
      ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address.1.1‖)
  convert hreindexed.sigma using 1 <;> rfl

/-- Reindexing the complete comparable norm population by maximum grade retains every address
occurrence exactly. -/
theorem tsum_norm_receiverWeightedPhysicalH2Comparable_eq_gradeKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    (∑' address : PhysicalH2ComparableAddress,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address.1‖) =
      ∑' topGrade : ℕ, physicalH2ComparableGradeKernel solution t topGrade := by
  let face : PhysicalH2ComparableAddress → ℝ := fun address ↦
    ‖receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t) address.1‖
  have hface : Summable face :=
    (summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
      solution t).subtype
        {address : CompleteTransportAddress |
          ComparableSector (completeTransportTriad address)}
  let reindex := physicalH2ComparableGradeEquiv
  have hreindexed : Summable (fun graded ↦ face (reindex.symm graded)) :=
    (reindex.symm.summable_iff).mpr hface
  calc
    (∑' address : PhysicalH2ComparableAddress, face address) =
        ∑' graded : Σ topGrade : ℕ,
          PhysicalH2ComparableGradeAddress topGrade,
          face (reindex.symm graded) :=
      (reindex.symm.tsum_eq face).symm
    _ = ∑' topGrade : ℕ,
        ∑' address : PhysicalH2ComparableGradeAddress topGrade,
          face address.1 := by
      rw [hreindexed.tsum_sigma]
      rfl
    _ = ∑' topGrade : ℕ,
        physicalH2ComparableGradeKernel solution t topGrade := rfl

/-! ## Finite fibres inside the complete kernel -/

/-- The source subtype of one finite comparable grade aperture. -/
abbrev FinitePhysicalH2ComparableGradeAddress (radius topGrade : ℕ) :=
  {address : CompleteTransportAddress //
    address ∈ (finitePhysicalH2ComparableAperture radius).filter
      (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade)}

/-- Placement of a finite occurrence into the complete comparable fibre with the same address. -/
def finitePhysicalH2ComparableGradePlacement (radius topGrade : ℕ) :
    FinitePhysicalH2ComparableGradeAddress radius topGrade ↪
      PhysicalH2ComparableGradeAddress topGrade := by
  classical
  exact
    { toFun := fun address ↦
        ⟨⟨address.1,
          (Finset.mem_filter.mp
            (Finset.mem_filter.mp address.2).1).2⟩,
          (Finset.mem_filter.mp address.2).2⟩
      inj' := by
        intro left right heq
        apply Subtype.coe_injective
        exact congrArg (fun placed : PhysicalH2ComparableGradeAddress topGrade ↦
          placed.1.1) heq }

/-- The actual finite grade aperture, with each occurrence placed in the corresponding complete
comparable grade fibre. -/
def finitePhysicalH2ComparableGradeFiberAperture
    (radius topGrade : ℕ) :
    Finset (PhysicalH2ComparableGradeAddress topGrade) := by
  classical
  exact ((finitePhysicalH2ComparableAperture radius).filter
    (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade)).attach.map
      (finitePhysicalH2ComparableGradePlacement radius topGrade)

theorem sum_norm_receiverWeighted_finiteComparableGrade_eq_fiberAperture
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    (∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖) =
      ∑ address ∈ finitePhysicalH2ComparableGradeFiberAperture radius topGrade,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address.1.1‖ := by
  classical
  rw [show finitePhysicalH2ComparableGradeFiberAperture radius topGrade =
      ((finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade)).attach.map
          (finitePhysicalH2ComparableGradePlacement radius topGrade) by rfl,
    Finset.sum_map]
  change _ = ∑ address ∈
      ((finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade)).attach,
      ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address.1‖
  exact (Finset.sum_attach
    ((finitePhysicalH2ComparableAperture radius).filter
      (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade))
    (fun address ↦
      ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address‖)).symm

/-- One finite receiver-weighted grade current is controlled by its actual complete grade
population. -/
theorem norm_finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_le_kernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    ‖finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      physicalH2ComparableGradeKernel solution t topGrade := by
  unfold finiteReceiverWeightedPhysicalH2ComparableGradeCurrent
  calc
    ‖∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
        receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖ ≤
      ∑ address ∈ (finitePhysicalH2ComparableAperture radius).filter
        (fun current ↦ comparableTopGrade (completeTransportTriad current) = topGrade),
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖ := by
      exact norm_sum_le _ _
    _ = ∑ address ∈ finitePhysicalH2ComparableGradeFiberAperture radius topGrade,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address.1.1‖ :=
      sum_norm_receiverWeighted_finiteComparableGrade_eq_fiberAperture
        solution t radius topGrade
    _ ≤ ∑' address : PhysicalH2ComparableGradeAddress topGrade,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address.1.1‖ :=
      (summable_norm_receiverWeightedPhysicalH2ComparableGradeFace
        solution t topGrade).sum_le_tsum
          (finitePhysicalH2ComparableGradeFiberAperture radius topGrade)
          (fun _address _haddress ↦ norm_nonneg _)
    _ = physicalH2ComparableGradeKernel solution t topGrade := rfl

/-- The completed finite grade current pays exactly the factor two returned by transport/
receiver exchange, then enters the complete summable grade kernel. -/
theorem norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_two_mul_kernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      2 * physicalH2ComparableGradeKernel solution t topGrade := by
  have hexchange :=
    finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_eq_neg_half_exchanged
      radius topGrade (openPeriodicVelocityFourierMode solution t)
      (fun frequency _hfrequency ↦
        openPeriodicVelocityFourierMode_divergenceFree solution t frequency)
  have hcurrent :
      finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t) =
        -(2 : ℂ) *
          finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
            (openPeriodicVelocityFourierMode solution t) := by
    rw [hexchange]
    ring
  calc
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ =
      2 * ‖finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ := by
      rw [hcurrent, norm_mul]
      norm_num
    _ ≤ 2 * physicalH2ComparableGradeKernel solution t topGrade :=
      mul_le_mul_of_nonneg_left
        (norm_finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_le_kernel
          solution t radius topGrade) (by norm_num)

/-! ## Cofinal-uniform complete population bound -/

/-- The complete comparable receiver population, including the exact exchange factor two needed
to return to the completed physical current. -/
def physicalH2ComparableCompleteKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' topGrade : ℕ, 2 * physicalH2ComparableGradeKernel solution t topGrade

theorem summable_two_mul_physicalH2ComparableGradeKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun topGrade : ℕ ↦
      2 * physicalH2ComparableGradeKernel solution t topGrade :=
  (summable_physicalH2ComparableGradeKernel solution t).mul_left 2

theorem physicalH2ComparableCompleteKernel_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ physicalH2ComparableCompleteKernel solution t := by
  exact tsum_nonneg fun topGrade ↦ mul_nonneg (by norm_num)
    (physicalH2ComparableGradeKernel_nonneg solution t topGrade)

/-- First finite receiver: only maximum grades actually occupied by this common cube are paid. -/
theorem norm_finiteOpenPhysicalH2ComparableCurrent_le_occupiedGradeKernels
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    ‖finitePhysicalH2ComparableCurrent radius
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      ∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        2 * physicalH2ComparableGradeKernel solution t topGrade := by
  rw [finitePhysicalH2ComparableCurrent_eq_sum_gradeCurrent]
  calc
    ‖∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ ≤
      ∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        2 * physicalH2ComparableGradeKernel solution t topGrade := by
      exact Finset.sum_le_sum fun topGrade _hgrade ↦
        norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_two_mul_kernel
          solution t radius topGrade

/-- **Radius-independent comparable bound.**  Every common-cube comparable current is controlled
by one actual complete summable population.  Thus taking the cofinal cube radius introduces no
new comparable-population constant. -/
theorem norm_finiteOpenPhysicalH2ComparableCurrent_le_completeKernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    ‖finitePhysicalH2ComparableCurrent radius
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      physicalH2ComparableCompleteKernel solution t := by
  apply (norm_finiteOpenPhysicalH2ComparableCurrent_le_occupiedGradeKernels
    solution t radius).trans
  unfold physicalH2ComparableCompleteKernel
  exact (summable_two_mul_physicalH2ComparableGradeKernel solution t).sum_le_tsum
    (finitePhysicalH2ComparableGradeSet radius)
    (fun topGrade _hgrade ↦ mul_nonneg (by norm_num)
      (physicalH2ComparableGradeKernel_nonneg solution t topGrade))

/-! ## Kernel audit -/

#print axioms comparableSector_pin_mem_topSlice
#print axioms finitePhysicalH2ComparableCurrent_eq_sum_gradeCurrent
#print axioms finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_eq_neg_half_exchanged
#print axioms summable_physicalH2ComparableGradeKernel
#print axioms tsum_norm_receiverWeightedPhysicalH2Comparable_eq_gradeKernel
#print axioms norm_finiteOpenPhysicalH2ComparableCurrent_le_completeKernel

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableResidueBound
