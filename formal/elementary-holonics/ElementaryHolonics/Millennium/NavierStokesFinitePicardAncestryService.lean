import ElementaryHolonics.Millennium.NavierStokesFinitePicardVolterraMass

/-!
# Finite-horizon Picard ancestry and its exact service coefficient

**[proved-derived; formal-checked]** A terminal finite receiver is expanded backwards through a
declared number of quadratic generations.  Every layer retains the previous addresses, every
advecting aperture address, and every transported parent `output - parent` needed by the next
Picard source.  This is a finite causal cone, not a claim that a nontrivial finite subset of the
integer lattice is closed under arbitrarily many interactions.

The projected interaction is calibrated by its action on the nine coordinate-atom pairs.  That
finite operator cost, together with the actual low and marked masses on the next ancestry layer,
gives an explicit service bound.  Composing it with the marked Volterra owner yields a genuine
one-step finite-horizon recurrence.  The repeated restart and quadratic marked payment remain
visible; no factorial suppression, terminal estimate, or regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesFinitePicardAncestryService

open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
open Soma.Holonics.Millennium.NavierStokesFinitePicardVolterraMass
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The finite backward address cone -/

/-- Every transported parent address requested by a finite output receiver and aperture. -/
def finiteTransportedParentReceiver
    (outputs aperture : Finset SpatialFrequency) : Finset SpatialFrequency :=
  outputs.biUnion fun output ↦ aperture.image (transportedFrequencyAt output)

/-- The cumulative backward causal cone through a declared number of quadratic generations. -/
def finiteHorizonAncestryReceiver
    (aperture terminal : Finset SpatialFrequency) : ℕ → Finset SpatialFrequency
  | 0 => terminal
  | horizon + 1 =>
      (finiteHorizonAncestryReceiver aperture terminal horizon ∪ aperture) ∪
        finiteTransportedParentReceiver
          (finiteHorizonAncestryReceiver aperture terminal horizon) aperture

theorem finiteHorizonAncestryReceiver_mono_step
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ) :
    finiteHorizonAncestryReceiver aperture terminal horizon ⊆
      finiteHorizonAncestryReceiver aperture terminal (horizon + 1) := by
  intro frequency hfrequency
  simp only [finiteHorizonAncestryReceiver, Finset.mem_union]
  exact Or.inl (Or.inl hfrequency)

theorem aperture_subset_finiteHorizonAncestryReceiver_succ
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ) :
    aperture ⊆ finiteHorizonAncestryReceiver aperture terminal (horizon + 1) := by
  intro frequency hfrequency
  simp only [finiteHorizonAncestryReceiver, Finset.mem_union]
  exact Or.inl (Or.inr hfrequency)

theorem transported_parent_mem_finiteHorizonAncestryReceiver_succ
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    {output parent : SpatialFrequency}
    (houtput : output ∈ finiteHorizonAncestryReceiver aperture terminal horizon)
    (hparent : parent ∈ aperture) :
    transportedFrequencyAt output parent ∈
      finiteHorizonAncestryReceiver aperture terminal (horizon + 1) := by
  simp only [finiteHorizonAncestryReceiver, Finset.mem_union]
  right
  unfold finiteTransportedParentReceiver
  rw [Finset.mem_biUnion]
  exact ⟨output, houtput, Finset.mem_image.2 ⟨parent, hparent, rfl⟩⟩

theorem terminal_subset_finiteHorizonAncestryReceiver
    (aperture terminal : Finset SpatialFrequency) :
    ∀ horizon, terminal ⊆ finiteHorizonAncestryReceiver aperture terminal horizon := by
  intro horizon
  induction horizon with
  | zero => exact fun _ hfrequency ↦ hfrequency
  | succ horizon inductionHypothesis =>
      exact Finset.Subset.trans inductionHypothesis
        (finiteHorizonAncestryReceiver_mono_step aperture terminal horizon)

/-! ## Exact finite coordinate-atom calibration -/

/-- The canonical coordinate atom used only to measure the already-founded interaction. -/
def complexVectorCoordinateAtom (component : Fin 3) : ComplexVector :=
  Pi.single component 1

/-- The complete nine-atom operator cost at one addressed projected interaction. -/
def finiteProjectedInteractionAtomCost
    (output parent : SpatialFrequency) : ℝ≥0∞ :=
  ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
    ‖lerayProjectMode output
      (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
        (complexVectorCoordinateAtom advectingComponent)
        (complexVectorCoordinateAtom transportedComponent))‖ₑ

theorem finiteProjectedInteractionAtomCost_ne_top
    (output parent : SpatialFrequency) :
    finiteProjectedInteractionAtomCost output parent ≠ ∞ := by
  unfold finiteProjectedInteractionAtomCost
  apply ENNReal.sum_ne_top.2
  intro _advectingComponent _hadvectingComponent
  apply ENNReal.sum_ne_top.2
  exact fun _transportedComponent _htransportedComponent ↦ enorm_ne_top

private theorem lerayProjectMode_add
    (output : SpatialFrequency) (left right : ComplexVector) :
    lerayProjectMode output (left + right) =
      lerayProjectMode output left + lerayProjectMode output right := by
  by_cases houtput : output = 0
  · subst output
    simp
  · rw [lerayProjectMode, if_neg houtput, lerayProjectMode, if_neg houtput,
      lerayProjectMode, if_neg houtput]
    ext component
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      complexDot, dotProduct_add]
    ring

private theorem lerayProjectMode_smul
    (amplitude : ℂ) (output : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectMode output (amplitude • mode) =
      amplitude • lerayProjectMode output mode := by
  by_cases houtput : output = 0
  · subst output
    simp
  · rw [lerayProjectMode, if_neg houtput, lerayProjectMode, if_neg houtput]
    ext component
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexDot,
      dotProduct_smul]
    ring

private theorem complexAdvectiveInteraction_add_advecting
    (parent transported : SpatialFrequency)
    (left right transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported (left + right) transportedMode =
      complexAdvectiveInteraction parent transported left transportedMode +
        complexAdvectiveInteraction parent transported right transportedMode := by
  unfold complexAdvectiveInteraction
  simp only [complexDot, dotProduct_add]
  module

private theorem complexAdvectiveInteraction_smul_advecting
    (parent transported : SpatialFrequency) (amplitude : ℂ)
    (advectingMode transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported
        (amplitude • advectingMode) transportedMode =
      amplitude • complexAdvectiveInteraction parent transported
        advectingMode transportedMode := by
  unfold complexAdvectiveInteraction
  simp only [complexDot, dotProduct_smul]
  module

private theorem complexAdvectiveInteraction_add_transported
    (parent transported : SpatialFrequency)
    (advectingMode left right : ComplexVector) :
    complexAdvectiveInteraction parent transported advectingMode (left + right) =
      complexAdvectiveInteraction parent transported advectingMode left +
        complexAdvectiveInteraction parent transported advectingMode right := by
  unfold complexAdvectiveInteraction
  module

private theorem complexAdvectiveInteraction_sum_advecting
    (parent transported : SpatialFrequency) (terms : Fin 3 → ComplexVector)
    (transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported
        (∑ component, terms component) transportedMode =
      ∑ component, complexAdvectiveInteraction parent transported
        (terms component) transportedMode := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp [complexAdvectiveInteraction, complexDot]
  | @insert component remaining hcomponent inductionHypothesis =>
      rw [Finset.sum_insert hcomponent, Finset.sum_insert hcomponent,
        complexAdvectiveInteraction_add_advecting, inductionHypothesis]

private theorem complexAdvectiveInteraction_sum_transported
    (parent transported : SpatialFrequency) (advectingMode : ComplexVector)
    (terms : Fin 3 → ComplexVector) :
    complexAdvectiveInteraction parent transported advectingMode
        (∑ component, terms component) =
      ∑ component, complexAdvectiveInteraction parent transported
        advectingMode (terms component) := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp [complexAdvectiveInteraction]
  | @insert component remaining hcomponent inductionHypothesis =>
      rw [Finset.sum_insert hcomponent, Finset.sum_insert hcomponent,
        complexAdvectiveInteraction_add_transported, inductionHypothesis]

private theorem lerayProjectMode_sum
    (output : SpatialFrequency) (terms : Fin 3 → ComplexVector) :
    lerayProjectMode output (∑ component, terms component) =
      ∑ component, lerayProjectMode output (terms component) := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty =>
      by_cases houtput : output = 0
      · subst output
        simp
      · simp [lerayProjectMode, houtput, complexDot]
  | @insert component remaining hcomponent inductionHypothesis =>
      rw [Finset.sum_insert hcomponent, Finset.sum_insert hcomponent,
        lerayProjectMode_add, inductionHypothesis]

private theorem projectedInteraction_eq_atomExpansion
    (output parent : SpatialFrequency) (advecting transported : ComplexVector) :
    lerayProjectMode output
        (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          advecting transported) =
      ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
        (advecting advectingComponent * transported transportedComponent) •
          lerayProjectMode output
            (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
              (complexVectorCoordinateAtom advectingComponent)
              (complexVectorCoordinateAtom transportedComponent)) := by
  rw [pi_eq_sum_univ' advecting, pi_eq_sum_univ' transported,
    complexAdvectiveInteraction_sum_advecting]
  simp_rw [complexAdvectiveInteraction_smul_advecting,
    complexAdvectiveInteraction_sum_transported,
    complexAdvectiveInteraction_smul_transported]
  rw [lerayProjectMode_sum]
  simp_rw [lerayProjectMode_smul, lerayProjectMode_sum]
  simp_rw [lerayProjectMode_smul, Finset.smul_sum, smul_smul]
  simp [complexVectorCoordinateAtom, Finset.sum_apply, Pi.single_apply]

theorem enorm_projectedInteraction_le_atomCost
    (output parent : SpatialFrequency) (advecting transported : ComplexVector) :
    ‖lerayProjectMode output
        (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          advecting transported)‖ₑ ≤
      finiteProjectedInteractionAtomCost output parent *
        ‖advecting‖ₑ * ‖transported‖ₑ := by
  rw [projectedInteraction_eq_atomExpansion]
  calc
    ‖∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
        (advecting advectingComponent * transported transportedComponent) •
          lerayProjectMode output
            (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
              (complexVectorCoordinateAtom advectingComponent)
              (complexVectorCoordinateAtom transportedComponent))‖ₑ ≤
        ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
          ‖(advecting advectingComponent * transported transportedComponent) •
            lerayProjectMode output
              (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                (complexVectorCoordinateAtom advectingComponent)
                (complexVectorCoordinateAtom transportedComponent))‖ₑ := by
      exact (enorm_sum_le _ _).trans
        (Finset.sum_le_sum fun _advectingComponent _hadvectingComponent ↦
          enorm_sum_le _ _)
    _ ≤ finiteProjectedInteractionAtomCost output parent *
          ‖advecting‖ₑ * ‖transported‖ₑ := by
      unfold finiteProjectedInteractionAtomCost
      simp_rw [enorm_smul, enorm_mul]
      have hadvecting (component : Fin 3) :
          ‖advecting component‖ₑ ≤ ‖advecting‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
        rw [Pi.nnnorm_def]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun index ↦ ‖advecting index‖₊) (Finset.mem_univ component)
      have htransported (component : Fin 3) :
          ‖transported component‖ₑ ≤ ‖transported‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
        rw [Pi.nnnorm_def]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun index ↦ ‖transported index‖₊) (Finset.mem_univ component)
      calc
        (∑ i : Fin 3, ∑ j : Fin 3,
            ‖advecting i‖ₑ * ‖transported j‖ₑ *
              ‖lerayProjectMode output
                (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                  (complexVectorCoordinateAtom i)
                  (complexVectorCoordinateAtom j))‖ₑ) ≤
            ∑ i : Fin 3, ∑ j : Fin 3,
              (‖advecting‖ₑ * ‖transported‖ₑ) *
                ‖lerayProjectMode output
                  (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                    (complexVectorCoordinateAtom i)
                    (complexVectorCoordinateAtom j))‖ₑ := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul' (mul_le_mul' (hadvecting i) (htransported j)) le_rfl
        _ = _ := by
          let service := ‖advecting‖ₑ * ‖transported‖ₑ
          change (∑ i : Fin 3, ∑ j : Fin 3,
            service * ‖lerayProjectMode output
              (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                (complexVectorCoordinateAtom i)
                (complexVectorCoordinateAtom j))‖ₑ) = _
          simp_rw [mul_comm service]
          simp_rw [← Finset.sum_mul]
          dsimp [service]
          ac_rfl

/-! ## The finite aperture service law -/

/-- The operator cost paid by every aperture parent at one output address. -/
def finiteProjectedInteractionOutputCost
    (output : SpatialFrequency) (aperture : Finset SpatialFrequency) : ℝ≥0∞ :=
  ∑ parent ∈ aperture, finiteProjectedInteractionAtomCost output parent

theorem finiteProjectedInteractionOutputCost_ne_top
    (output : SpatialFrequency) (aperture : Finset SpatialFrequency) :
    finiteProjectedInteractionOutputCost output aperture ≠ ∞ := by
  unfold finiteProjectedInteractionOutputCost
  exact ENNReal.sum_ne_top.2 fun parent _hparent ↦
    finiteProjectedInteractionAtomCost_ne_top output parent

private theorem lerayProjectMode_finset_sum
    {index : Type*} [DecidableEq index]
    (output : SpatialFrequency) (addresses : Finset index)
    (terms : index → ComplexVector) :
    lerayProjectMode output (∑ address ∈ addresses, terms address) =
      ∑ address ∈ addresses, lerayProjectMode output (terms address) := by
  induction addresses using Finset.induction_on with
  | empty =>
      by_cases houtput : output = 0
      · subst output
        simp
      · simp [lerayProjectMode, houtput, complexDot]
  | @insert address addresses haddress inductionHypothesis =>
      rw [Finset.sum_insert haddress, Finset.sum_insert haddress,
        lerayProjectMode_add, inductionHypothesis]

/-- The complete finite projected coefficient is bounded by the sum of its addressed atom costs
times the actual two parent amplitudes. -/
theorem enorm_finiteProjectedAdvectiveCoefficient_le_atomPayments
    (aperture : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    ‖finiteProjectedAdvectiveCoefficient aperture advecting transported output‖ₑ ≤
      ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent * ‖advecting parent‖ₑ *
          ‖transported (transportedFrequencyAt output parent)‖ₑ := by
  unfold finiteProjectedAdvectiveCoefficient finiteAdvectiveCoefficient
  rw [lerayProjectMode_finset_sum]
  exact (enorm_sum_le _ _).trans
    (Finset.sum_le_sum fun parent _hparent ↦
      enorm_projectedInteraction_le_atomCost output parent
        (advecting parent) (transported (transportedFrequencyAt output parent)))

theorem enorm_mode_le_finiteFourierReceiverMass
    (receiver : Finset SpatialFrequency)
    (field : ComplexFourierModePopulation) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ receiver) :
    ‖field frequency‖ₑ ≤ finiteFourierReceiverMass receiver field := by
  unfold finiteFourierReceiverMass
  exact Finset.single_le_sum
    (fun address _haddress ↦ (zero_le : (0 : ℝ≥0∞) ≤ ‖field address‖ₑ)) hfrequency

/-- An output coefficient is paid by one finite output service cost and the two actual finite
receiver masses, provided that the receiver contains every addressed parent occurrence. -/
theorem enorm_finiteProjectedAdvectiveCoefficient_le_receiverService
    (aperture inputs : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation)
    (output : SpatialFrequency)
    (hadvecting : aperture ⊆ inputs)
    (htransported : ∀ parent ∈ aperture,
      transportedFrequencyAt output parent ∈ inputs) :
    ‖finiteProjectedAdvectiveCoefficient aperture advecting transported output‖ₑ ≤
      finiteProjectedInteractionOutputCost output aperture *
        finiteFourierReceiverMass inputs advecting *
        finiteFourierReceiverMass inputs transported := by
  calc
    ‖finiteProjectedAdvectiveCoefficient aperture advecting transported output‖ₑ ≤
        ∑ parent ∈ aperture,
          finiteProjectedInteractionAtomCost output parent * ‖advecting parent‖ₑ *
            ‖transported (transportedFrequencyAt output parent)‖ₑ :=
      enorm_finiteProjectedAdvectiveCoefficient_le_atomPayments
        aperture advecting transported output
    _ ≤ ∑ parent ∈ aperture,
          finiteProjectedInteractionAtomCost output parent *
            finiteFourierReceiverMass inputs advecting *
            finiteFourierReceiverMass inputs transported := by
      apply Finset.sum_le_sum
      intro parent hparent
      exact mul_le_mul'
        (mul_le_mul' le_rfl
          (enorm_mode_le_finiteFourierReceiverMass inputs advecting
            (hadvecting hparent)))
        (enorm_mode_le_finiteFourierReceiverMass inputs transported
          (htransported parent hparent))
    _ = _ := by
      unfold finiteProjectedInteractionOutputCost
      rw [Finset.sum_mul, Finset.sum_mul]

/-! ## The actual low/marked service on one ancestry layer -/

/-- Actual low-path mass on the next ancestry receiver. -/
def finiteHorizonPicardLowMass
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ) (sourceTime : ℝ) : ℝ≥0∞ :=
  finiteFourierReceiverMass
    (finiteHorizonAncestryReceiver aperture terminal (horizon + 1))
    (finiteHeatSeededPicardLowGeneration nu restartTime aperture
      baseRadius seed depth sourceTime)

/-- Actual marked-path mass on the next ancestry receiver. -/
def finiteHorizonPicardMarkedMass
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ) (sourceTime : ℝ) : ℝ≥0∞ :=
  finiteHeatSeededPicardMarkedHighMass
    (finiteHorizonAncestryReceiver aperture terminal (horizon + 1))
    nu restartTime aperture baseRadius seed depth sourceTime

/-- The strongest direct service payment produced here: the exact finite operator cost at one
output multiplied by the actual marked--low, low--marked, and marked--marked receiver masses. -/
def finiteHorizonPicardMarkedServiceAt
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (sourceTime : ℝ) (output : SpatialFrequency) : ℝ≥0∞ :=
  let lowMass := finiteHorizonPicardLowMass aperture terminal horizon
    nu restartTime baseRadius seed depth sourceTime
  let markedMass := finiteHorizonPicardMarkedMass aperture terminal horizon
    nu restartTime baseRadius seed depth sourceTime
  finiteProjectedInteractionOutputCost output aperture *
    (markedMass * lowMass + lowMass * markedMass + markedMass * markedMass)

theorem finiteHorizonPicardMarkedServiceAt_ne_top
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (sourceTime : ℝ) (output : SpatialFrequency) :
    finiteHorizonPicardMarkedServiceAt aperture terminal horizon nu restartTime
      baseRadius seed depth sourceTime output ≠ ∞ := by
  unfold finiteHorizonPicardMarkedServiceAt finiteHorizonPicardLowMass
    finiteHorizonPicardMarkedMass finiteHeatSeededPicardMarkedHighMass
  have hcost := finiteProjectedInteractionOutputCost_ne_top output aperture
  have hlow := finiteFourierReceiverMass_ne_top
    (finiteHorizonAncestryReceiver aperture terminal (horizon + 1))
    (finiteHeatSeededPicardLowGeneration nu restartTime aperture
      baseRadius seed depth sourceTime)
  have hmarked := finiteFourierReceiverMass_ne_top
    (finiteHorizonAncestryReceiver aperture terminal (horizon + 1))
    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
      baseRadius seed depth sourceTime)
  finiteness

/-- Every marked source mode on the current ancestry layer is paid by actual finite amplitudes on
the next layer.  All address-containment hypotheses are discharged by the cone construction. -/
theorem finiteHeatSeededPicardMarkedQuadraticModeMass_le_ancestryService
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (sourceTime : ℝ) {output : SpatialFrequency}
    (houtput : output ∈ finiteHorizonAncestryReceiver aperture terminal horizon) :
    finiteHeatSeededPicardMarkedQuadraticModeMass nu restartTime aperture
        baseRadius seed depth sourceTime output ≤
      finiteHorizonPicardMarkedServiceAt aperture terminal horizon nu restartTime
        baseRadius seed depth sourceTime output := by
  let inputs := finiteHorizonAncestryReceiver aperture terminal (horizon + 1)
  let low := finiteHeatSeededPicardLowGeneration nu restartTime aperture
    baseRadius seed depth sourceTime
  let marked := finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
    baseRadius seed depth sourceTime
  let lowMass := finiteFourierReceiverMass inputs low
  let markedMass := finiteFourierReceiverMass inputs marked
  have haperture : aperture ⊆ inputs :=
    aperture_subset_finiteHorizonAncestryReceiver_succ aperture terminal horizon
  have htransported : ∀ parent ∈ aperture,
      transportedFrequencyAt output parent ∈ inputs := by
    intro parent hparent
    exact transported_parent_mem_finiteHorizonAncestryReceiver_succ
      aperture terminal horizon houtput hparent
  have hmarkedLow := enorm_finiteProjectedAdvectiveCoefficient_le_receiverService
    aperture inputs marked low output haperture htransported
  have hlowMarked := enorm_finiteProjectedAdvectiveCoefficient_le_receiverService
    aperture inputs low marked output haperture htransported
  have hmarkedMarked := enorm_finiteProjectedAdvectiveCoefficient_le_receiverService
    aperture inputs marked marked output haperture htransported
  change
    ‖finiteProjectedAdvectiveCoefficient aperture marked low output‖ₑ +
        ‖finiteProjectedAdvectiveCoefficient aperture low marked output‖ₑ +
      ‖finiteProjectedAdvectiveCoefficient aperture marked marked output‖ₑ ≤
        finiteProjectedInteractionOutputCost output aperture *
          (markedMass * lowMass + lowMass * markedMass + markedMass * markedMass)
  calc
    _ ≤ (finiteProjectedInteractionOutputCost output aperture * markedMass * lowMass) +
          (finiteProjectedInteractionOutputCost output aperture * lowMass * markedMass) +
          (finiteProjectedInteractionOutputCost output aperture * markedMass * markedMass) :=
      add_le_add (add_le_add hmarkedLow hlowMarked) hmarkedMarked
    _ = _ := by ring

/-- The finite-horizon clock payment obtained by integrating the actual service at each retained
output.  No time supremum or generation-independent constant is introduced. -/
def finiteHorizonPicardMarkedServiceVolterraMass
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ) (targetTime : ℝ) : ℝ≥0∞ :=
  ∑ output ∈ finiteHorizonAncestryReceiver aperture terminal horizon,
    ∫⁻ sourceTime in Ioc restartTime targetTime,
      finiteHorizonPicardMarkedServiceAt aperture terminal horizon nu restartTime
        baseRadius seed depth sourceTime output

/-- **Closed finite-horizon marked recurrence.**  The previous exact Volterra law is paid by the
actual finite operator and low/marked amplitude quantities on the next ancestry layer. -/
theorem finiteHeatSeededPicardMarkedHighMass_ancestry_succ_le
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (nu restartTime : ℝ) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    {targetTime : ℝ} (hnu : 0 ≤ nu) (htime : restartTime ≤ targetTime) :
    finiteHeatSeededPicardMarkedHighMass
        (finiteHorizonAncestryReceiver aperture terminal horizon)
        nu restartTime aperture baseRadius seed (depth + 1) targetTime ≤
      finiteHeatSeededPicardHighRestartMass
          (finiteHorizonAncestryReceiver aperture terminal horizon)
          nu restartTime targetTime baseRadius seed +
        finiteHorizonPicardMarkedServiceVolterraMass aperture terminal horizon
          nu restartTime baseRadius seed depth targetTime := by
  calc
    finiteHeatSeededPicardMarkedHighMass
        (finiteHorizonAncestryReceiver aperture terminal horizon)
        nu restartTime aperture baseRadius seed (depth + 1) targetTime ≤
      finiteHeatSeededPicardHighRestartMass
          (finiteHorizonAncestryReceiver aperture terminal horizon)
          nu restartTime targetTime baseRadius seed +
        finiteHeatSeededPicardMarkedQuadraticVolterraMass
          (finiteHorizonAncestryReceiver aperture terminal horizon)
          nu restartTime aperture baseRadius seed depth targetTime :=
      finiteHeatSeededPicardMarkedHighMass_succ_le _ _ _ _ _ _ _ hnu htime
    _ ≤ _ := by
      apply add_le_add_right
      unfold finiteHeatSeededPicardMarkedQuadraticVolterraMass
        finiteHorizonPicardMarkedServiceVolterraMass
      apply Finset.sum_le_sum
      intro output houtput
      apply lintegral_mono
      intro sourceTime
      exact finiteHeatSeededPicardMarkedQuadraticModeMass_le_ancestryService
        aperture terminal horizon nu restartTime baseRadius seed depth sourceTime houtput

section Audit

#print axioms transported_parent_mem_finiteHorizonAncestryReceiver_succ
#print axioms finiteProjectedInteractionAtomCost_ne_top
#print axioms enorm_projectedInteraction_le_atomCost
#print axioms finiteHorizonPicardMarkedServiceAt_ne_top
#print axioms finiteHeatSeededPicardMarkedQuadraticModeMass_le_ancestryService
#print axioms finiteHeatSeededPicardMarkedHighMass_ancestry_succ_le

end Audit

end Soma.Holonics.Millennium.NavierStokesFinitePicardAncestryService
