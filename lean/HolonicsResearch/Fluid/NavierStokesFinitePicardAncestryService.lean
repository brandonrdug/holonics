import HolonicsResearch.Fluid.NavierStokesFinitePicardVolterraMass

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

namespace Holonics.Fluid.NavierStokesFinitePicardAncestryService

open Holonics.Fluid.NavierStokesDyadicFlowCommutator
open Holonics.Fluid.NavierStokesFiniteGalerkin
open Holonics.Fluid.NavierStokesFinitePicardChronology
open Holonics.Fluid.NavierStokesFinitePicardVolterraMass
open Holonics.Fluid.NavierStokesFiniteScaleAncestry
open Holonics.Fluid.NavierStokesFourierTriads
open Holonics.Fluid.NavierStokesMildFourierNonlinearity
open Holonics.Fluid.NavierStokesTorusFourier

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

/-! ## The finite aperture service law -/

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
#print axioms finiteHorizonPicardMarkedServiceAt_ne_top
#print axioms finiteHeatSeededPicardMarkedQuadraticModeMass_le_ancestryService
#print axioms finiteHeatSeededPicardMarkedHighMass_ancestry_succ_le

end Audit

end Holonics.Fluid.NavierStokesFinitePicardAncestryService
