import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import ElementaryHolonics.Millennium.ReceiverIndexedCausalLengthTower

/-!
# The clocked Navier--Stokes extension tower

This module lifts the existing compatible open-lifespan continuation receipt into an exact
occurrence-bearing holon before adding any discrete measurement chart.  The strict extension
occurrence retains its source solution, longer target solution, real lifespan increase, velocity
agreement, and pressure-gradient agreement.  Serial contact is the existing pullback population;
the older `CompatibleOpenPeriodicExtension.comp` is exposed only as a condensation which forgets
the intermediate solution.

The optional tower presentation adds a reflexive history solely because a `Tower` requires a
stationary occurrence.  Its natural-number clock counts strict extension occurrences.  It is not
identified with real lifespan, spatial boundary size, dyadic Hodge scale, or resource work:
boundary and work counts enter through separate caller-supplied measurement ports, an exact
clock--ruler span is supplied separately, and a dyadic scale event has its own typed face below.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]` unless its statement says otherwise.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesClockedExtensionTower

open Soma.Holonics
open Soma.Holonics.Millennium.HolonicClockedPantographicSwing
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower

/-! ## The strict physical continuation holon -/

/-- [definition] One complete open periodic solution state with the viscosity, initial datum, and
force fixed as parameters of the continuing ecology.  The real lifespan remains a physical
coordinate rather than a natural-number clock or scale count. -/
structure OpenPeriodicState
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) where
  lifetime : ℝ
  velocity : VelocityField
  pressure : PressureField
  solution : OpenPeriodicSolutionOn lifetime nu initial force velocity pressure

/-- [definition] An exact strict extension occurrence beginning at a bundled solution state. -/
abbrev ExtensionHistory
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) :=
  Σ source : OpenPeriodicState nu initial force,
    CompatibleOpenPeriodicExtension source.solution

namespace ExtensionHistory

variable {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}

/-- [definition] The addressed source of one strict extension. -/
def source (history : ExtensionHistory nu initial force) :
    OpenPeriodicState nu initial force :=
  history.1

/-- [definition] The longer solution returned by one strict extension occurrence. -/
def target (history : ExtensionHistory nu initial force) :
    OpenPeriodicState nu initial force where
  lifetime := history.2.lifetime
  velocity := history.2.extendedVelocity
  pressure := history.2.extendedPressure
  solution := history.2.extendedSolution

/-- [definition] The exact positive real lifespan traversed by an extension occurrence. -/
def realLifespanSpan (history : ExtensionHistory nu initial force) : ℝ :=
  history.target.lifetime - history.source.lifetime

/-- The real lifespan span of every strict extension is positive. -/
theorem realLifespanSpan_pos (history : ExtensionHistory nu initial force) :
    0 < history.realLifespanSpan := by
  exact sub_pos.mpr history.2.terminal_lt

/-- [definition] Rebase an extension receipt along equality of its complete source state.  This
transport is needed because the solution proof is dependent on the state's lifespan and fields. -/
def transportSource
    {source target : OpenPeriodicState nu initial force}
    (source_eq : source = target)
    (extension : CompatibleOpenPeriodicExtension target.solution) :
    CompatibleOpenPeriodicExtension source.solution :=
  @Eq.ndrec (OpenPeriodicState nu initial force) target
    (fun state => CompatibleOpenPeriodicExtension state.solution)
    extension source source_eq.symm

/-- Transporting only the source index of an extension preserves its longer target state. -/
theorem target_transportSource
    {source target : OpenPeriodicState nu initial force}
    (source_eq : source = target)
    (extension : CompatibleOpenPeriodicExtension target.solution) :
    ExtensionHistory.target ⟨source, transportSource source_eq extension⟩ =
      ExtensionHistory.target ⟨target, extension⟩ := by
  cases source_eq
  simp [transportSource]

end ExtensionHistory

/-- [definition] The complete receiver face of a continuation.  It retains both endpoint states,
their oriented real lifespan order, exact old velocity agreement, and pressure-gradient agreement
modulo the physical pressure gauge. -/
structure ContinuationFace
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) where
  source : OpenPeriodicState nu initial force
  target : OpenPeriodicState nu initial force
  lifetime_le : source.lifetime ≤ target.lifetime
  agreesBefore : PeriodicFieldsAgreeBefore source.lifetime
    source.velocity target.velocity source.pressure target.pressure

/-- [definition] A dyadic Hodge scale is an addressed spatial event at one strict-interior time of
one solution state.  It is not the extension tick, the real lifespan, or the state's exterior
boundary count.  A later Hodge theorem must supply the actual scale-dependent receiver current. -/
structure DyadicScaleFace
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField)
    (ScaleAddress : Type*) where
  address : ScaleAddress
  state : OpenPeriodicState nu initial force
  time : Set.Ioo (0 : ℝ) state.lifetime
  scale : ℕ

/-- [definition] The receiver face returned by a strict extension occurrence. -/
def ExtensionHistory.receive
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    (history : ExtensionHistory nu initial force) :
    ContinuationFace nu initial force where
  source := history.source
  target := history.target
  lifetime_le := history.2.terminal_lt.le
  agreesBefore := history.2.agreesBefore

/-- [definition] The strict Navier--Stokes continuation holon.  Its occurrence population is
definitionally the existing compatible-extension carrier. -/
def extensionHolon
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) :
    Holon (OpenPeriodicState nu initial force) (OpenPeriodicState nu initial force)
      (ContinuationFace nu initial force) where
  Occurrence := ExtensionHistory nu initial force
  source := ExtensionHistory.source
  target := ExtensionHistory.target
  receive := ExtensionHistory.receive

/-- [definition] Every strict continuation occurrence beginning at one exact solution state. -/
def ExtensionSourceFibre
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    (state : OpenPeriodicState nu initial force) : Type _ :=
  { history : (extensionHolon nu initial force).Occurrence //
    (extensionHolon nu initial force).source history = state }

/-- The source fibre of the extension holon is exactly the existing compatible-extension
population. -/
def extensionSourceFibreEquiv
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    (state : OpenPeriodicState nu initial force) :
    ExtensionSourceFibre state ≃ CompatibleOpenPeriodicExtension state.solution where
  toFun carried := by
    rcases carried with ⟨⟨source, extension⟩, source_eq⟩
    cases source_eq
    exact extension
  invFun extension := ⟨⟨state, extension⟩, rfl⟩
  left_inv carried := by
    rcases carried with ⟨⟨source, extension⟩, source_eq⟩
    cases source_eq
    rfl
  right_inv extension := rfl

/-- Compatible extension exists exactly when the strict holon's source fibre is inhabited. -/
theorem canExtendCompatibly_iff_extensionSourceFibre_nonempty
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    (state : OpenPeriodicState nu initial force) :
    state.solution.CanExtendCompatibly ↔ Nonempty (ExtensionSourceFibre state) := by
  constructor
  · rintro ⟨extension⟩
    exact ⟨(extensionSourceFibreEquiv state).symm extension⟩
  · rintro ⟨carried⟩
    exact ⟨(extensionSourceFibreEquiv state) carried⟩

/-! ## Exact serial contact and lineage-losing condensation -/

/-- [definition] Two strict extensions interact only through their exact shared solution state. -/
abbrev ExtensionInteraction
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) :=
  Holon.Interaction (extensionHolon nu initial force) (extensionHolon nu initial force)

namespace ExtensionInteraction

variable {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}

/-- [definition] The real span of an exact serial interaction is the sum of its two retained
extension spans. -/
def realLifespanSpan (joined : ExtensionInteraction nu initial force) : ℝ :=
  joined.left.realLifespanSpan + joined.right.realLifespanSpan

/-- The real serial span is exactly final lifespan minus initial lifespan. -/
theorem realLifespanSpan_eq (joined : ExtensionInteraction nu initial force) :
    joined.realLifespanSpan =
      joined.right.target.lifetime - joined.left.source.lifetime := by
  have middle_lifetime : joined.left.target.lifetime = joined.right.source.lifetime :=
    congrArg OpenPeriodicState.lifetime joined.joins
  simp only [realLifespanSpan, ExtensionHistory.realLifespanSpan]
  linarith

/-- [definition] Rebase the second receipt of a pullback interaction to the exact target state of
the first.  No field or receiver data are changed. -/
def alignedRight (joined : ExtensionInteraction nu initial force) :
    CompatibleOpenPeriodicExtension joined.left.2.extendedSolution := by
  change CompatibleOpenPeriodicExtension joined.left.target.solution
  exact ExtensionHistory.transportSource joined.joins joined.right.2

/-- [definition] Condense an exact two-extension interaction to the older direct extension
receipt.  This intentionally forgets the intermediate state; the input pullback occurrence remains
the exact serial lineage owner. -/
def condense (joined : ExtensionInteraction nu initial force) :
    ExtensionHistory nu initial force :=
  ⟨joined.left.source, joined.left.2.comp joined.alignedRight⟩

/-- Condensation preserves the exterior source. -/
theorem condense_source (joined : ExtensionInteraction nu initial force) :
    joined.condense.source = joined.left.source := rfl

/-- Condensation preserves the exterior target. -/
theorem condense_target (joined : ExtensionInteraction nu initial force) :
    joined.condense.target = joined.right.target := by
  change ExtensionHistory.target ⟨joined.left.target, joined.alignedRight⟩ =
    ExtensionHistory.target joined.right
  exact ExtensionHistory.target_transportSource joined.joins joined.right.2

/-- Condensation preserves the total real lifespan span even though it forgets the intermediate
solution state. -/
theorem condense_realLifespanSpan (joined : ExtensionInteraction nu initial force) :
    joined.condense.realLifespanSpan = joined.realLifespanSpan := by
  rw [realLifespanSpan_eq]
  change joined.condense.target.lifetime - joined.condense.source.lifetime = _
  rw [condense_source, condense_target]

end ExtensionInteraction

/-! ## Reflexive completion and separately typed measurement ports -/

/-- [definition] The reflexive completion adds only stationary occurrences; strict extension
occurrences are not copied or altered. -/
abbrev ReflexiveExtensionHistory
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) :=
  OpenPeriodicState nu initial force ⊕ ExtensionHistory nu initial force

/-- [definition] The exact addressed history used by the optional discrete tower chart. -/
def reflexiveAddressedHistory
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) :
    AddressedHistory (ReflexiveExtensionHistory nu initial force)
      (OpenPeriodicState nu initial force) (ContinuationFace nu initial force) where
  source
    | Sum.inl state => state
    | Sum.inr extension => extension.source
  target
    | Sum.inl state => state
    | Sum.inr extension => extension.target
  receive
    | Sum.inl state =>
        { source := state
          target := state
          lifetime_le := le_rfl
          agreesBefore := PeriodicFieldsAgreeBefore.refl
            state.lifetime state.velocity state.pressure }
    | Sum.inr extension => extension.receive

/-- [definition] Apparatus measurements which are absent from the PDE extension receipt.  Boundary
scale, clock--ruler gearing, and per-resource work remain independent ports. -/
structure ExtensionTowerMeasurements
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField)
    (BoundaryAddress ClockAddress RulerAddress Resource : Type*) where
  boundaryAddress : BoundaryAddress
  boundaryLength : OpenPeriodicState nu initial force → ℕ
  clockRuler : ClockRulerSpan ClockAddress RulerAddress
  extensionWork : ExtensionHistory nu initial force → Resource → ℕ
  resourceCapacity : Resource → ℕ
  resourceCapacity_pos : ∀ resource, 0 < resourceCapacity resource

/-- [definition] The clocked extension tower relative to declared measurement ports.  Its clock
counts zero for a stationary occurrence and one for every strict extension occurrence. -/
def clockedExtensionTower
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    {BoundaryAddress ClockAddress RulerAddress Resource : Type*}
    (measurements : ExtensionTowerMeasurements nu initial force
      BoundaryAddress ClockAddress RulerAddress Resource) :
    Tower (ReflexiveExtensionHistory nu initial force)
      (OpenPeriodicState nu initial force) BoundaryAddress ClockAddress RulerAddress
      (ContinuationFace nu initial force) Resource where
  history := reflexiveAddressedHistory nu initial force
  boundaryAddress := measurements.boundaryAddress
  clockAddress := measurements.clockRuler.clockAddress
  rulerAddress := measurements.clockRuler.rulerAddress
  boundaryLength := measurements.boundaryLength
  clockLength
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  resourceWork
    | Sum.inl _, _ => 0
    | Sum.inr extension, resource => measurements.extensionWork extension resource
  resourceCapacity := measurements.resourceCapacity
  resourceCapacity_pos := measurements.resourceCapacity_pos
  clockRuler := measurements.clockRuler
  clockAddress_exact := rfl
  rulerAddress_exact := rfl
  stay := Sum.inl
  stay_source := fun _ => rfl
  stay_target := fun _ => rfl
  stay_clockLength := fun _ => rfl
  stay_resourceWork := fun _ _ => rfl

/-- Every strict extension contributes exactly one discrete extension-count tick. -/
@[simp]
theorem clockedExtensionTower_extension_clockLength
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    {BoundaryAddress ClockAddress RulerAddress Resource : Type*}
    (measurements : ExtensionTowerMeasurements nu initial force
      BoundaryAddress ClockAddress RulerAddress Resource)
    (extension : ExtensionHistory nu initial force) :
    (clockedExtensionTower measurements).clockLength (Sum.inr extension) = 1 := rfl

/-- Two exactly joined strict extensions carry two extension-count ticks while retaining both
occurrences and their middle equality. -/
theorem clockedExtensionTower_two_extension_clockLength
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    {BoundaryAddress ClockAddress RulerAddress Resource : Type*}
    (measurements : ExtensionTowerMeasurements nu initial force
      BoundaryAddress ClockAddress RulerAddress Resource)
    (joined : ExtensionInteraction nu initial force) :
    (clockedExtensionTower measurements).serialClockLength
      ⟨Sum.inr joined.left, Sum.inr joined.right, joined.joins⟩ = 2 := by
  rfl

/-- Exact pullback lineage and its condensed receiver shadow have the same exterior endpoints and
real span, but the event clock separates them: the retained serial occurrence has two ticks while
the re-embedded condensation has one. -/
theorem serial_and_condensed_have_same_exterior_but_distinct_clockLength
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    {BoundaryAddress ClockAddress RulerAddress Resource : Type*}
    (measurements : ExtensionTowerMeasurements nu initial force
      BoundaryAddress ClockAddress RulerAddress Resource)
    (joined : ExtensionInteraction nu initial force) :
    joined.condense.source = joined.left.source ∧
      joined.condense.target = joined.right.target ∧
      joined.condense.realLifespanSpan = joined.realLifespanSpan ∧
      (clockedExtensionTower measurements).serialClockLength
          ⟨Sum.inr joined.left, Sum.inr joined.right, joined.joins⟩ ≠
        (clockedExtensionTower measurements).clockLength (Sum.inr joined.condense) := by
  exact ⟨joined.condense_source, joined.condense_target,
    joined.condense_realLifespanSpan, by
      change 2 ≠ 1
      decide⟩

section Audit

#print axioms extensionSourceFibreEquiv
#print axioms canExtendCompatibly_iff_extensionSourceFibre_nonempty
#print axioms ExtensionInteraction.realLifespanSpan_eq
#print axioms ExtensionInteraction.condense
#print axioms ExtensionInteraction.condense_realLifespanSpan
#print axioms clockedExtensionTower_two_extension_clockLength
#print axioms serial_and_condensed_have_same_exterior_but_distinct_clockLength

end Audit

end Soma.Holonics.Millennium.NavierStokesClockedExtensionTower
