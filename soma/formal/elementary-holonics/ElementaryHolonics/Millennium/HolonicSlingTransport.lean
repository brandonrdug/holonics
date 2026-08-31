import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Millennium.HolonicEntropyActionInduction
import Mathlib.Data.Fintype.BigOperators

/-!
# A holonic sling is a released Swing plus a typed continuation ecology

**[proved-derived]** The sling-specific datum is not another dynamics cabinet.  It refines the
existing deterministic `SuccessorCurrent` by decomposing each exact source difference into a
deliberate impulse and a returned medium current.  Structural induction then retains both terms
through every finite successor occurrence.

The affine Swing supplies an exact release impulse after a declared additive chart transports its
coordinate difference into the momentum line.  A subsequent atmosphere, field, or other medium is
an ordered generator word with a complete addressed fibre.  Calling its current negligible means
exact membership in a declared receiver kernel; the source current remains in the reconstruction
fibre.

The final section proves the kinematic identity underlying an ideal gravity assist.  Equal
asymptotic speed in the moving pivot frame does not imply equal speed in the exterior frame: the
exterior squared-speed difference is exactly the pivot velocity paired with the turned relative
velocity difference.  The orbital law establishing equal relative speeds remains a separate
source-specific constitutive theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicSlingTransport

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.HolonicEntropyActionInduction
open Soma.Holonics.Millennium.Swing

/-! ## The exact source decomposition -/

/-- One deterministic successor current whose local source is resolved into deliberate release
impulse and returned medium current. -/
structure HolonicSling
    (State Momentum : Type*) [AddCommGroup Momentum]
    extends SuccessorCurrent State Momentum where
  impulse : State → Momentum
  mediumReturn : State → Momentum
  source_decomposition : ∀ state,
    source state = impulse state + mediumReturn state

namespace HolonicSling

variable {State Momentum : Type*} [AddCommGroup Momentum]

/-- One sling occurrence returns the deliberate impulse together with the complete medium
response. -/
theorem release_balance (sling : HolonicSling State Momentum) (state : State) :
    sling.coordinate (sling.successor state) - sling.coordinate state =
      sling.impulse state + sling.mediumReturn state := by
  rw [sling.localLaw, sling.source_decomposition]

/-- Structural induction promotes the resolved local law through the whole deterministic sling
chronology without deleting intermediate medium interactions. -/
theorem serial_difference
    (sling : HolonicSling State Momentum) (initial : State) (steps : ℕ) :
    sling.coordinate (successorOrbit sling.successor initial steps) -
        sling.coordinate initial =
      ∑ k ∈ Finset.range steps,
        (sling.impulse (successorOrbit sling.successor initial k) +
          sling.mediumReturn (successorOrbit sling.successor initial k)) := by
  simpa only [sling.source_decomposition] using
    sling.toSuccessorCurrent.telescopes initial steps

/-- `Negligible in this receiver' means that the complete medium return belongs to its kernel.
This is exact receiver equality, not a small-error estimate. -/
theorem receiver_release_eq_impulse
    {Reading : Type*} [AddCommGroup Reading]
    (sling : HolonicSling State Momentum) (receiver : Momentum →+ Reading)
    (medium_kernel : ∀ state, sling.mediumReturn state ∈ receiver.ker)
    (state : State) :
    receiver (sling.coordinate (sling.successor state) - sling.coordinate state) =
      receiver (sling.impulse state) := by
  rw [sling.release_balance, map_add]
  have hzero : receiver (sling.mediumReturn state) = 0 := medium_kernel state
  rw [hzero, add_zero]

/-- When every medium return lies in the receiver kernel, the received finite sling difference is
exactly the received sum of deliberate impulses.  The source history still retains the medium. -/
theorem receiver_serial_difference_eq_impulses
    {Reading : Type*} [AddCommGroup Reading]
    (sling : HolonicSling State Momentum) (receiver : Momentum →+ Reading)
    (medium_kernel : ∀ state, sling.mediumReturn state ∈ receiver.ker)
    (initial : State) (steps : ℕ) :
    receiver
        (sling.coordinate (successorOrbit sling.successor initial steps) -
          sling.coordinate initial) =
      ∑ k ∈ Finset.range steps,
        receiver (sling.impulse (successorOrbit sling.successor initial k)) := by
  have returned := congrArg receiver (sling.serial_difference initial steps)
  have medium_zero : ∀ state, receiver (sling.mediumReturn state) = 0 :=
    fun state ↦ medium_kernel state
  simpa only [map_sub, map_sum, map_add, medium_zero, add_zero] using returned

end HolonicSling

/-! ## Swing difference realized as a typed impulse -/

/-- The complete coordinate difference returned by one frozen-board Swing. -/
def swingImpulse {G : Type*} [AddCommGroup G] (anchor body : G) : G :=
  swing anchor body - body

/-- One Swing changes the body by twice its oriented displacement toward the anchor. -/
theorem swingImpulse_eq_doubled_anchorDifference
    {G : Type*} [AddCommGroup G] (anchor body : G) :
    swingImpulse anchor body = (anchor - body) + (anchor - body) := by
  simp only [swingImpulse, swing]
  abel

/-- The release target reconstructs from the pre-release body and the complete Swing impulse. -/
theorem body_add_swingImpulse
    {G : Type*} [AddCommGroup G] (anchor body : G) :
    body + swingImpulse anchor body = swing anchor body := by
  simp only [swingImpulse]
  abel

/-- A source-specific additive chart transports the geometric Swing difference into a typed
momentum line. -/
def realizedSwingImpulse
    {G Momentum : Type*} [AddCommGroup G] [AddCommGroup Momentum]
    (realize : G →+ Momentum) (anchor body : G) : Momentum :=
  realize (swingImpulse anchor body)

/-- Realization preserves the exact doubled-anchor form of the impulse. -/
theorem realizedSwingImpulse_eq_doubled_anchorDifference
    {G Momentum : Type*} [AddCommGroup G] [AddCommGroup Momentum]
    (realize : G →+ Momentum) (anchor body : G) :
    realizedSwingImpulse realize anchor body =
      realize (anchor - body) + realize (anchor - body) := by
  rw [realizedSwingImpulse, swingImpulse_eq_doubled_anchorDifference, map_add]

/-- Momentum after the declared release is prior momentum plus the realized Swing impulse. -/
def releasedMomentum
    {G Momentum : Type*} [AddCommGroup G] [AddCommGroup Momentum]
    (realize : G →+ Momentum) (anchor body : G) (before : Momentum) : Momentum :=
  before + realizedSwingImpulse realize anchor body

theorem releasedMomentum_difference
    {G Momentum : Type*} [AddCommGroup G] [AddCommGroup Momentum]
    (realize : G →+ Momentum) (anchor body : G) (before : Momentum) :
    releasedMomentum realize anchor body before - before =
      realizedSwingImpulse realize anchor body := by
  simp [releasedMomentum]

/-! ## Release followed by an ordered deterministic medium word -/

/-- The two source species in a sling chronology: one addressed Swing release or one medium
interaction. -/
inductive SlingGenerator (MediumGenerator : Type*) where
  | release (anchor : Site)
  | medium (generator : MediumGenerator)

/-- Both species act on the same carried state, so their order remains a real coordinate. -/
def slingTransport {MediumGenerator : Type*}
    (mediumTransport : MediumGenerator → Site → Site) :
    SlingGenerator MediumGenerator → Site → Site
  | .release anchor => swing anchor
  | .medium generator => mediumTransport generator

/-- `transportWord` reads right-to-left, so the release is the rightmost/first occurrence and the
medium history follows it. -/
def releasedMediumWord {MediumGenerator : Type*}
    (anchor : Site) (mediumWord : List MediumGenerator) :
    List (SlingGenerator MediumGenerator) :=
  mediumWord.map SlingGenerator.medium ++ [SlingGenerator.release anchor]

theorem transportWord_append
    {Generator State : Type*} (transport : Generator → State → State)
    (left right : List Generator) (state : State) :
    transportWord transport (left ++ right) state =
      transportWord transport left (transportWord transport right state) := by
  induction left with
  | nil => rfl
  | cons generator left ih =>
      simp only [List.cons_append, transportWord_cons, ih]

theorem transportWord_mediumMap
    {MediumGenerator : Type*} (mediumTransport : MediumGenerator → Site → Site)
    (mediumWord : List MediumGenerator) (state : Site) :
    transportWord (slingTransport mediumTransport)
        (mediumWord.map SlingGenerator.medium) state =
      transportWord mediumTransport mediumWord state := by
  induction mediumWord with
  | nil => rfl
  | cons generator mediumWord ih =>
      simp only [List.map_cons, transportWord_cons, slingTransport, ih]

/-- A sling chronology is exactly one Swing release followed by the declared ordered medium
history. -/
theorem releasedMediumWord_eq
    {MediumGenerator : Type*} (mediumTransport : MediumGenerator → Site → Site)
    (anchor body : Site) (mediumWord : List MediumGenerator) :
    transportWord (slingTransport mediumTransport)
        (releasedMediumWord anchor mediumWord) body =
      transportWord mediumTransport mediumWord (swing anchor body) := by
  rw [releasedMediumWord, transportWord_append, transportWord_mediumMap]
  rfl

/-- The release and every later medium interaction retain a complete nested addressed occurrence
and all joining equalities. -/
theorem releasedMediumWord_retains_lineage
    {MediumGenerator : Type*} (mediumTransport : MediumGenerator → Site → Site)
    (anchor body : Site) (mediumWord : List MediumGenerator) :
    Nonempty
      ((AddressedPassage.wordPassage (slingTransport mediumTransport)
        (releasedMediumWord anchor mediumWord)).Fibre body
          (transportWord (slingTransport mediumTransport)
            (releasedMediumWord anchor mediumWord) body)) :=
  ⟨AddressedPassage.wordFibre (slingTransport mediumTransport)
    (releasedMediumWord anchor mediumWord) body⟩

/-! ## The deterministic Markov receiver is a quotient criterion -/

/-- A deterministic successor is Markov on a receiver face exactly when every complete source
pair collapsed by the receiver also has equal returned successor faces.  Otherwise the missing
medium state remains a reconstruction fibre and a probability kernel cannot repair the quotient. -/
theorem deterministicMarkovReceiver_exists_iff_fibre_stable
    {State Face : Type*} (successor : State → State) (receiver : State → Face) :
    Nonempty (ReceiverTransformer receiver (fun state ↦ receiver (successor state))) ↔
      ∀ left right, receiver left = receiver right →
        receiver (successor left) = receiver (successor right) :=
  receiverTransformer_exists_iff receiver (fun state ↦ receiver (successor state))

/-! ## Exact exterior-frame gravity-assist identity -/

/-- Squared speed in one finite coordinate receiver. -/
def squaredSpeed {Axis : Type*} [Fintype Axis] (velocity : Axis → ℝ) : ℝ :=
  ∑ axis, velocity axis ^ 2

/-- Euclidean pairing in the same finite coordinate receiver. -/
def velocityPairing {Axis : Type*} [Fintype Axis]
    (left right : Axis → ℝ) : ℝ :=
  ∑ axis, left axis * right axis

/-- If the incoming and outgoing velocities have equal squared speed in the moving pivot frame,
then the exterior-frame squared-speed change is exactly twice the pivot velocity paired with the
turned relative-velocity difference. -/
theorem gravityAssist_squaredSpeed_difference
    {Axis : Type*} [Fintype Axis]
    (pivot incomingRelative outgoingRelative : Axis → ℝ)
    (relativeSpeedConserved :
      squaredSpeed outgoingRelative = squaredSpeed incomingRelative) :
    squaredSpeed (pivot + outgoingRelative) -
        squaredSpeed (pivot + incomingRelative) =
      2 * velocityPairing pivot (outgoingRelative - incomingRelative) := by
  have hrelative :
      (∑ axis, outgoingRelative axis ^ 2) =
        ∑ axis, incomingRelative axis ^ 2 := by
    simpa only [squaredSpeed] using relativeSpeedConserved
  have hcross :
      (∑ axis, 2 * pivot axis *
        (outgoingRelative axis - incomingRelative axis)) =
        2 * (∑ axis, pivot axis *
          (outgoingRelative axis - incomingRelative axis)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro axis _haxis
    ring
  unfold squaredSpeed velocityPairing
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ axis, ((pivot axis + outgoingRelative axis) ^ 2 -
        (pivot axis + incomingRelative axis) ^ 2)) =
      ∑ axis,
        (2 * pivot axis * (outgoingRelative axis - incomingRelative axis) +
          (outgoingRelative axis ^ 2 - incomingRelative axis ^ 2)) := by
        apply Finset.sum_congr rfl
        intro axis _haxis
        ring
    _ = 2 * (∑ axis, pivot axis *
          (outgoingRelative axis - incomingRelative axis)) +
        ((∑ axis, outgoingRelative axis ^ 2) -
          ∑ axis, incomingRelative axis ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hcross]
    _ = 2 * (∑ axis, pivot axis *
          (outgoingRelative axis - incomingRelative axis)) := by
        rw [hrelative, sub_self, add_zero]

section Audit

#print axioms HolonicSling.release_balance
#print axioms HolonicSling.serial_difference
#print axioms HolonicSling.receiver_release_eq_impulse
#print axioms HolonicSling.receiver_serial_difference_eq_impulses
#print axioms swingImpulse_eq_doubled_anchorDifference
#print axioms realizedSwingImpulse_eq_doubled_anchorDifference
#print axioms releasedMediumWord_eq
#print axioms releasedMediumWord_retains_lineage
#print axioms deterministicMarkovReceiver_exists_iff_fibre_stable
#print axioms gravityAssist_squaredSpeed_difference

end Audit

end Soma.Holonics.Millennium.HolonicSlingTransport
