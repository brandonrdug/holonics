import ElementaryHolonics.Transport.ReceiverPotential
import ElementaryHolonics.Foundation.JointReceiverDescent
import ElementaryHolonics.Millennium.Swing

/-!
# Swing transports compatible potential and its receiver tolerance

[proved-derived] The existing fixed-board Swing supplies an explicit source equivalence.
Rebasing observation, receiver and generators through that equivalence preserves the complete
family of possible future faces. In a normed additive chart the affine Swing is an isometry,
so it also carries a declared receiver tolerance exactly. This does not extend that metric claim
to every projective chart, nor identify coordinate rebase with a physical intervention.
-/

namespace Soma.Holonics.Geometry.SwingPotential

open Soma.Holonics
open Soma.Holonics.Millennium.Swing
open Soma.Holonics.Transport.ReceiverPotential
open Soma.Holonics.Foundation.JointReceiverDescent
open Soma.Holonics.Millennium.LineageCompression

universe u

/-- The standing involution, with its exact inverse retained. -/
def swingEquiv {X : Type*} [AddCommGroup X] (anchor : X) : X ≃ X where
  toFun := swing anchor
  invFun := swing anchor
  left_inv := theSwingIsAnInvolution anchor
  right_inv := theSwingIsAnInvolution anchor

/-- The full potential family, rather than a selected source, crosses the Swing chart. -/
theorem swing_preserves_history_potential
    {X Observation Generator Result : Type*} [AddCommGroup X]
    (anchor : X) (entering : X → Observation) (observed : Set.range entering)
    (transport : Generator → X → X) (word : List Generator) (receiver : X → Result) :
    historyOutcomes (entering ∘ (swingEquiv anchor).symm)
      (rebaseObservation (swingEquiv anchor) entering observed)
      (rebaseTransport (swingEquiv anchor) transport) word
      (receiver ∘ (swingEquiv anchor).symm) =
      historyOutcomes entering observed transport word receiver :=
  historyOutcomes_rebase _ _ _ _ _ _

/-- The affine half-turn preserves receiver separation in its declared normed chart. -/
theorem swing_preserves_distance {X : Type*} [NormedAddCommGroup X]
    (anchor left right : X) : dist (swing anchor left) (swing anchor right) = dist left right := by
  simp only [dist_eq_norm, swing]
  have difference : anchor + anchor - left - (anchor + anchor - right) = -(left - right) := by
    abel
  rw [difference, norm_neg]

/-- A finite tolerance for the whole future family transports through the Swing without
selecting one of its compatible causes. -/
theorem swing_transports_tolerance
    {Source Observation X : Type*} [NormedAddCommGroup X]
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → X) (anchor reference : X) (tolerance : ℝ)
    (bounded : ∀ result ∈ outcomes entering observed future,
      dist result reference ≤ tolerance) :
    ∀ result ∈ outcomes entering observed (swing anchor ∘ future),
      dist result (swing anchor reference) ≤ tolerance := by
  have h := bounded_outcomes_transport entering observed future (swing anchor)
    reference tolerance 1 (by norm_num) bounded
    (by intro left right; simp [swing_preserves_distance])
  simpa using h

/-- The canonical joint additive quotient carries the affine Swing itself, including its
anchor. This uses the quotient's additive law; no additive-law claim is made for a nonzero
anchored Swing as a map on the original carrier. -/
theorem joint_quotient_swing
    {Generator Receiver X V : Type u} [AddCommGroup X] [AddCommGroup V]
    (J : JointReceiverHistory Generator Receiver X V) (anchor source : X) :
    J.quotient (swing anchor source) = swing (J.quotient anchor) (J.quotient source) := by
  simp [JointReceiverHistory.quotient, swing]

/-- Every admitted anchor family induces an exact receiver-history compression for its
ordered affine Swings. The full joint quotient and preimage population are reused. -/
def swingHistoryCompression
    {Generator Receiver X V Anchor : Type u} [AddCommGroup X] [AddCommGroup V]
    (J : JointReceiverHistory Generator Receiver X V) (anchors : Anchor → X) :
    ReceiverHistoryCompression Anchor Receiver X J.JointQuotient V where
  present := J.presentCompression
  sourceTransport anchor := swing (anchors anchor)
  quotientTransport anchor := swing (J.quotient (anchors anchor))
  generatorExact anchor source := joint_quotient_swing J (anchors anchor) source

/-- Primitive Swing words conduct through the joint quotient for the whole future family. -/
theorem swing_word_joint_receiver_exact
    {Generator Receiver X V Anchor : Type u} [AddCommGroup X] [AddCommGroup V]
    (J : JointReceiverHistory Generator Receiver X V) (anchors : Anchor → X)
    (word : List Anchor) (source : X) :
    J.quotient (Millennium.Chronology.transportWord (fun i ↦ swing (anchors i)) word source) =
      Millennium.Chronology.transportWord (fun i ↦ swing (J.quotient (anchors i))) word
        (J.quotient source) :=
  (swingHistoryCompression J anchors).quotientCommutesWithEveryOrderedWord word source

end Soma.Holonics.Geometry.SwingPotential

section Audit
open Soma.Holonics.Geometry.SwingPotential
#print axioms swing_preserves_history_potential
#print axioms swing_preserves_distance
#print axioms swing_transports_tolerance
#print axioms joint_quotient_swing
#print axioms swing_word_joint_receiver_exact
end Audit
