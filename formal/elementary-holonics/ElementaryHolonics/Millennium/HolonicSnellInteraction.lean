import ElementaryHolonics.Millennium.HolonicDirectedPassage
import ElementaryHolonics.Millennium.Turn
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Snell--Euler interaction: an exact interface current and its multiway fibre

Euler phase supplies an oriented complex direction.  Its imaginary receiver is the tangential
component.  Snell's law is exactly the vanishing of the returned tangential current across an
interface, while the normal component remains as an explicit unresolved remainder.  Thus the law
does not collapse distinct phase branches.

A `SnellMultiway` retains every graph edge compatible with that interface receiver.  Every finite
edge path preserves the tangential receiver, but the graph may still branch through different
normal components, phases, and later histories.  This is a source-specific instance of
`HolonicDirectedPassage`: local interaction, oriented returned difference, exact gluing, and a
receiver fibre rather than a chosen ray.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` over exact real/complex trigonometry.  Calling the weights
physical refractive indices requires the usual additional apparatus and positivity hypotheses;
this module proves the interface algebra itself.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.HolonicSnellInteraction

open Soma.Holonics.Millennium.HolonicDirectedPassage

/-- [definition] One oriented phase occurrence at an interface. -/
structure PhaseOccurrence where
  weight : ℝ
  angle : ℝ

/-- [definition] Euler's unit complex direction. -/
def eulerDirection (angle : ℝ) : ℂ :=
  Complex.exp ((angle : ℂ) * Complex.I)

/-- [proved-derived; formal-checked] The real and imaginary receiver faces of Euler direction
are cosine and sine exactly. -/
theorem eulerDirection_receivers (angle : ℝ) :
    (eulerDirection angle).re = Real.cos angle ∧
      (eulerDirection angle).im = Real.sin angle := by
  exact ⟨Complex.exp_ofReal_mul_I_re angle, Complex.exp_ofReal_mul_I_im angle⟩

/-- [proved-derived; formal-checked] Successive turns compose multiplicatively. -/
theorem eulerDirection_add (left right : ℝ) :
    eulerDirection (left + right) = eulerDirection left * eulerDirection right := by
  rw [eulerDirection, eulerDirection, eulerDirection]
  rw [show (((left + right : ℝ) : ℂ) * Complex.I) =
      (left : ℂ) * Complex.I + (right : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_add _ _

/-- [proved-derived; formal-checked] The Euler carrier retains unit magnitude while its angle
turns. -/
theorem eulerDirection_norm (angle : ℝ) : ‖eulerDirection angle‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I angle

/-- [definition] The complete weighted phase carrier before a receiver selects a component. -/
def phaseCarrier (occurrence : PhaseOccurrence) : ℂ :=
  (occurrence.weight : ℂ) * eulerDirection occurrence.angle

/-- [definition] The tangential interface receiver. -/
def tangentialReceiver (occurrence : PhaseOccurrence) : ℝ :=
  occurrence.weight * (eulerDirection occurrence.angle).im

/-- [definition] The complementary normal receiver, retained rather than silently discarded. -/
def normalReceiver (occurrence : PhaseOccurrence) : ℝ :=
  occurrence.weight * (eulerDirection occurrence.angle).re

/-- [proved-derived; formal-checked] The paired normal/tangential receivers reconstruct the
complete weighted Euler carrier exactly. -/
theorem phaseCarrier_eq_receivers (occurrence : PhaseOccurrence) :
    phaseCarrier occurrence = ⟨normalReceiver occurrence, tangentialReceiver occurrence⟩ := by
  apply Complex.ext
  · simp [phaseCarrier, normalReceiver]
  · simp [phaseCarrier, tangentialReceiver]

/-- [definition] The oriented tangential current returned by one interface crossing. -/
def interfaceCurrent (incoming outgoing : PhaseOccurrence) : ℝ :=
  tangentialReceiver outgoing - tangentialReceiver incoming

/-- [proved-derived; formal-checked] The Snell current is the imaginary receiver of the complete
oriented phase-carrier difference. -/
theorem interfaceCurrent_eq_phaseCarrierDifference_im
    (incoming outgoing : PhaseOccurrence) :
    interfaceCurrent incoming outgoing =
      (phaseCarrier outgoing - phaseCarrier incoming).im := by
  rw [phaseCarrier_eq_receivers, phaseCarrier_eq_receivers]
  rfl

/-- [definition] Snell compatibility is the null fibre of the tangential interface current. -/
def SnellCompatible (incoming outgoing : PhaseOccurrence) : Prop :=
  interfaceCurrent incoming outgoing = 0

/-- [proved-derived; formal-checked] The interface current is exactly the difference of the two
classical `weight * sin(angle)` faces. -/
theorem interfaceCurrent_eq_sineDifference (incoming outgoing : PhaseOccurrence) :
    interfaceCurrent incoming outgoing =
      outgoing.weight * Real.sin outgoing.angle -
        incoming.weight * Real.sin incoming.angle := by
  simp [interfaceCurrent, tangentialReceiver, eulerDirection,
    Complex.exp_ofReal_mul_I_im]

/-- [proved-derived; formal-checked] Snell's law is precisely zero returned tangential current. -/
theorem snellCompatible_iff (incoming outgoing : PhaseOccurrence) :
    SnellCompatible incoming outgoing ↔
      incoming.weight * Real.sin incoming.angle =
        outgoing.weight * Real.sin outgoing.angle := by
  rw [SnellCompatible, interfaceCurrent_eq_sineDifference]
  exact sub_eq_zero.trans eq_comm

/-- [definition] The addressed Snell current as a state-induced exact ledger. -/
def snellCurrentLedger : AddressedCurrent PhaseOccurrence ℝ :=
  AddressedCurrent.fromState tangentialReceiver

/-- [proved-derived; formal-checked] Every finite chain of interfaces glues exactly to its
exterior tangential difference. -/
theorem finiteInterfaceChain_eq_exterior
    (address : ℕ → PhaseOccurrence) (pieces : ℕ) :
    snellCurrentLedger.pathCurrent address pieces =
      interfaceCurrent (address 0) (address pieces) := by
  simpa [snellCurrentLedger, interfaceCurrent] using
    (snellCurrentLedger.pathCurrent_eq_exterior_of_composesExactly
      (AddressedCurrent.fromState_composesExactly tangentialReceiver) address pieces)

/-- [proved-derived; formal-checked] Tangential conservation does not collapse the complete phase:
zero and a half-turn have the same tangential receiver and opposite normal receivers. -/
theorem tangentialConservation_retainsNormalRemainder :
    let incoming : PhaseOccurrence := ⟨1, 0⟩
    let outgoing : PhaseOccurrence := ⟨1, Real.pi⟩
    SnellCompatible incoming outgoing ∧
      normalReceiver outgoing - normalReceiver incoming = -2 := by
  dsimp
  constructor
  · rw [snellCompatible_iff]
    simp
  · simp [normalReceiver, eulerDirection]
    norm_num

/-! ## The compatible multiway graph -/

/-- [definition] A multiway interaction graph whose edges all conserve the declared tangential
receiver.  The edge population is retained; no successor is selected. -/
structure SnellMultiway (Vertex : Type*) where
  occurrence : Vertex → PhaseOccurrence
  Edge : Vertex → Vertex → Prop
  edge_compatible : ∀ {source target}, Edge source target →
    SnellCompatible (occurrence source) (occurrence target)

namespace SnellMultiway

variable {Vertex : Type*} (graph : SnellMultiway Vertex)

/-- [proved-derived; formal-checked] Every admitted edge returns zero tangential current. -/
theorem edge_interfaceCurrent_eq_zero {source target : Vertex}
    (edge : graph.Edge source target) :
    interfaceCurrent (graph.occurrence source) (graph.occurrence target) = 0 :=
  graph.edge_compatible edge

/-- [proved-derived; formal-checked] Every finite multiway path preserves the tangential receiver
exactly, independent of how many alternative compatible branches the graph retains. -/
theorem path_preserves_tangentialReceiver
    (address : ℕ → Vertex) (pieces : ℕ)
    (follows : ∀ piece, piece < pieces → graph.Edge (address piece) (address (piece + 1))) :
    tangentialReceiver (graph.occurrence (address pieces)) =
      tangentialReceiver (graph.occurrence (address 0)) := by
  have eachZero :
      ∀ piece ∈ Finset.range pieces,
        interfaceCurrent (graph.occurrence (address piece))
          (graph.occurrence (address (piece + 1))) = 0 := by
    intro piece hpiece
    exact graph.edge_interfaceCurrent_eq_zero (follows piece (Finset.mem_range.mp hpiece))
  have chain := finiteInterfaceChain_eq_exterior
    (fun piece ↦ graph.occurrence (address piece)) pieces
  have sumZero :
      snellCurrentLedger.pathCurrent
        (fun piece ↦ graph.occurrence (address piece)) pieces = 0 := by
    unfold AddressedCurrent.pathCurrent
    apply Finset.sum_eq_zero
    intro piece hpiece
    simpa [snellCurrentLedger, interfaceCurrent] using eachZero piece hpiece
  rw [sumZero] at chain
  apply sub_eq_zero.mp
  change interfaceCurrent (graph.occurrence (address 0))
    (graph.occurrence (address pieces)) = 0
  exact chain.symm

end SnellMultiway

section Audit

#print axioms eulerDirection_receivers
#print axioms eulerDirection_add
#print axioms phaseCarrier_eq_receivers
#print axioms interfaceCurrent_eq_phaseCarrierDifference_im
#print axioms interfaceCurrent_eq_sineDifference
#print axioms snellCompatible_iff
#print axioms finiteInterfaceChain_eq_exterior
#print axioms tangentialConservation_retainsNormalRemainder
#print axioms SnellMultiway.path_preserves_tangentialReceiver

end Audit

end Soma.Holonics.Millennium.HolonicSnellInteraction
