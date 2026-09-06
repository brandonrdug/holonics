import ElementaryHolonics.Computation.HolonicConstitutiveFibre
import Mathlib.Tactic

/-!
# A two-port rational phase circulation

This file records one exact local junction law.  Incoming and held incidences remain distinct; the
emitted output and successor-held output are distinct returned faces.  The paired-current relations
below retain those source/output tickets through `HolonicConstitutiveFibre`; they do not fit a global
map or install a learning update.
-/

namespace Soma.Holonics.Computation.HolonicConstitutiveCirculation

open Soma.Holonics
open HolonicConstitutiveFibre

abbrev Phase := ℚ × ℚ

def junctionVelocity (a b incoming held : ℚ) : ℚ :=
  2 * (a * incoming + b * held) / (a + b)

def emitted (a b incoming held : ℚ) : ℚ :=
  junctionVelocity a b incoming held - incoming

def successorHeld (a b incoming held : ℚ) : ℚ :=
  junctionVelocity a b incoming held - held

theorem admittance_sum_ne_zero {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    a + b ≠ 0 := by
  exact ne_of_gt (add_pos ha hb)

/-- The weighted square energy is conserved across the scalar two-port junction. -/
theorem weighted_square_energy
    {a b incoming held : ℚ} (ha : 0 < a) (hb : 0 < b) :
    a * emitted a b incoming held ^ 2 + b * successorHeld a b incoming held ^ 2 =
      a * incoming ^ 2 + b * held ^ 2 := by
  dsimp [emitted, successorHeld, junctionVelocity]
  field_simp [admittance_sum_ne_zero ha hb]
  ring

/-- The junction velocity is additive in the paired incoming/held incidences. -/
theorem junctionVelocity_additive
    {a b i₁ h₁ i₂ h₂ : ℚ} (hab : a + b ≠ 0) :
    junctionVelocity a b (i₁ + i₂) (h₁ + h₂) =
      junctionVelocity a b i₁ h₁ + junctionVelocity a b i₂ h₂ := by
  dsimp [junctionVelocity]
  field_simp [hab]
  ring

/-- The junction velocity is homogeneous in the paired incoming/held incidences. -/
theorem junctionVelocity_smul
    {a b scalar incoming held : ℚ} (hab : a + b ≠ 0) :
    junctionVelocity a b (scalar * incoming) (scalar * held) =
      scalar * junctionVelocity a b incoming held := by
  dsimp [junctionVelocity]
  field_simp [hab]

theorem emitted_additive
    {a b i₁ h₁ i₂ h₂ : ℚ} (hab : a + b ≠ 0) :
    emitted a b (i₁ + i₂) (h₁ + h₂) =
      emitted a b i₁ h₁ + emitted a b i₂ h₂ := by
  dsimp [emitted]
  rw [junctionVelocity_additive hab]
  ring

theorem emitted_smul
    {a b scalar incoming held : ℚ} (hab : a + b ≠ 0) :
    emitted a b (scalar * incoming) (scalar * held) =
      scalar * emitted a b incoming held := by
  dsimp [emitted]
  rw [junctionVelocity_smul hab]
  ring

theorem successorHeld_additive
    {a b i₁ h₁ i₂ h₂ : ℚ} (hab : a + b ≠ 0) :
    successorHeld a b (i₁ + i₂) (h₁ + h₂) =
      successorHeld a b i₁ h₁ + successorHeld a b i₂ h₂ := by
  dsimp [successorHeld]
  rw [junctionVelocity_additive hab]
  ring

theorem successorHeld_smul
    {a b scalar incoming held : ℚ} (hab : a + b ≠ 0) :
    successorHeld a b (scalar * incoming) (scalar * held) =
      scalar * successorHeld a b incoming held := by
  dsimp [successorHeld]
  rw [junctionVelocity_smul hab]
  ring

/-- Exact scalar coefficient expansion of the emitted current. -/
theorem emitted_coefficient_expansion
    {a b incoming held : ℚ} (hab : a + b ≠ 0) :
    emitted a b incoming held =
      ((a - b) / (a + b)) * incoming + ((2 * b) / (a + b)) * held := by
  dsimp [emitted, junctionVelocity]
  field_simp [hab]
  ring

/-- Exact scalar coefficient expansion of the successor-held current. -/
theorem successorHeld_coefficient_expansion
    {a b incoming held : ℚ} (hab : a + b ≠ 0) :
    successorHeld a b incoming held =
      ((2 * a) / (a + b)) * incoming + ((b - a) / (a + b)) * held := by
  dsimp [successorHeld, junctionVelocity]
  field_simp [hab]
  ring

def phaseEmitted (a b : ℚ) (incoming held : Phase) : Phase :=
  (emitted a b incoming.1 held.1, emitted a b incoming.2 held.2)

def phaseSuccessorHeld (a b : ℚ) (incoming held : Phase) : Phase :=
  (successorHeld a b incoming.1 held.1, successorHeld a b incoming.2 held.2)

def phaseWeightedSquareEnergy (a b : ℚ) (incoming held : Phase) : ℚ :=
  a * (incoming.1 ^ 2 + incoming.2 ^ 2) +
    b * (held.1 ^ 2 + held.2 ^ 2)

theorem phase_weighted_square_energy
    {a b : ℚ} (ha : 0 < a) (hb : 0 < b) (incoming held : Phase) :
    phaseWeightedSquareEnergy a b (phaseEmitted a b incoming held)
        (phaseSuccessorHeld a b incoming held) =
      phaseWeightedSquareEnergy a b incoming held := by
  dsimp [phaseWeightedSquareEnergy, phaseEmitted, phaseSuccessorHeld]
  have first := weighted_square_energy ha hb (incoming := incoming.1) (held := held.1)
  have second := weighted_square_energy ha hb (incoming := incoming.2) (held := held.2)
  linarith

def phaseRotate (c s : ℚ) (phase : Phase) : Phase :=
  (c * phase.1 - s * phase.2, s * phase.1 + c * phase.2)

def phaseNormSquare (phase : Phase) : ℚ := phase.1 ^ 2 + phase.2 ^ 2

theorem phaseRotate_normSquare
    {c s : ℚ} (unit : c ^ 2 + s ^ 2 = 1) (phase : Phase) :
    phaseNormSquare (phaseRotate c s phase) = phaseNormSquare phase := by
  dsimp [phaseNormSquare, phaseRotate]
  nlinarith

/-- Simultaneous rational phase rechart preserves the scalar norm of each incidence. -/
theorem phase_weighted_square_energy_norm_covariant
    {c s : ℚ} (unit : c ^ 2 + s ^ 2 = 1) (phase : Phase) :
    phaseNormSquare (phaseRotate c s phase) = phaseNormSquare phase :=
  phaseRotate_normSquare unit phase

theorem phaseEmitted_rotate_covariant
    {a b c s : ℚ} (hab : a + b ≠ 0) (incoming held : Phase) :
    phaseEmitted a b (phaseRotate c s incoming) (phaseRotate c s held) =
      phaseRotate c s (phaseEmitted a b incoming held) := by
  apply Prod.ext <;> dsimp [phaseEmitted, phaseRotate, emitted, junctionVelocity]
  · field_simp [hab]
    ring
  · field_simp [hab]
    ring

theorem phaseSuccessorHeld_rotate_covariant
    {a b c s : ℚ} (hab : a + b ≠ 0) (incoming held : Phase) :
    phaseSuccessorHeld a b (phaseRotate c s incoming) (phaseRotate c s held) =
      phaseRotate c s (phaseSuccessorHeld a b incoming held) := by
  apply Prod.ext <;> dsimp [phaseSuccessorHeld, phaseRotate, successorHeld, junctionVelocity]
  · field_simp [hab]
    ring
  · field_simp [hab]
    ring

/-! ## Relation tickets for one admitted circulation -/

def emittedConstitutiveRelation {I : Type*}
    (a b : ℚ) (incoming held : I → Phase) :
    Submodule ℚ ((Phase × Phase) × Phase) :=
  pairedCurrentSubmodule (fun i ↦ (incoming i, held i))
    (fun i ↦ phaseEmitted a b (incoming i) (held i))

def successorConstitutiveRelation {I : Type*}
    (a b : ℚ) (incoming held : I → Phase) :
    Submodule ℚ ((Phase × Phase) × Phase) :=
  pairedCurrentSubmodule (fun i ↦ (incoming i, held i))
    (fun i ↦ phaseSuccessorHeld a b (incoming i) (held i))

theorem emitted_ticket_admitted {I : Type*}
    (a b : ℚ) (incoming held : I → Phase) (i : I) :
    ((incoming i, held i), phaseEmitted a b (incoming i) (held i)) ∈
      emittedConstitutiveRelation a b incoming held := by
  exact Submodule.subset_span ⟨i, rfl⟩

theorem successor_ticket_admitted {I : Type*}
    (a b : ℚ) (incoming held : I → Phase) (i : I) :
    ((incoming i, held i), phaseSuccessorHeld a b (incoming i) (held i)) ∈
      successorConstitutiveRelation a b incoming held := by
  exact Submodule.subset_span ⟨i, rfl⟩

/-! ## Unequal-admittance and joint-rechart controls -/

theorem unequal_admittance_sameIncoming_heldChangesEmitted :
    emitted 2 1 0 1 ≠ emitted 2 1 0 2 := by
  norm_num [emitted, junctionVelocity]

theorem joint_phase_rechart_preserves_outputs
    {a b c s : ℚ} (hab : a + b ≠ 0) (incoming held : Phase) :
    phaseEmitted a b (phaseRotate c s incoming) (phaseRotate c s held) =
        phaseRotate c s (phaseEmitted a b incoming held) ∧
      phaseSuccessorHeld a b (phaseRotate c s incoming) (phaseRotate c s held) =
        phaseRotate c s (phaseSuccessorHeld a b incoming held) := by
  exact ⟨phaseEmitted_rotate_covariant hab incoming held,
    phaseSuccessorHeld_rotate_covariant hab incoming held⟩

/-! ## One finite-node circulation event -/

structure CirculationState (Node : Type*) [Fintype Node] where
  /-- Positive local admittances, seeded per node. -/
  a : Node → ℚ
  b : Node → ℚ
  positive_a : ∀ node, 0 < a node
  positive_b : ∀ node, 0 < b node
  /-- A fixed rational phase rechart seeded independently at each node. -/
  rotationReal : Node → ℚ
  rotationImag : Node → ℚ
  unit_rotation : ∀ node, rotationReal node ^ 2 + rotationImag node ^ 2 = 1
  /-- The held field is not conflated with the incoming field. -/
  held : Node → Phase
  /-- Complete source/return relation accumulated by this local owner. -/
  relation : Submodule ℚ ((Node → Phase) × Phase)
  /-- Previously emitted source fields, retained as addressed tickets. -/
  issued : List (Node → Phase)

def generatedSource {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase) : Node → Phase :=
  fun node ↦ phaseEmitted (state.a node) (state.b node)
    (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
    (state.held node)

def generatedSuccessorHeld {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase) : Node → Phase :=
  fun node ↦ phaseSuccessorHeld (state.a node) (state.b node)
    (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
    (state.held node)

def joinIssuedContact {Node : Type*} [Fintype Node]
    (relation : Submodule ℚ ((Node → Phase) × Phase))
    (issued : List (Node → Phase)) (incoming : Phase)
    (handle : Option (Fin issued.length)) : Submodule ℚ ((Node → Phase) × Phase) :=
  match handle with
  | none => relation
  | some handle => relation ⊔ Submodule.span ℚ {(issued.get handle, incoming)}

/-- One ordinary event: only an existing issued handle can add a contact ticket. -/
def circulate {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) : CirculationState Node × (Node → Phase) :=
  let source := generatedSource state incoming
  let relation := joinIssuedContact state.relation state.issued incoming handle
  ({ state with
      held := generatedSuccessorHeld state incoming
      relation := relation
      issued := state.issued ++ [source] }, source)

/-- The graph submodule of a declared local linear constitutive map. -/
def linearGraph {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℚ X] [Module ℚ Y] (M : X →ₗ[ℚ] Y) : Submodule ℚ (X × Y) where
  carrier := {pair | pair.2 = M pair.1}
  zero_mem' := by simp
  add_mem' := by
    intro left right left_mem right_mem
    change left.2 + right.2 = M (left.1 + right.1)
    rw [left_mem, right_mem, M.map_add]
  smul_mem' := by
    intro scalar pair pair_mem
    change scalar • pair.2 = M (scalar • pair.1)
    rw [pair_mem, M.map_smul]

/-- The relation carried by the successor state of one circulation event. -/
def circulateSuccessorRelation {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    Submodule ℚ ((Node → Phase) × Phase) :=
  (circulate state incoming handle).1.relation

/-- Receiver fibre over the generated source field; no representative is selected. -/
def circulateReceiverFibre {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) : Set Phase :=
  {output | (generatedSource state incoming, output) ∈
    circulateSuccessorRelation state incoming handle}

theorem circulate_successor_relation_preserves_linearGraph
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Fin state.issued.length) (M : (Node → Phase) →ₗ[ℚ] Phase)
    (predecessor_graph : state.relation ≤ linearGraph M)
    (linked : incoming = M (state.issued.get handle)) :
    circulateSuccessorRelation state incoming (some handle) ≤ linearGraph M := by
  change state.relation ⊔
      Submodule.span ℚ {(state.issued.get handle, incoming)} ≤ linearGraph M
  apply sup_le
  · exact predecessor_graph
  · apply Submodule.span_le.mpr
    intro pair pair_mem
    rw [Set.mem_singleton_iff] at pair_mem
    rw [pair_mem]
    exact linked

theorem circulate_receiverFibre_member_eq_declared
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Fin state.issued.length) (M : (Node → Phase) →ₗ[ℚ] Phase)
    (predecessor_graph : state.relation ≤ linearGraph M)
    (linked : incoming = M (state.issued.get handle))
    {output : Phase} (member : output ∈
      circulateReceiverFibre state incoming (some handle)) :
    output = M (generatedSource state incoming) := by
  have successor_graph := circulate_successor_relation_preserves_linearGraph
    state incoming handle M predecessor_graph linked
  exact successor_graph member

theorem circulate_source_eq_generated
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    (circulate state incoming handle).2 = generatedSource state incoming := by
  rfl

theorem circulate_held_eq_successor
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) (node : Node) :
    (circulate state incoming handle).1.held node =
      phaseSuccessorHeld (state.a node) (state.b node)
        (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
        (state.held node) := by
  rfl

theorem circulate_source_appended
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    (circulate state incoming handle).2 ∈ (circulate state incoming handle).1.issued := by
  exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem circulate_successor_ticket_admitted
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) (node : Node) :
    ((phaseRotate (state.rotationReal node) (state.rotationImag node) incoming,
        state.held node),
      phaseSuccessorHeld (state.a node) (state.b node)
        (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
        (state.held node)) ∈
      successorConstitutiveRelation (state.a node) (state.b node)
        (fun _ : Unit ↦ phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
        (fun _ ↦ state.held node) := by
  exact successor_ticket_admitted (state.a node) (state.b node)
    (fun _ : Unit ↦ phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
    (fun _ ↦ state.held node) ()

theorem circulate_linked_contact_admitted
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase)
    (handle : Fin state.issued.length) :
    (state.issued.get handle, incoming) ∈
      (circulate state incoming (some handle)).1.relation := by
  change (state.issued.get handle, incoming) ∈
    state.relation ⊔ Submodule.span ℚ {(state.issued.get handle, incoming)}
  exact (le_sup_right : Submodule.span ℚ {(state.issued.get handle, incoming)} ≤
    state.relation ⊔ Submodule.span ℚ {(state.issued.get handle, incoming)})
    (Submodule.subset_span (by simp))

theorem circulate_unlinked_relation_unchanged
    {Node : Type*} [Fintype Node]
    (state : CirculationState Node) (incoming : Phase) :
    (circulate state incoming none).1.relation = state.relation := by
  rfl

end Soma.Holonics.Computation.HolonicConstitutiveCirculation

section Audit
open Soma.Holonics.Computation.HolonicConstitutiveCirculation
#print axioms weighted_square_energy
#print axioms phase_weighted_square_energy
#print axioms emitted_smul
#print axioms successorHeld_smul
#print axioms phaseEmitted_rotate_covariant
#print axioms phaseSuccessorHeld_rotate_covariant
#print axioms emitted_ticket_admitted
#print axioms successor_ticket_admitted
#print axioms unequal_admittance_sameIncoming_heldChangesEmitted
#print axioms circulate_successor_ticket_admitted
#print axioms circulate_linked_contact_admitted
#print axioms circulate_unlinked_relation_unchanged
#print axioms circulate_successor_relation_preserves_linearGraph
#print axioms circulate_receiverFibre_member_eq_declared
end Audit
