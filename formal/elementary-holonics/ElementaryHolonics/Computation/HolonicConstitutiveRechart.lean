import ElementaryHolonics.Computation.HolonicConstitutiveCirculation
import ElementaryHolonics.Computation.HolonicConstitutiveFibre
import Mathlib.Tactic

/-!
# A fixed-node phase rechart of one constitutive circulation

This is a coordinate rebase of the local circulation owner.  The node set and its admittances stay
fixed; each node receives a rational unit phase gauge, with no permutation or new receiver chart.
Held fields, rotation seeds, issued source fields, and the source side of the accumulated relation
travel together.  Root incoming and returned receiver values remain in their existing chart.
-/

namespace Soma.Holonics.Computation.HolonicConstitutiveRechart

open Soma.Holonics
open HolonicConstitutiveFibre
open HolonicConstitutiveCirculation

abbrev Phase := HolonicConstitutiveCirculation.Phase

universe uNode

/-- A fixed rational unit phase gauge at every existing node. -/
structure PhaseGauge (Node : Type*) [Fintype Node] where
  real : Node → ℚ
  imag : Node → ℚ
  unit : ∀ node, real node ^ 2 + imag node ^ 2 = 1

/-- A unit rational phase rotation is an explicit linear equivalence with its inverse rotation. -/
def phaseRotateEquiv (c s : ℚ) (unit : c ^ 2 + s ^ 2 = 1) :
    Phase ≃ₗ[ℚ] Phase where
  toFun := phaseRotate c s
  invFun := phaseRotate c (-s)
  left_inv phase := by
    ext <;> dsimp [phaseRotate]
    · ring_nf
      linear_combination phase.1 * unit
    · ring_nf
      linear_combination phase.2 * unit
  right_inv phase := by
    ext <;> dsimp [phaseRotate]
    · ring_nf
      linear_combination phase.1 * unit
    · ring_nf
      linear_combination phase.2 * unit
  map_add' left right := by
    ext <;> dsimp [phaseRotate] <;> ring
  map_smul' scalar phase := by
    ext <;> dsimp [phaseRotate] <;> ring

def gaugePhaseEquiv {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (node : Node) : Phase ≃ₗ[ℚ] Phase :=
  phaseRotateEquiv (gauge.real node) (gauge.imag node) (gauge.unit node)

/-- Apply the fixed-node gauge to a whole phase field. -/
def gaugeFieldEquiv {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) : (Node → Phase) ≃ₗ[ℚ] (Node → Phase) where
  toFun field node := (gaugePhaseEquiv gauge node) (field node)
  invFun field node := (gaugePhaseEquiv gauge node).symm (field node)
  left_inv field := by
    funext node
    exact (gaugePhaseEquiv gauge node).left_inv (field node)
  right_inv field := by
    funext node
    exact (gaugePhaseEquiv gauge node).right_inv (field node)
  map_add' left right := by
    funext node
    exact (gaugePhaseEquiv gauge node).map_add (left node) (right node)
  map_smul' scalar field := by
    funext node
    exact (gaugePhaseEquiv gauge node).map_smul scalar (field node)

/-- Transport an immutable earlier source presentation through its actual old and current frames.
The retained source itself need not be overwritten when the live ecology is recharted. -/
def sourceFramePassage {Node : Type*} [Fintype Node]
    (before after : PhaseGauge Node) : (Node → Phase) ≃ₗ[ℚ] (Node → Phase) :=
  (gaugeFieldEquiv before).symm.trans (gaugeFieldEquiv after)

theorem retained_source_frame_transport {Node : Type*} [Fintype Node]
    (before after : PhaseGauge Node) (source : Node → Phase) :
    sourceFramePassage before after (gaugeFieldEquiv before source) =
      gaugeFieldEquiv after source := by
  simp [sourceFramePassage]

theorem sourceFramePassage_composes {Node : Type*} [Fintype Node]
    (first middle last : PhaseGauge Node) (source : Node → Phase) :
    sourceFramePassage middle last (sourceFramePassage first middle source) =
      sourceFramePassage first last source := by
  simp [sourceFramePassage]

def composedRotationReal {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (node : Node) : ℚ :=
  gauge.real node * state.rotationReal node - gauge.imag node * state.rotationImag node

def composedRotationImag {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (node : Node) : ℚ :=
  gauge.imag node * state.rotationReal node + gauge.real node * state.rotationImag node

theorem composed_rotation_apply {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node)
    (node : Node) (incoming : Phase) :
    phaseRotate (composedRotationReal gauge state node)
        (composedRotationImag gauge state node) incoming =
      phaseRotate (gauge.real node) (gauge.imag node)
        (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming) := by
  dsimp [composedRotationReal, composedRotationImag, phaseRotate]
  ring

def gaugePairEquiv {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) :
    ((Node → Phase) × Phase) ≃ₗ[ℚ] ((Node → Phase) × Phase) :=
  pairRechartEquiv (gaugeFieldEquiv gauge) (LinearEquiv.refl ℚ Phase)

/-- Rechart only the source side of the accumulated constitutive relation. -/
def rechartRelation {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node)
    (relation : Submodule ℚ ((Node → Phase) × Phase)) :
    Submodule ℚ ((Node → Phase) × Phase) :=
  rechartedPairedSubmodule (gaugeFieldEquiv gauge) (LinearEquiv.refl ℚ Phase) relation

def mappedIssuedHandle {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) {issued : List (Node → Phase)}
    (handle : Fin issued.length) : Fin (issued.map (gaugeFieldEquiv gauge)).length :=
  ⟨handle.val, by simp⟩

def mappedIssuedOption {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) {issued : List (Node → Phase)}
    (handle : Option (Fin issued.length)) :
    Option (Fin (issued.map (gaugeFieldEquiv gauge)).length) :=
  handle.map (mappedIssuedHandle gauge)

@[simp] theorem issued_get_mapped_handle {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) {issued : List (Node → Phase)}
    (handle : Fin issued.length) :
    (issued.map (gaugeFieldEquiv gauge)).get (mappedIssuedHandle gauge handle) =
      gaugeFieldEquiv gauge (issued.get handle) := by
  simp [mappedIssuedHandle]

theorem rechart_joinIssuedContact {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node)
    (relation : Submodule ℚ ((Node → Phase) × Phase))
    (issued : List (Node → Phase)) (incoming : Phase)
    (handle : Option (Fin issued.length)) :
    rechartRelation gauge (joinIssuedContact relation issued incoming handle) =
      joinIssuedContact (rechartRelation gauge relation)
        (issued.map (gaugeFieldEquiv gauge)) incoming (mappedIssuedOption gauge handle) := by
  cases handle with
  | none => rfl
  | some handle =>
      change Submodule.map (gaugePairEquiv gauge).toLinearMap
          (relation ⊔ Submodule.span ℚ {(issued.get handle, incoming)}) =
        Submodule.map (gaugePairEquiv gauge).toLinearMap relation ⊔
          Submodule.span ℚ {((issued.map (gaugeFieldEquiv gauge)).get
            (mappedIssuedHandle gauge handle), incoming)}
      rw [Submodule.map_sup]
      rw [Submodule.map_span]
      simp only [Set.image_singleton]
      rw [issued_get_mapped_handle]
      rfl

theorem rechart_receiverFibre_iff {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node)
    (relation : Submodule ℚ ((Node → Phase) × Phase))
    (source : Node → Phase) (output : Phase) :
    (gaugeFieldEquiv gauge source, output) ∈ rechartRelation gauge relation ↔
      (source, output) ∈ relation := by
  change (gaugeFieldEquiv gauge source, output) ∈
    rechartedPairedSubmodule (gaugeFieldEquiv gauge) (LinearEquiv.refl ℚ Phase) relation ↔ _
  rw [mem_rechartedPairedSubmodule_iff]
  simp [gaugePairEquiv, pairRechartEquiv]

/-- The admitted source domain is the source projection of the complete paired relation. -/
def sourceDomain {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℚ X] [Module ℚ Y] (relation : Submodule ℚ (X × Y)) : Submodule ℚ X :=
  Submodule.map (LinearMap.fst ℚ X Y) relation

theorem sourceDomain_rechart_covariant {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node)
    (relation : Submodule ℚ ((Node → Phase) × Phase)) :
    sourceDomain (rechartRelation gauge relation) =
      Submodule.map (gaugeFieldEquiv gauge).toLinearMap (sourceDomain relation) := by
  apply le_antisymm
  · intro source source_mem
    rcases (Submodule.mem_map.mp source_mem) with ⟨pair, pair_mem, mapped⟩
    rcases (Submodule.mem_map.mp pair_mem) with ⟨original, original_mem, original_mapped⟩
    refine Submodule.mem_map.mpr ⟨original.1, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨original, original_mem, rfl⟩
    · rw [← mapped, ← original_mapped]
      rfl
  · intro source source_mem
    rcases (Submodule.mem_map.mp source_mem) with ⟨original, original_mem, original_mapped⟩
    rcases (Submodule.mem_map.mp original_mem) with ⟨pair, pair_mem, pair_mapped⟩
    apply Submodule.mem_map.mpr
    refine ⟨(gaugePairEquiv gauge) pair, ?_, ?_⟩
    · apply Submodule.mem_map.mpr
      exact ⟨pair, pair_mem, rfl⟩
    · rw [← original_mapped, ← pair_mapped]
      rfl

/-- Source residuals are equivalent modulo the projected domain in either frame. -/
theorem source_residual_class_rechart_iff {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node)
    (relation : Submodule ℚ ((Node → Phase) × Phase))
    (left right : Node → Phase) :
    left - right ∈ sourceDomain relation ↔
      gaugeFieldEquiv gauge left - gaugeFieldEquiv gauge right ∈
        sourceDomain (rechartRelation gauge relation) := by
  rw [sourceDomain_rechart_covariant]
  constructor
  · intro residual
    apply Submodule.mem_map.mpr
    refine ⟨left - right, residual, ?_⟩
    simp
  · intro residual
    rcases (Submodule.mem_map.mp residual) with ⟨difference, difference_mem, mapped⟩
    have equal : gaugeFieldEquiv gauge difference =
        gaugeFieldEquiv gauge left - gaugeFieldEquiv gauge right := mapped
    have difference_eq : difference = left - right := by
      apply (gaugeFieldEquiv gauge).injective
      rw [equal]
      simp
    rw [← difference_eq]
    exact difference_mem

def rebaseState {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) : CirculationState Node where
  a := state.a
  b := state.b
  positive_a := state.positive_a
  positive_b := state.positive_b
  rotationReal := composedRotationReal gauge state
  rotationImag := composedRotationImag gauge state
  unit_rotation := by
    intro node
    dsimp [composedRotationReal, composedRotationImag]
    nlinarith [gauge.unit node, state.unit_rotation node]
  held := gaugeFieldEquiv gauge state.held
  relation := rechartRelation gauge state.relation
  issued := state.issued.map (gaugeFieldEquiv gauge)

def rebaseIssuedHandle {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node)
    (handle : Fin state.issued.length) : Fin (rebaseState gauge state).issued.length :=
  ⟨handle.val, by simp [rebaseState]⟩

def rebaseIssuedOption {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node)
    (handle : Option (Fin state.issued.length)) :
    Option (Fin (rebaseState gauge state).issued.length) :=
  handle.map (rebaseIssuedHandle gauge state)

theorem generatedSource_rebase_covariant {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase) :
    generatedSource (rebaseState gauge state) incoming =
      gaugeFieldEquiv gauge (generatedSource state incoming) := by
  funext node
  change phaseEmitted (state.a node) (state.b node)
      (phaseRotate (composedRotationReal gauge state node)
        (composedRotationImag gauge state node) incoming)
      (phaseRotate (gauge.real node) (gauge.imag node) (state.held node)) =
    phaseRotate (gauge.real node) (gauge.imag node)
      (phaseEmitted (state.a node) (state.b node)
        (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
        (state.held node))
  rw [composed_rotation_apply]
  rw [phaseEmitted_rotate_covariant
    (admittance_sum_ne_zero (state.positive_a node) (state.positive_b node))]

theorem generatedSuccessorHeld_rebase_covariant {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase) :
    generatedSuccessorHeld (rebaseState gauge state) incoming =
      gaugeFieldEquiv gauge (generatedSuccessorHeld state incoming) := by
  funext node
  change phaseSuccessorHeld (state.a node) (state.b node)
      (phaseRotate (composedRotationReal gauge state node)
        (composedRotationImag gauge state node) incoming)
      (phaseRotate (gauge.real node) (gauge.imag node) (state.held node)) =
    phaseRotate (gauge.real node) (gauge.imag node)
      (phaseSuccessorHeld (state.a node) (state.b node)
        (phaseRotate (state.rotationReal node) (state.rotationImag node) incoming)
        (state.held node))
  rw [composed_rotation_apply]
  rw [phaseSuccessorHeld_rotate_covariant
    (admittance_sum_ne_zero (state.positive_a node) (state.positive_b node))]

theorem rebase_circulate_relation_square {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    rechartRelation gauge (circulate state incoming handle).1.relation =
      (circulate (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle)).1.relation := by
  change rechartRelation gauge
      (joinIssuedContact state.relation state.issued incoming handle) =
    joinIssuedContact (rechartRelation gauge state.relation)
      (state.issued.map (gaugeFieldEquiv gauge)) incoming
        (rebaseIssuedOption gauge state handle)
  cases handle with
  | none => rfl
  | some handle =>
      change rechartRelation gauge
          (joinIssuedContact state.relation state.issued incoming (some handle)) =
        joinIssuedContact (rechartRelation gauge state.relation)
          (state.issued.map (gaugeFieldEquiv gauge)) incoming
          (some (rebaseIssuedHandle gauge state handle))
      simpa [rebaseIssuedOption, mappedIssuedOption, rebaseIssuedHandle,
        mappedIssuedHandle, rebaseState] using
        (rechart_joinIssuedContact gauge state.relation state.issued incoming (some handle))

theorem rebase_circulate_source_square {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    gaugeFieldEquiv gauge (circulate state incoming handle).2 =
      (circulate (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle)).2 := by
  change gaugeFieldEquiv gauge (generatedSource state incoming) =
    generatedSource (rebaseState gauge state) incoming
  exact (generatedSource_rebase_covariant gauge state incoming).symm

theorem rebase_circulate_held_square {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    (rebaseState gauge (circulate state incoming handle).1).held =
      (circulate (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle)).1.held := by
  funext node
  change (gaugePhaseEquiv gauge node)
      (generatedSuccessorHeld state incoming node) =
    generatedSuccessorHeld (rebaseState gauge state) incoming node
  simpa [gaugeFieldEquiv] using
    (congrFun (generatedSuccessorHeld_rebase_covariant gauge state incoming) node).symm

theorem rebase_circulate_issued_square {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) :
    (rebaseState gauge (circulate state incoming handle).1).issued =
      (circulate (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle)).1.issued := by
  change (state.issued ++ [generatedSource state incoming]).map (gaugeFieldEquiv gauge) =
    state.issued.map (gaugeFieldEquiv gauge) ++
      [generatedSource (rebaseState gauge state) incoming]
  rw [List.map_append, generatedSource_rebase_covariant]
  simp

theorem rebase_circulate_receiverFibre_iff {Node : Type*} [Fintype Node]
    (gauge : PhaseGauge Node) (state : CirculationState Node) (incoming : Phase)
    (handle : Option (Fin state.issued.length)) (output : Phase) :
    output ∈ circulateReceiverFibre (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle) ↔
      output ∈ circulateReceiverFibre state incoming handle := by
  change (generatedSource (rebaseState gauge state) incoming, output) ∈
      (circulate (rebaseState gauge state) incoming
        (rebaseIssuedOption gauge state handle)).1.relation ↔
    (generatedSource state incoming, output) ∈
      (circulate state incoming handle).1.relation
  rw [generatedSource_rebase_covariant]
  rw [← rebase_circulate_relation_square]
  exact rechart_receiverFibre_iff gauge
    (circulate state incoming handle).1.relation (generatedSource state incoming) output

end Soma.Holonics.Computation.HolonicConstitutiveRechart

section Audit
open Soma.Holonics.Computation.HolonicConstitutiveRechart
#print axioms phaseRotateEquiv
#print axioms retained_source_frame_transport
#print axioms sourceFramePassage_composes
#print axioms rechart_joinIssuedContact
#print axioms rechart_receiverFibre_iff
#print axioms sourceDomain_rechart_covariant
#print axioms source_residual_class_rechart_iff
#print axioms generatedSource_rebase_covariant
#print axioms generatedSuccessorHeld_rebase_covariant
#print axioms rebase_circulate_relation_square
#print axioms rebase_circulate_source_square
#print axioms rebase_circulate_held_square
#print axioms rebase_circulate_issued_square
#print axioms rebase_circulate_receiverFibre_iff
end Audit
