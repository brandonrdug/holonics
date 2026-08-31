import ElementaryHolonics.Foundation.MeasuredDifferenceReceiver
import ElementaryHolonics.Millennium.HolonicComplexParametron
import ElementaryHolonics.Millennium.HolonicEntropyActionInduction
import ElementaryHolonics.Millennium.SituatedReturnedDifference
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# An addressed constitutive membrane and its scalar cross-entropy receiver

**[proved-derived]** A membrane crossing is an addressed occurrence with two boundary maps.  Its
potential drop is formed in the interior target fibre, after transporting the exterior potential
through a declared chart passage.  A constitutive admittance then returns current.  The complete
drop is prior to every scalar receiver.

The first section proves that source, target, and current chart changes preserve this current only
when both the potential transport and the constitutive map commute.  The existing coupled
Complex-Parametron theorem then supplies the contact-local mixing law: incidence and the complete
two-index constitutive form must be reoriented together.

The final section defines conventional finite cross-entropy only after a normalized reference
population and a strictly positive normalized receiver section have been declared.  It is one real
receiver face, with a complete reconstruction fibre.  A concrete three-member population proves
that equal cross-entropy does not identify receiver sections, and a separating successor cannot
factor through that scalar.  No theorem identifies this receiver with microscopic probability,
uses it to select membrane support, or deposits it as morphology.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicMembraneActionTransport

open scoped BigOperators
open Soma.Holonics.Foundation.MeasuredDifferenceReceiver
open Soma.Holonics.Millennium.HolonicComplexParametron

/-! ## The complete addressed membrane contact -/

/-- One caused crossing from an exterior boundary occurrence into an interior boundary
occurrence.  Potentials may initially occupy different additive fibres. -/
structure AddressedMembraneContact
    (Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current :
      Type*)
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current] where
  occurrence : Occurrence
  exteriorBoundary : ExteriorBoundary
  interiorBoundary : InteriorBoundary
  exteriorPotential : ExteriorPotential
  interiorPotential : InteriorPotential
  transport : ExteriorPotential →+ InteriorPotential
  admittance : InteriorPotential →+ Current

namespace AddressedMembraneContact

variable
    {Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current :
      Type*}
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current]

/-- The oriented potential drop belongs to the interior target fibre. -/
def returnedPotential
    (contact : AddressedMembraneContact Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current) : InteriorPotential :=
  contact.interiorPotential - contact.transport contact.exteriorPotential

/-- Constitutive current is a response to the complete target-fibre potential drop. -/
def returnedCurrent
    (contact : AddressedMembraneContact Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current) : Current :=
  contact.admittance contact.returnedPotential

/-- A receiver face of membrane current factors through the complete returned current. -/
def receiverFace
    {Reading : Type*}
    (contact : AddressedMembraneContact Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current)
    (receiver : Current → Reading) : Reading :=
  receiver contact.returnedCurrent

/-- The complete contact population retained by one receiver reading. -/
def reconstructionFiber
    {Reading : Type*}
    (receiver : Current → Reading) (reading : Reading) :
    Set (AddressedMembraneContact Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current) :=
  {contact | contact.receiverFace receiver = reading}

@[simp] theorem receiverFace_factors_through_returnedCurrent
    {Reading : Type*}
    (contact : AddressedMembraneContact Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current)
    (receiver : Current → Reading) :
    contact.receiverFace receiver = receiver contact.returnedCurrent := rfl

end AddressedMembraneContact

/-! ## Simultaneous chart transport -/

/-- If the exterior/interior transport square and the constitutive/current square commute, the
returned membrane current rebases naturally.  Moving only one face is therefore an intervention,
not a chart change. -/
theorem membraneCurrent_rebase
    {ExteriorPotential InteriorPotential Current
      ExteriorPotential' InteriorPotential' Current' : Type*}
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential] [AddCommGroup Current]
    [AddCommGroup ExteriorPotential'] [AddCommGroup InteriorPotential'] [AddCommGroup Current']
    (sourceChart : ExteriorPotential ≃+ ExteriorPotential')
    (targetChart : InteriorPotential ≃+ InteriorPotential')
    (currentChart : Current ≃+ Current')
    (transport : ExteriorPotential →+ InteriorPotential)
    (transport' : ExteriorPotential' →+ InteriorPotential')
    (admittance : InteriorPotential →+ Current)
    (admittance' : InteriorPotential' →+ Current')
    (transportSquare : ∀ potential,
      transport' (sourceChart potential) = targetChart (transport potential))
    (constitutiveSquare : ∀ potential,
      admittance' (targetChart potential) = currentChart (admittance potential))
    (exterior : ExteriorPotential) (interior : InteriorPotential) :
    admittance'
        (targetChart interior - transport' (sourceChart exterior)) =
      currentChart (admittance (interior - transport exterior)) := by
  rw [transportSquare, ← targetChart.map_sub, constitutiveSquare]

/-! ## Contact-local coupled response -/

/-- The membrane's contact-local mutual response is the existing Complex-Parametron response.
The theorem records that arbitrary organs may mix only through founded incidence and the complete
off-diagonal constitutive table, both transported together. -/
theorem localMembraneMixing_reorient
    {Node Branch : Type*} [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (coupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) (node : Node) :
    coupledResponse (reorientCoupling selected coupling)
        (reorientIncidence selected incidence) state node =
      coupledResponse coupling incidence state node :=
  coupledResponse_reorient selected coupling incidence state node

/-- A branch-disjoint coupling row returns no response at that branch.  This is the finite
negative control for indiscriminate all-to-all mixing. -/
theorem localMembraneMixing_zero_of_couplingRow_zero
    {Node Branch : Type*} [Fintype Node] [Fintype Branch]
    (coupling : Branch → Branch → ℝ) (incidence : Branch → Node → ℝ)
    (state : Node → ℝ) (node : Node)
    (rowZero : ∀ first, incidence first node = 0) :
    coupledResponse coupling incidence state node = 0 := by
  unfold coupledResponse
  apply Finset.sum_eq_zero
  intro first hfirst
  rw [rowZero first, zero_mul]

/-! ## Cross-entropy is a declared receiver face -/

/-- Conventional finite cross-entropy.  Positivity and normalization belong to the receiver
chart below; this raw expression is kept separate so its exact quotient can be inspected. -/
def finiteCrossEntropy {Index : Type*} [Fintype Index]
    (reference emitted : Index → ℝ) : ℝ :=
  -∑ index, reference index * Real.log (emitted index)

/-- A probability receiver chart for one action population.  The action itself remains arbitrary;
only its emitted receiver section is assigned normalized positive coordinates. -/
structure FiniteCrossEntropyReceiver (Action Index : Type*) [Fintype Index] where
  reference : Index → ℝ
  emitted : Action → Index → ℝ
  reference_nonnegative : ∀ index, 0 ≤ reference index
  reference_normalized : ∑ index, reference index = 1
  emitted_positive : ∀ action index, 0 < emitted action index
  emitted_normalized : ∀ action, ∑ index, emitted action index = 1

namespace FiniteCrossEntropyReceiver

variable {Action Index : Type*} [Fintype Index]

/-- The scalar face returned after the complete action has entered the probability chart. -/
def face (receiver : FiniteCrossEntropyReceiver Action Index) (action : Action) : ℝ :=
  finiteCrossEntropy receiver.reference (receiver.emitted action)

/-- The complete population of actions one scalar cross-entropy reading cannot distinguish. -/
def reconstructionFiber (receiver : FiniteCrossEntropyReceiver Action Index) (reading : ℝ) :
    Set Action :=
  {action | receiver.face action = reading}

@[simp] theorem mem_reconstructionFiber_iff
    (receiver : FiniteCrossEntropyReceiver Action Index) (reading : ℝ) (action : Action) :
    action ∈ receiver.reconstructionFiber reading ↔ receiver.face action = reading := Iff.rfl

/-- Equal cross-entropy puts two actions in one receiver fibre; it does not identify them. -/
theorem same_fibre_of_equal_face
    (receiver : FiniteCrossEntropyReceiver Action Index) {left right : Action}
    (equalFace : receiver.face left = receiver.face right) :
    left ∈ receiver.reconstructionFiber (receiver.face left) ∧
      right ∈ receiver.reconstructionFiber (receiver.face left) := by
  exact ⟨rfl, equalFace.symm⟩

/-- If a later receiver separates two equal-cross-entropy actions, that successor cannot factor
through the scalar cross-entropy face. -/
theorem no_successor_factor_of_equal_face
    {Successor : Type*}
    (receiver : FiniteCrossEntropyReceiver Action Index)
    (successor : Action → Successor) {left right : Action}
    (equalFace : receiver.face left = receiver.face right)
    (separated : successor left ≠ successor right) :
    ¬ ∃ factor : ℝ → Successor, ∀ action, successor action = factor (receiver.face action) := by
  rintro ⟨factor, factors⟩
  apply separated
  calc
    successor left = factor (receiver.face left) := factors left
    _ = factor (receiver.face right) := congrArg factor equalFace
    _ = successor right := (factors right).symm

end FiniteCrossEntropyReceiver

/-! ## A concrete nontrivial cross-entropy fibre -/

def firstOnlyReference : Fin 3 → ℝ := ![1, 0, 0]
def quarterTailEmission : Fin 3 → ℝ := ![(1 / 2 : ℝ), 1 / 4, 1 / 4]
def splitTailEmission : Fin 3 → ℝ := ![(1 / 2 : ℝ), 1 / 3, 1 / 6]

theorem quarterTailEmission_ne_splitTailEmission :
    quarterTailEmission ≠ splitTailEmission := by
  intro equalSections
  have coordinateOne := congrFun equalSections (1 : Fin 3)
  norm_num [quarterTailEmission, splitTailEmission] at coordinateOne

/-- Two distinct normalized, strictly positive sections return exactly the same cross-entropy
under a receiver supported on their common first coordinate. -/
theorem distinct_sections_equal_crossEntropy :
    finiteCrossEntropy firstOnlyReference quarterTailEmission =
      finiteCrossEntropy firstOnlyReference splitTailEmission := by
  simp [finiteCrossEntropy, firstOnlyReference, quarterTailEmission, splitTailEmission,
    Fin.sum_univ_succ]

theorem firstOnlyReference_normalized : ∑ index, firstOnlyReference index = 1 := by
  norm_num [firstOnlyReference, Fin.sum_univ_succ]

theorem firstOnlyReference_nonnegative : ∀ index, 0 ≤ firstOnlyReference index := by
  intro index
  fin_cases index <;> norm_num [firstOnlyReference]

theorem quarterTailEmission_normalized : ∑ index, quarterTailEmission index = 1 := by
  norm_num [quarterTailEmission, Fin.sum_univ_succ]

theorem quarterTailEmission_positive : ∀ index, 0 < quarterTailEmission index := by
  intro index
  fin_cases index <;> norm_num [quarterTailEmission]

theorem splitTailEmission_normalized : ∑ index, splitTailEmission index = 1 := by
  norm_num [splitTailEmission, Fin.sum_univ_succ]

theorem splitTailEmission_positive : ∀ index, 0 < splitTailEmission index := by
  intro index
  fin_cases index <;> norm_num [splitTailEmission]

/-- One fully admitted receiver whose two Boolean action occurrences occupy the concrete
nontrivial equal-cross-entropy fibre. -/
def tailCrossEntropyReceiver : FiniteCrossEntropyReceiver Bool (Fin 3) where
  reference := firstOnlyReference
  emitted action := if action then quarterTailEmission else splitTailEmission
  reference_nonnegative := firstOnlyReference_nonnegative
  reference_normalized := firstOnlyReference_normalized
  emitted_positive action := by
    cases action with
    | false => exact splitTailEmission_positive
    | true => exact quarterTailEmission_positive
  emitted_normalized action := by
    cases action with
    | false => exact splitTailEmission_normalized
    | true => exact quarterTailEmission_normalized

theorem tailCrossEntropyReceiver_equalFace :
    tailCrossEntropyReceiver.face false = tailCrossEntropyReceiver.face true := by
  exact distinct_sections_equal_crossEntropy.symm

/-- The identity successor separates the concrete equal-face actions, so it cannot factor through
the cross-entropy scalar. -/
theorem tailCrossEntropyReceiver_no_identitySuccessorFactor :
    ¬ ∃ factor : ℝ → Bool, ∀ action,
      action = factor (tailCrossEntropyReceiver.face action) := by
  exact tailCrossEntropyReceiver.no_successor_factor_of_equal_face id
    tailCrossEntropyReceiver_equalFace Bool.false_ne_true

/-- The already-proved binary normalized exponential quotient supplies the common-shift gauge face
used by a two-member probability receiver. -/
theorem binaryNormalizedExponential_commonShift
    (firstPotential secondPotential common : ℝ) :
    binaryExponentialFace (firstPotential + common) (secondPotential + common) =
      binaryExponentialFace firstPotential secondPotential :=
  binaryExponentialFace_add_common firstPotential secondPotential common

section Audit

#print axioms membraneCurrent_rebase
#print axioms localMembraneMixing_reorient
#print axioms localMembraneMixing_zero_of_couplingRow_zero
#print axioms FiniteCrossEntropyReceiver.same_fibre_of_equal_face
#print axioms FiniteCrossEntropyReceiver.no_successor_factor_of_equal_face
#print axioms quarterTailEmission_ne_splitTailEmission
#print axioms distinct_sections_equal_crossEntropy
#print axioms tailCrossEntropyReceiver_equalFace
#print axioms tailCrossEntropyReceiver_no_identitySuccessorFactor
#print axioms binaryNormalizedExponential_commonShift

end Audit

end Soma.Holonics.Millennium.HolonicMembraneActionTransport
