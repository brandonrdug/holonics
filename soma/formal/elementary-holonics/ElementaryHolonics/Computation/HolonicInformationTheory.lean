import ElementaryHolonics.Computation.HolonicNeuralEcology
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Finite information receivers over complete holonic action

Probability, entropy, cross-entropy, and KL divergence are defined here only after a finite,
strictly positive, normalized receiver section has been supplied.  They are real-valued faces of
that section.  The complete action, membrane current, lineage, and morphology return remain prior
objects.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicInformationTheory

open scoped BigOperators
universe uI uN

/-- A strictly positive normalized finite receiver section.  Strict positivity gives a common
support on which logarithmic information faces are defined without silent conventions at zero. -/
structure PositiveProbabilitySection (Index : Type uI) [Fintype Index] where
  mass : Index → ℝ
  positive : ∀ index, 0 < mass index
  normalized : ∑ index, mass index = 1

namespace PositiveProbabilitySection

variable {Index : Type uI} [Fintype Index]

theorem nonnegative (p : PositiveProbabilitySection Index) (index : Index) :
    0 ≤ p.mass index := (p.positive index).le

theorem ne_zero (p : PositiveProbabilitySection Index) (index : Index) :
    p.mass index ≠ 0 := (p.positive index).ne'

/-- Shannon entropy is a scalar receiver face of one complete finite section. -/
def entropy (p : PositiveProbabilitySection Index) : ℝ :=
  -∑ index, p.mass index * Real.log (p.mass index)

/-- Cross-entropy is a scalar receiver face of an ordered pair of complete sections. -/
def crossEntropy (reference emitted : PositiveProbabilitySection Index) : ℝ :=
  -∑ index, reference.mass index * Real.log (emitted.mass index)

/-- KL divergence in its standard likelihood-ratio chart. -/
def klDivergence (reference emitted : PositiveProbabilitySection Index) : ℝ :=
  ∑ index, reference.mass index *
    Real.log (reference.mass index / emitted.mass index)

/-- The ratio and difference-of-logarithms presentations commute on the declared positive
support. -/
theorem klDivergence_eq_logDifference
    (reference emitted : PositiveProbabilitySection Index) :
    reference.klDivergence emitted =
      ∑ index, reference.mass index *
        (Real.log (reference.mass index) - Real.log (emitted.mass index)) := by
  unfold klDivergence
  apply Finset.sum_congr rfl
  intro index hindex
  rw [Real.log_div (reference.ne_zero index) (emitted.ne_zero index)]

/-- Exact finite cross-entropy decomposition.  It is an identity between receiver faces, not an
identification of the two complete distributions or of any native action occurrences. -/
theorem crossEntropy_eq_entropy_add_kl
    (reference emitted : PositiveProbabilitySection Index) :
    reference.crossEntropy emitted =
      reference.entropy + reference.klDivergence emitted := by
  rw [klDivergence_eq_logDifference]
  unfold crossEntropy entropy
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- A probability receiver over native occurrences.  Equal returned sections define one
receiver fibre while retaining every native occurrence in that fibre. -/
structure ProbabilityReceiver (Native : Type uN) where
  observe : Native → PositiveProbabilitySection Index

def ProbabilityReceiver.preimageFibre {Native : Type uN}
    (receiver : ProbabilityReceiver (Index := Index) Native) (face : Index → ℝ) : Set Native :=
  {native | (receiver.observe native).mass = face}

theorem ProbabilityReceiver.sameFibre_of_equalSection {Native : Type uN}
    (receiver : ProbabilityReceiver (Index := Index) Native) {left right : Native}
    (equalSection : (receiver.observe left).mass = (receiver.observe right).mass) :
    left ∈ receiver.preimageFibre (receiver.observe left).mass ∧
      right ∈ receiver.preimageFibre (receiver.observe left).mass := by
  exact ⟨rfl, equalSection.symm⟩

end PositiveProbabilitySection

/-! ## Entropy does not identify the complete probability section -/

def entropyControlLeftMass : Bool → ℝ
  | false => 1 / 3
  | true => 2 / 3

def entropyControlRightMass : Bool → ℝ
  | false => 2 / 3
  | true => 1 / 3

def entropyControlLeft : PositiveProbabilitySection Bool where
  mass := entropyControlLeftMass
  positive := by intro index; cases index <;> norm_num [entropyControlLeftMass]
  normalized := by norm_num [entropyControlLeftMass, Fintype.sum_bool]

def entropyControlRight : PositiveProbabilitySection Bool where
  mass := entropyControlRightMass
  positive := by intro index; cases index <;> norm_num [entropyControlRightMass]
  normalized := by norm_num [entropyControlRightMass, Fintype.sum_bool]

theorem entropyControl_sections_ne :
    entropyControlLeft.mass ≠ entropyControlRight.mass := by
  intro equalMass
  have first := congrFun equalMass false
  norm_num [entropyControlLeft, entropyControlRight, entropyControlLeftMass,
    entropyControlRightMass] at first

theorem entropyControl_equal_entropy :
    entropyControlLeft.entropy = entropyControlRight.entropy := by
  simp [PositiveProbabilitySection.entropy, entropyControlLeft, entropyControlRight,
    entropyControlLeftMass, entropyControlRightMass, Fintype.sum_bool]
  ring

/-- Equal entropy is a genuine many-to-one receiver quotient. -/
theorem entropyFace_doesNotDetermineSection :
    entropyControlLeft.entropy = entropyControlRight.entropy ∧
      entropyControlLeft.mass ≠ entropyControlRight.mass :=
  ⟨entropyControl_equal_entropy, entropyControl_sections_ne⟩

/-! ## Physical crossing precedes scalar cross-entropy -/

/-- The minimal exact physical crossing interface used here.  It has the same target-fibre
potential-drop law as the standing membrane theorem but does not import that actively edited
Millennium dependency closure. -/
structure AddressedPhysicalCrossing
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

def AddressedPhysicalCrossing.returnedPotential
    {Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current :
      Type*}
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current]
    (crossing : AddressedPhysicalCrossing Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current) : InteriorPotential :=
  crossing.interiorPotential - crossing.transport crossing.exteriorPotential

def AddressedPhysicalCrossing.returnedCurrent
    {Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current :
      Type*}
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current]
    (crossing : AddressedPhysicalCrossing Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current) : Current :=
  crossing.admittance crossing.returnedPotential

/-- One physical information occurrence retains the complete addressed membrane contact beside
the later probability/action receiver.  The scalar face is not allowed to replace this product. -/
structure PhysicalCrossEntropyOccurrence
    (Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current
      Action Index : Type*)
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current] [Fintype Index] where
  contact : AddressedPhysicalCrossing Occurrence ExteriorBoundary InteriorBoundary
    ExteriorPotential InteriorPotential Current
  action : Action
  reference : PositiveProbabilitySection Index
  emitted : Action → PositiveProbabilitySection Index

namespace PhysicalCrossEntropyOccurrence

variable
    {Occurrence ExteriorBoundary InteriorBoundary ExteriorPotential InteriorPotential Current
      Action Index : Type*}
    [AddCommGroup ExteriorPotential] [AddCommGroup InteriorPotential]
    [AddCommGroup Current] [Fintype Index]

/-- The complete constitutive current returned by the crossing. -/
def current
    (event : PhysicalCrossEntropyOccurrence Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current Action Index) : Current :=
  event.contact.returnedCurrent

/-- Conventional cross-entropy is a later scalar receiver face of the retained action section. -/
def scalarFace
    (event : PhysicalCrossEntropyOccurrence Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current Action Index) : ℝ :=
  event.reference.crossEntropy (event.emitted event.action)

@[simp] theorem scalarFace_is_receiver_projection
    (event : PhysicalCrossEntropyOccurrence Occurrence ExteriorBoundary InteriorBoundary
      ExteriorPotential InteriorPotential Current Action Index) :
    event.scalarFace =
      -∑ index, event.reference.mass index *
        Real.log ((event.emitted event.action).mass index) := rfl

end PhysicalCrossEntropyOccurrence

end Soma.Holonics.Computation.HolonicInformationTheory

section Audit
open Soma.Holonics.Computation.HolonicInformationTheory
#print axioms PositiveProbabilitySection.klDivergence_eq_logDifference
#print axioms PositiveProbabilitySection.crossEntropy_eq_entropy_add_kl
#print axioms entropyFace_doesNotDetermineSection
#print axioms PhysicalCrossEntropyOccurrence.scalarFace_is_receiver_projection
end Audit
