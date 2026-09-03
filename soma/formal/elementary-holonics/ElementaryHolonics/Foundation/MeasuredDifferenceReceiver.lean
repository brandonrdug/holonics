import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# A scalar face is returned from an addressed difference

**[proved-derived]** This file separates three objects which are often collapsed into one scalar:
an addressed pair of occurrences, its oriented difference in a declared additive chart, and a
receiver reading of that difference.  A magnitude is therefore not primitive data attached to an
occurrence.  It is a (generally non-injective) receiver face of a comparison.

The reconstruction fibre is retained explicitly.  An injective reading reconstructs the chart
difference, while an even reading such as a norm identifies the two orientations.  The final
section proves the exact binary exponential identity: a two-channel normalized exponential face
depends only on the difference of the two potentials and is invariant under a common chart shift.
This does not identify a software activation with a physical law; it identifies their shared exact
receiver quotient when the stated real-valued hypotheses apply.
-/

namespace Soma.Holonics.Foundation.MeasuredDifferenceReceiver

noncomputable section

/-- A typed scalar-producing receiver: first enter an additive chart, then read its difference. -/
structure DifferenceReceiver (X A S : Type*) [AddCommGroup A] where
  chart : X → A
  read : A → S

namespace DifferenceReceiver

variable {X A S : Type*} [AddCommGroup A]

/-- The oriented chart difference carried by the addressed pair. -/
def returnedDifference (receiver : DifferenceReceiver X A S)
    (source target : X) : A :=
  receiver.chart target - receiver.chart source

/-- The receiver face returned from the oriented chart difference. -/
def face (receiver : DifferenceReceiver X A S) (source target : X) : S :=
  receiver.read (receiver.returnedDifference source target)

/-- Every scalar face in this owner factors through its returned difference by construction. -/
theorem face_factors_through_returnedDifference
    (receiver : DifferenceReceiver X A S) (source target : X) :
    receiver.face source target =
      receiver.read (receiver.returnedDifference source target) := rfl

/-- Reversing the addressed pair negates the difference before any scalar reading is taken. -/
@[simp] theorem returnedDifference_reverse
    (receiver : DifferenceReceiver X A S) (source target : X) :
    receiver.returnedDifference target source =
      -receiver.returnedDifference source target := by
  simp [returnedDifference]

/-- The complete population of addressed pairs which one receiver scalar cannot distinguish. -/
def preimageFibre (receiver : DifferenceReceiver X A S) (value : S) : Set (X × X) :=
  {pair | receiver.face pair.1 pair.2 = value}

@[simp] theorem pair_mem_preimageFibre_iff
    (receiver : DifferenceReceiver X A S) (value : S) (source target : X) :
    (source, target) ∈ receiver.preimageFibre value ↔
      receiver.face source target = value := Iff.rfl

/-- An injective reading retains the complete chart difference, though not necessarily the source
and target separately. -/
theorem face_eq_iff_returnedDifference_eq_of_injective
    (receiver : DifferenceReceiver X A S) (hread : Function.Injective receiver.read)
    (source target source' target' : X) :
    receiver.face source target = receiver.face source' target' ↔
      receiver.returnedDifference source target =
        receiver.returnedDifference source' target' := by
  constructor
  · intro h
    exact hread h
  · intro h
    exact congrArg receiver.read h

/-- An even receiver deliberately forgets orientation.  Its fibre contains both directed pairs. -/
theorem face_reverse_of_even
    (receiver : DifferenceReceiver X A S)
    (heven : ∀ difference, receiver.read (-difference) = receiver.read difference)
    (source target : X) :
    receiver.face target source = receiver.face source target := by
  rw [face, returnedDifference_reverse]
  exact heven _

end DifferenceReceiver

/-! ## Length is a comparison face, not an intrinsic scalar label -/

/-- The norm receiver on an additive metric chart. -/
def lengthReceiver (X : Type*) [NormedAddCommGroup X] : DifferenceReceiver X X ℝ where
  chart := id
  read := norm

@[simp] theorem lengthReceiver_face {X : Type*} [NormedAddCommGroup X]
    (source target : X) :
    (lengthReceiver X).face source target = ‖target - source‖ := rfl

/-- Zero measured length is equality of the two addressed chart occurrences. -/
theorem lengthReceiver_face_eq_zero_iff {X : Type*} [NormedAddCommGroup X]
    (source target : X) :
    (lengthReceiver X).face source target = 0 ↔ target = source := by
  rw [lengthReceiver_face, norm_eq_zero]
  exact sub_eq_zero

/-- Length forgets orientation even though its pre-reading difference does not. -/
theorem lengthReceiver_face_reverse {X : Type*} [NormedAddCommGroup X]
    (source target : X) :
    (lengthReceiver X).face target source =
      (lengthReceiver X).face source target := by
  rw [lengthReceiver_face, lengthReceiver_face]
  rw [show source - target = -(target - source) by abel, norm_neg]

/-! ## Ratios of returned differences -/

/-- The returned difference of a real-valued section between two occurrences. -/
def sectionDifference {X : Type*} (reading : X → ℝ) (source target : X) : ℝ :=
  reading target - reading source

/-- A constitutive coefficient measured as one returned difference relative to another. -/
def differenceRatio {X : Type*} (numerator denominator : X → ℝ)
    (source target : X) : ℝ :=
  sectionDifference numerator source target /
    sectionDifference denominator source target

/-- A common affine offset is in the null fibre of a returned section difference. -/
theorem sectionDifference_add_common {X : Type*} (reading : X → ℝ)
    (offset : ℝ) (source target : X) :
    sectionDifference (fun occurrence ↦ reading occurrence + offset) source target =
      sectionDifference reading source target := by
  unfold sectionDifference
  ring

/-- A measured ratio is independent of the independently chosen zero points of its two charts. -/
theorem differenceRatio_add_common {X : Type*} (numerator denominator : X → ℝ)
    (numeratorOffset denominatorOffset : ℝ) (source target : X) :
    differenceRatio
        (fun occurrence ↦ numerator occurrence + numeratorOffset)
        (fun occurrence ↦ denominator occurrence + denominatorOffset)
        source target =
      differenceRatio numerator denominator source target := by
  simp only [differenceRatio, sectionDifference_add_common]

/-- Away from a zero denominator difference, the ratio is exactly its cross-multiplied
constitutive relation. -/
theorem differenceRatio_mul_denominator {X : Type*}
    (numerator denominator : X → ℝ) (source target : X)
    (hdenominator : sectionDifference denominator source target ≠ 0) :
    differenceRatio numerator denominator source target *
        sectionDifference denominator source target =
      sectionDifference numerator source target := by
  exact div_mul_cancel₀ _ hdenominator

/-! ## A binary normalized exponential is a quotient of one potential difference -/

/-- Logistic reading of one oriented potential difference. -/
def logisticDifference (difference : ℝ) : ℝ :=
  Real.exp difference / (1 + Real.exp difference)

/-- The two-channel normalized exponential face before eliminating its common potential. -/
def binaryExponentialFace (firstPotential secondPotential : ℝ) : ℝ :=
  Real.exp secondPotential /
    (Real.exp firstPotential + Real.exp secondPotential)

/-- The exact difference receiver underlying the binary exponential face. -/
def binaryExponentialReceiver : DifferenceReceiver ℝ ℝ ℝ where
  chart := id
  read := logisticDifference

/-- Binary normalization collapses the two potentials to their one oriented difference. -/
theorem binaryExponentialFace_eq_logisticDifference
    (firstPotential secondPotential : ℝ) :
    binaryExponentialFace firstPotential secondPotential =
      logisticDifference (secondPotential - firstPotential) := by
  have hfirst : Real.exp firstPotential ≠ 0 := Real.exp_ne_zero firstPotential
  have hsum : Real.exp firstPotential + Real.exp secondPotential ≠ 0 := by
    positivity
  rw [binaryExponentialFace, logisticDifference, Real.exp_sub]
  field_simp [hfirst, hsum]

/-- The normalized binary face is literally the face of the difference receiver. -/
theorem binaryExponentialFace_eq_receiverFace
    (firstPotential secondPotential : ℝ) :
    binaryExponentialFace firstPotential secondPotential =
      binaryExponentialReceiver.face firstPotential secondPotential := by
  rw [binaryExponentialFace_eq_logisticDifference]
  rfl

/-- A common shift changes neither the difference nor the binary receiver face. -/
theorem binaryExponentialFace_add_common
    (firstPotential secondPotential common : ℝ) :
    binaryExponentialFace (firstPotential + common) (secondPotential + common) =
      binaryExponentialFace firstPotential secondPotential := by
  rw [binaryExponentialFace_eq_logisticDifference,
    binaryExponentialFace_eq_logisticDifference]
  congr 1
  ring

/-- Equal potential differences are exactly sufficient for equal binary exponential faces.  The
converse is intentionally not asserted here; it requires proving injectivity of the chosen scalar
reading and still would not reconstruct the two original potentials. -/
theorem binaryExponentialFace_eq_of_difference_eq
    {firstPotential secondPotential firstPotential' secondPotential' : ℝ}
    (hdifference : secondPotential - firstPotential =
      secondPotential' - firstPotential') :
    binaryExponentialFace firstPotential secondPotential =
      binaryExponentialFace firstPotential' secondPotential' := by
  rw [binaryExponentialFace_eq_logisticDifference,
    binaryExponentialFace_eq_logisticDifference, hdifference]

section Audit

#print axioms DifferenceReceiver.returnedDifference_reverse
#print axioms lengthReceiver_face_eq_zero_iff
#print axioms differenceRatio_add_common
#print axioms differenceRatio_mul_denominator
#print axioms binaryExponentialFace_eq_logisticDifference
#print axioms binaryExponentialFace_eq_receiverFace
#print axioms binaryExponentialFace_add_common

end Audit

end

end Soma.Holonics.Foundation.MeasuredDifferenceReceiver
