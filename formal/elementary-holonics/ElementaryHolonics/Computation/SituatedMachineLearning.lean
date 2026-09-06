import ElementaryHolonics.Computation.MachineLearningStrictLift
import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Millennium.HolonicComplexParametron
import ElementaryHolonics.Millennium.SituatedReturnedDifference
import Mathlib.Tactic

/-!
# Situated loss, cultivation return, and the fixed Parametron receiver chart

Loss is first a complete returned difference.  A scalar loss is a later receiver face.  It governs
learning only when the durable morphology return itself descends through that face.  The second
half of the file gives one exact configuration in which a pre-locking complex Parametron current
has a traditional real-valued affine receiver chart.

`IsInferenceReturn` below names the zero-morphology special case of this receiver chart, not the
definition of inference throughout HNA. The complete developing operation is owned by
`HolonicRecurrentEcology`; no inference/exterior-cultivation mode split follows from this file.
-/

namespace Soma.Holonics.Computation.SituatedMachineLearning

open Soma.Holonics.Computation.MachineLearningChart
open Soma.Holonics.Millennium.HolonicComplexParametron

universe uB uE uD uL

/--
A learning occurrence retains its complete situated difference and the morphology return caused by
that difference.  `lossFace` is only a declared receiver of the difference.
-/
structure SituatedLearningReturn
    (Body : Type uB) (Exterior : Type uE) (Difference : Type uD) (LossFace : Type uL) where
  difference : Body → Exterior → Difference
  lossFace : Difference → LossFace
  returnMorphology : Difference → Body → Body

namespace SituatedLearningReturn

variable {Body : Type uB} {Exterior : Type uE} {Difference : Type uD} {LossFace : Type uL}
  (L : SituatedLearningReturn Body Exterior Difference LossFace)

/-- Inference at this boundary means that the return leaves reusable morphology unchanged. -/
def IsInferenceReturn : Prop :=
  ∀ difference body, L.returnMorphology difference body = body

/-- Cultivation is witnessed locally by one returned difference changing the continuing body. -/
def IsCultivationAt (difference : Difference) (body : Body) : Prop :=
  L.returnMorphology difference body ≠ body

/-- A witnessed cultivation occurrence cannot simultaneously be a zero-morphology inference return. -/
theorem cultivation_excludes_inference {difference : Difference} {body : Body}
    (cultivates : L.IsCultivationAt difference body) :
    ¬ L.IsInferenceReturn := by
  intro inference
  exact cultivates (inference difference body)

/-- The durable return descends through scalar loss only when one loss-indexed return determines it. -/
def ReturnDescendsThroughLoss : Prop :=
  ∃ descendedReturn : LossFace → Body → Body,
    ∀ difference body,
      L.returnMorphology difference body = descendedReturn (L.lossFace difference) body

/-- If return truly descends through loss, equal loss faces force equal morphology returns. -/
theorem equalLoss_forces_equalReturn
    (descends : L.ReturnDescendsThroughLoss)
    {left right : Difference} (sameLoss : L.lossFace left = L.lossFace right)
    (body : Body) :
    L.returnMorphology left body = L.returnMorphology right body := by
  rcases descends with ⟨descendedReturn, exactReturn⟩
  rw [exactReturn, exactReturn, sameLoss]

/-- Two equal scalar losses causing different morphology are a shortest obstruction to scalar loss. -/
theorem equalLoss_differentReturn_obstructsDescent
    {left right : Difference} (sameLoss : L.lossFace left = L.lossFace right)
    {body : Body} (differentReturn :
      L.returnMorphology left body ≠ L.returnMorphology right body) :
    ¬ L.ReturnDescendsThroughLoss := by
  intro descends
  exact differentReturn (L.equalLoss_forces_equalReturn descends sameLoss body)

end SituatedLearningReturn

/-! ## A finite scalar-loss separator -/

namespace LossControl

/-- A conventional squared-magnitude receiver on a two-current integer difference. -/
def squaredMagnitude (difference : ℤ × ℤ) : ℤ :=
  difference.1 ^ 2 + difference.2 ^ 2

/-- The complete oriented difference changes its corresponding body coordinates. -/
def orientedReturn (difference body : ℤ × ℤ) : ℤ × ℤ :=
  body + difference

def learningReturn : SituatedLearningReturn (ℤ × ℤ) Unit (ℤ × ℤ) ℤ where
  difference body _ := body
  lossFace := squaredMagnitude
  returnMorphology := orientedReturn

theorem orthogonalDifferences_sameScalarLoss :
    learningReturn.lossFace (1, 0) = learningReturn.lossFace (0, 1) := by
  norm_num [learningReturn, squaredMagnitude]

theorem orthogonalDifferences_distinctReturn :
    learningReturn.returnMorphology (1, 0) (0, 0) ≠
      learningReturn.returnMorphology (0, 1) (0, 0) := by
  norm_num [learningReturn, orientedReturn]

/-- Equal squared scalar loss does not determine the oriented morphology return. -/
theorem scalarLossDoesNotDetermineCultivation :
    ¬ learningReturn.ReturnDescendsThroughLoss :=
  learningReturn.equalLoss_differentReturn_obstructsDescent
    orthogonalDifferences_sameScalarLoss orthogonalDifferences_distinctReturn

end LossControl

/-! ## The traditional affine chart of one real-phase Parametron current -/

namespace ParametronChart

/-- A fixed real constitutive gain acts on the complete pre-locking complex current. -/
def complexConstitutiveStep (gain : ℝ) (current : ℂ) : ℂ :=
  (gain : ℂ) * current

/-- The corresponding traditional real affine preactivation. -/
def realAffineStep (gain current : ℝ) : ℝ :=
  gain * current

/-- The real receiver chart of a pre-locking complex Parametron current. -/
def realCurrentFace (current : ℂ) : ℝ := current.re

/--
With fixed real gain, the complete complex current has an exact traditional real receiver chart.
The imaginary phase remains in the reconstruction fibre; no equality with the native current is
claimed.
-/
def fixedRealPhaseChart (gain : ℝ) :
    DynamicReceiverChart Unit Unit ℂ ℝ ℝ where
  quotient := realCurrentFace
  nativeStep _ := complexConstitutiveStep gain
  classicalStep _ := realAffineStep gain
  nativeObserve _ := realCurrentFace
  classicalObserve _ := _root_.id
  observeExact := by intros; rfl
  generatorExact := by
    intro _ current
    simp [realCurrentFace, complexConstitutiveStep, realAffineStep, Complex.mul_re]

theorem fixedRealPhaseChart_everyRecurrence (gain : ℝ) (word : List Unit) (current : ℂ) :
    (fixedRealPhaseChart gain).quotient
        (Soma.Holonics.Millennium.Chronology.transportWord
          (fixedRealPhaseChart gain).nativeStep word current) =
      Soma.Holonics.Millennium.Chronology.transportWord
        (fixedRealPhaseChart gain).classicalStep word
        ((fixedRealPhaseChart gain).quotient current) :=
  (fixedRealPhaseChart gain).everyOrderedWordExact word current

/-- The classical preactivation of one full Parametron receiver face. -/
def classicalPotential (face : ParametronReceiverFace) : ℝ :=
  face.complexCurrent.re

/-- The phase quadrature deliberately retained behind that classical face. -/
def retainedQuadrature (face : ParametronReceiverFace) : ℝ :=
  face.complexCurrent.im

/-- Two native Parametron faces can agree classically while retaining distinct phase quadrature. -/
theorem equalClassicalPotential_canRetainDifferentQuadrature :
    let inPhase : ParametronReceiverFace :=
      { complexCurrent := 0, diagonalContribution := 0 }
    let quadrature : ParametronReceiverFace :=
      { complexCurrent := Complex.I, diagonalContribution := 0 }
    classicalPotential inPhase = classicalPotential quadrature ∧
      retainedQuadrature inPhase ≠ retainedQuadrature quadrature := by
  norm_num [classicalPotential, retainedQuadrature]

end ParametronChart

/-! ## A finite orientation control for a situated receiver -/

namespace OrientationControl

open Soma.Holonics.Millennium.HolonicComplexParametron

/-- One scalar node coordinate shared by two branch-orientation charts. -/
def scalarState : Unit → ℝ := fun _ ↦ 1

/-- Equal branch drive in the two-branch control. -/
def branchDrive : Bool → ℝ := fun _ ↦ 1

/-- Equal unoriented branch incidence in the two-branch control. -/
def branchIncidence : Bool → Unit → ℝ := fun _ _ ↦ 1

/-- One orientation chart leaves both branches alone; the other reverses the second branch. -/
def selected (orientation : Bool) : Bool → Bool :=
  fun branch ↦ orientation && branch

/-- The returned drive action when only incidence is reoriented. -/
def untransportedAction (orientation : Bool) : ℝ :=
  driveAction branchDrive
    (reorientIncidence (selected orientation) branchIncidence) scalarState

theorem sameScalar_differentUntransportedOrientation :
    (untransportedAction false : ℝ) ≠ untransportedAction true := by
  norm_num [untransportedAction, branchDrive, branchIncidence, scalarState,
    selected, driveAction, branchDrop, reorientIncidence, orientationSign]

/-- The same scalar entering coordinate carries two distinct returned actions. -/
def orientationInsufficiency : ReceiverInsufficiency
    (fun _ : Bool ↦ (1 : ℝ)) untransportedAction where
  left := false
  right := true
  sameEntering := rfl
  differentReturned := sameScalar_differentUntransportedOrientation

/-- Forgetting branch orientation cannot define this action from the scalar coordinate alone. -/
theorem untransportedOrientation_noReceiverTransformer :
    ¬ Nonempty (ReceiverTransformer
      (fun _ : Bool ↦ (1 : ℝ)) untransportedAction) := by
  rintro ⟨transformer⟩
  exact transformer.excludesInsufficiency orientationInsufficiency

/-- Transporting the drive covector with incidence preserves the action on the same state. -/
theorem transportingDriveWithIncidence_preservesAction :
    driveAction (reorientDrive (selected true) branchDrive)
        (reorientIncidence (selected true) branchIncidence) scalarState =
      driveAction branchDrive branchIncidence scalarState := by
  exact driveAction_reorientBoth (selected true) branchDrive branchIncidence scalarState

end OrientationControl

end Soma.Holonics.Computation.SituatedMachineLearning

section Audit
open Soma.Holonics.Computation.SituatedMachineLearning
#print axioms SituatedLearningReturn.cultivation_excludes_inference
#print axioms SituatedLearningReturn.equalLoss_forces_equalReturn
#print axioms SituatedLearningReturn.equalLoss_differentReturn_obstructsDescent
#print axioms LossControl.scalarLossDoesNotDetermineCultivation
#print axioms ParametronChart.fixedRealPhaseChart_everyRecurrence
#print axioms ParametronChart.equalClassicalPotential_canRetainDifferentQuadrature
#print axioms OrientationControl.sameScalar_differentUntransportedOrientation
#print axioms OrientationControl.untransportedOrientation_noReceiverTransformer
#print axioms OrientationControl.transportingDriveWithIncidence_preservesAction
end Audit
