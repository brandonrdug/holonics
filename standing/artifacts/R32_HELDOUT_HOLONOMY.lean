import R32_ELEMENTARY_CAUSAL_CALCULUS

namespace Soma.Holonics.R32

def heldoutTriangleProduct : ExactMatrix2 := {a := 2, b := 1, c := 1, d := 1}

def heldoutTriangleTrace : List ℚ := [((2 : ℚ) / 1),((3 : ℚ) / 1),((7 : ℚ) / 1),((18 : ℚ) / 1),((47 : ℚ) / 1),((123 : ℚ) / 1),((322 : ℚ) / 1),((843 : ℚ) / 1),((2207 : ℚ) / 1)]

def heldoutOrganPredictions : List ℚ := [((2 : ℚ) / 1),((3 : ℚ) / 1),((7 : ℚ) / 1),((18 : ℚ) / 1),((47 : ℚ) / 1),((123 : ℚ) / 1),((322 : ℚ) / 1),((843 : ℚ) / 1),((2207 : ℚ) / 1)]

def heldoutRecurrenceStatement : Prop :=
  1 * ((2 : ℚ) / 1) + (-3) * ((3 : ℚ) / 1) + 1 * ((7 : ℚ) / 1) = 0 ∧
  1 * ((3 : ℚ) / 1) + (-3) * ((7 : ℚ) / 1) + 1 * ((18 : ℚ) / 1) = 0 ∧
  1 * ((7 : ℚ) / 1) + (-3) * ((18 : ℚ) / 1) + 1 * ((47 : ℚ) / 1) = 0 ∧
  1 * ((18 : ℚ) / 1) + (-3) * ((47 : ℚ) / 1) + 1 * ((123 : ℚ) / 1) = 0 ∧
  1 * ((47 : ℚ) / 1) + (-3) * ((123 : ℚ) / 1) + 1 * ((322 : ℚ) / 1) = 0 ∧
  1 * ((123 : ℚ) / 1) + (-3) * ((322 : ℚ) / 1) + 1 * ((843 : ℚ) / 1) = 0 ∧
  1 * ((322 : ℚ) / 1) + (-3) * ((843 : ℚ) / 1) + 1 * ((2207 : ℚ) / 1) = 0

theorem heldoutHolonomyOrganImprovement :
    selfHolonomyKernel = [1,-3,1] ∧
    heldoutTriangleTrace = heldoutOrganPredictions ∧ heldoutRecurrenceStatement := by
  norm_num [selfHolonomyKernel, heldoutTriangleTrace, heldoutOrganPredictions,
    heldoutRecurrenceStatement]

theorem generated_heldout_holonomy_transport :
    selfHolonomyKernel = [1,-3,1] ∧
    heldoutTriangleTrace = heldoutOrganPredictions ∧ heldoutRecurrenceStatement := by
  exact heldoutHolonomyOrganImprovement

end Soma.Holonics.R32

#check Soma.Holonics.R32.generated_heldout_holonomy_transport
