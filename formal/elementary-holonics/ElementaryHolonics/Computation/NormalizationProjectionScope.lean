import Mathlib.Tactic

/-! Elementary domain/sign controls for the projection step in the continuous Transformer
interpretation. The normal cone uses its standard outward convention. The controls expose
the source hypotheses required by the normalization formula, rather than rejecting the
operator-splitting construction. -/

namespace Soma.Holonics.Computation.NormalizationProjectionScope

def nonnegativeNormal (point normal : ℝ) : Prop :=
  0 ≤ point ∧ ∀ feasible : ℝ, 0 ≤ feasible → normal * (feasible - point) ≤ 0

/-- For input -1 and its projection 0, input-minus-projection is the outward normal. -/
theorem projection_normal_sign :
    nonnegativeNormal 0 (-1) ∧ ¬nonnegativeNormal 0 1 := by
  constructor
  · constructor
    · norm_num
    · intro z hz
      simp only [sub_zero, neg_mul, one_mul]
      linarith
  · intro wrong
    have h := wrong.2 1 (by norm_num)
    norm_num at h

def meanZeroUnitVariance (x y : ℝ) : Prop :=
  (x+y)/2 = 0 ∧ (x^2+y^2)/2 = 1

/-- At a constant input the centered sphere has multiple nearest directions. -/
theorem constant_input_retains_two_directions :
    meanZeroUnitVariance 1 (-1) ∧ meanZeroUnitVariance (-1) 1 ∧
      (1 : ℝ)^2 + (-1)^2 = (-1)^2 + 1^2 ∧ (1 : ℝ) ≠ -1 ∧
      ∀ x y, meanZeroUnitVariance x y → x^2+y^2=2 := by
  refine ⟨by norm_num [meanZeroUnitVariance], by norm_num [meanZeroUnitVariance],
    by norm_num, by norm_num, ?_⟩
  intro x y feasible
  linarith [feasible.2]

/-- Per-feature learned gain changes the mean/variance surface after normalization. -/
theorem anisotropic_gain_changes_constraint_face :
    meanZeroUnitVariance (-1) 1 ∧ ¬meanZeroUnitVariance (-1) 2 := by
  norm_num [meanZeroUnitVariance]

end Soma.Holonics.Computation.NormalizationProjectionScope
