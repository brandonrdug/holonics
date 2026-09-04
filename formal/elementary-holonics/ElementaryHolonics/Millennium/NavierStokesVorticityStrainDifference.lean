import ElementaryHolonics.Millennium.NavierStokesHodge
import ElementaryHolonics.Millennium.NavierStokesVorticityThreeStrands

/-!
# The strain difference carries the sign of vortex stretching

**[proved-derived]** The local velocity jet splits into symmetric strain and the canonical skew
chart reconstructed from vorticity.  The skew chart annihilates its own vorticity, so the complete
stretching reading is carried by the symmetric fibre.  An explicit pair of divergence-free jets
with the same curl but opposite stretching proves that a curl/magnitude receiver has discarded the
sign-bearing difference required by the critical-vorticity continuation problem.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesVorticityStrainDifference

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesHodge
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- The canonical skew chart has no action along the vorticity which generated it. -/
theorem matrixAction_skewFromVorticity_self (ω : Space) :
    matrixAction (skewFromVorticity ω) ω = 0 := by
  ext i
  fin_cases i <;>
    simp [matrixAction, skewFromVorticity, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- Matrix action preserves the additive incidence of two local jets. -/
theorem matrixAction_add (A B : Matrix3) (u : Space) :
    matrixAction (A + B) u = matrixAction A u + matrixAction B u := by
  ext i
  simp only [matrixAction_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    PiLp.add_apply]

/-- Matrix action preserves an oriented difference of two local jets. -/
theorem matrixAction_sub (A B : Matrix3) (u : Space) :
    matrixAction (A - B) u = matrixAction A u - matrixAction B u := by
  ext i
  simp only [matrixAction_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib,
    PiLp.sub_apply]

/-- A skew Jacobian contributes no signed work along its own curl direction. -/
theorem inner_skewJacobianPart_action_curl_eq_zero (J : Matrix3) :
    inner ℝ (curlFromJacobian J)
        (matrixAction (skewJacobianPart J) (curlFromJacobian J)) = 0 := by
  rw [skewJacobianPart_eq_skewFromVorticity,
    matrixAction_skewFromVorticity_self, inner_zero_right]

/-- The signed local stretching reading is carried exactly by the symmetric strain face. -/
theorem inner_matrixAction_curl_eq_symmetricPart
    (J : Matrix3) :
    inner ℝ (curlFromJacobian J) (matrixAction J (curlFromJacobian J)) =
      inner ℝ (curlFromJacobian J)
        (matrixAction (symmetricJacobianPart J) (curlFromJacobian J)) := by
  calc
    inner ℝ (curlFromJacobian J) (matrixAction J (curlFromJacobian J)) =
        inner ℝ (curlFromJacobian J)
          (matrixAction (symmetricJacobianPart J + skewJacobianPart J)
            (curlFromJacobian J)) := by
              rw [← jacobian_eq_symmetricPart_add_skewPart J]
    _ = inner ℝ (curlFromJacobian J)
          (matrixAction (symmetricJacobianPart J) (curlFromJacobian J) +
            matrixAction (skewJacobianPart J) (curlFromJacobian J)) := by
              rw [matrixAction_add]
    _ = inner ℝ (curlFromJacobian J)
          (matrixAction (symmetricJacobianPart J) (curlFromJacobian J)) := by
              rw [inner_add_right, inner_skewJacobianPart_action_curl_eq_zero, add_zero]

/-- The scalar sign receiver for one local vortex-stretching occurrence. -/
def localVortexStretchingReading (J : Matrix3) : ℝ :=
  inner ℝ (curlFromJacobian J) (matrixAction J (curlFromJacobian J))

/-- A unit vorticity occurrence along the first coordinate axis. -/
def firstAxisVorticity : Space :=
  vectorOfCoordinates ![1, 0, 0]

/-- A trace-free symmetric strain which stretches the first axis and compresses the second. -/
def polarizedTraceFreeStrain : Matrix3 :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- The positive orientation of the same curl/divergence receiver fibre. -/
def positiveStretchJacobian : Matrix3 :=
  skewFromVorticity firstAxisVorticity + polarizedTraceFreeStrain

/-- The negative orientation of the same curl/divergence receiver fibre. -/
def negativeStretchJacobian : Matrix3 :=
  skewFromVorticity firstAxisVorticity - polarizedTraceFreeStrain

/-- Both polarized jets return the same unit vorticity. -/
theorem curl_positiveStretchJacobian :
    curlFromJacobian positiveStretchJacobian = firstAxisVorticity := by
  ext i
  fin_cases i
  all_goals
    simp [positiveStretchJacobian, firstAxisVorticity, polarizedTraceFreeStrain,
      curlFromJacobian, skewFromVorticity] <;> ring

theorem curl_negativeStretchJacobian :
    curlFromJacobian negativeStretchJacobian = firstAxisVorticity := by
  ext i
  fin_cases i
  all_goals
    simp [negativeStretchJacobian, firstAxisVorticity, polarizedTraceFreeStrain,
      curlFromJacobian, skewFromVorticity] <;> ring

/-- Both polarized jets are incompressible at the local trace receiver. -/
theorem divergence_positiveStretchJacobian :
    divergenceFromJacobian positiveStretchJacobian = 0 := by
  norm_num [divergenceFromJacobian, positiveStretchJacobian,
    polarizedTraceFreeStrain, skewFromVorticity, Fin.sum_univ_succ]

theorem divergence_negativeStretchJacobian :
    divergenceFromJacobian negativeStretchJacobian = 0 := by
  norm_num [divergenceFromJacobian, negativeStretchJacobian,
    polarizedTraceFreeStrain, skewFromVorticity, Fin.sum_univ_succ]

/-- The two orientations return opposite unit stretching readings. -/
theorem positiveStretchJacobian_reading :
    localVortexStretchingReading positiveStretchJacobian = 1 := by
  rw [localVortexStretchingReading, curl_positiveStretchJacobian]
  change inner ℝ firstAxisVorticity
    (matrixAction (skewFromVorticity firstAxisVorticity + polarizedTraceFreeStrain)
      firstAxisVorticity) = 1
  rw [matrixAction_add, matrixAction_skewFromVorticity_self, zero_add]
  norm_num [firstAxisVorticity, polarizedTraceFreeStrain, matrixAction,
    dotProduct, PiLp.inner_apply, Fin.sum_univ_succ]

theorem negativeStretchJacobian_reading :
    localVortexStretchingReading negativeStretchJacobian = -1 := by
  rw [localVortexStretchingReading, curl_negativeStretchJacobian]
  change inner ℝ firstAxisVorticity
    (matrixAction (skewFromVorticity firstAxisVorticity - polarizedTraceFreeStrain)
      firstAxisVorticity) = -1
  rw [matrixAction_sub, matrixAction_skewFromVorticity_self, zero_sub]
  norm_num [firstAxisVorticity, polarizedTraceFreeStrain, matrixAction,
    dotProduct, PiLp.inner_apply, Fin.sum_univ_succ]

/-- **[receiver-insufficiency; formal-checked]** Curl and incompressibility return identical
readings on two local jets whose stretching signs are opposite.  The unresolved continuation
receiver must therefore retain the symmetric strain/direction fibre. -/
theorem same_curl_divergence_opposite_stretching :
    curlFromJacobian positiveStretchJacobian =
        curlFromJacobian negativeStretchJacobian ∧
      divergenceFromJacobian positiveStretchJacobian =
        divergenceFromJacobian negativeStretchJacobian ∧
      localVortexStretchingReading positiveStretchJacobian = 1 ∧
      localVortexStretchingReading negativeStretchJacobian = -1 := by
  exact ⟨curl_positiveStretchJacobian.trans curl_negativeStretchJacobian.symm,
    divergence_positiveStretchJacobian.trans divergence_negativeStretchJacobian.symm,
    positiveStretchJacobian_reading, negativeStretchJacobian_reading⟩

section Audit

#print axioms matrixAction_skewFromVorticity_self
#print axioms inner_matrixAction_curl_eq_symmetricPart
#print axioms curl_positiveStretchJacobian
#print axioms curl_negativeStretchJacobian
#print axioms divergence_positiveStretchJacobian
#print axioms divergence_negativeStretchJacobian
#print axioms positiveStretchJacobian_reading
#print axioms negativeStretchJacobian_reading
#print axioms same_curl_divergence_opposite_stretching

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityStrainDifference
