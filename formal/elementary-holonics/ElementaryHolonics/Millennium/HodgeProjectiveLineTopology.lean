import ElementaryHolonics.Millennium.HodgeProjectiveLineCellularCohomology
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The projective-line carrier is the two-sphere

The algebraic atlas and cellular calculation now receive their genuine topology.  We construct an
explicit equivalence between the existing projectivization quotient and the one-point
compactification of `ℂ`: the distinguished point is infinity and the complementary second chart
is the finite complex coordinate.  The topology on the projectivization is transported through
that equivalence, making it a homeomorphism by construction.

Mathlib proves that the one-point compactification of a finite-dimensional real vector space is a
sphere.  Composing that theorem gives an actual homeomorphism

`ℙ¹_ℂ ≃ₜ S²`, and hence `ℙ¹_ℂ × ℙ¹_ℂ ≃ₜ S² × S²`.

This removes the topology/sphere identity from the open Hodge comparison.  It does not by itself
compute singular cohomology or prove the cellular-to-singular comparison.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineTopology

open scoped OnePoint
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology

/-- [definition] Infinity is the distinguished point; a finite complex number is reconstructed in
the second affine chart. -/
def onePointEquivProjectiveLine : OnePoint ℂ ≃ ComplexProjectiveLine := by
  classical
  exact
    { toFun := fun value => value.elim coordinatePoint (point .second)
      invFun := fun projectivePoint => if h : projectivePoint = coordinatePoint then ∞
        else (affineCellEquiv ⟨projectivePoint, h⟩ : ℂ)
      left_inv := by
        intro value
        induction value using OnePoint.rec with
        | infty =>
            change (if _ : coordinatePoint = coordinatePoint then ∞ else _) = ∞
            simp
        | coe z =>
            have hne : point .second z ≠ coordinatePoint := by
              intro hequal
              apply coordinatePoint_not_in_second_chart
              rw [← hequal]
              exact point_mem .second z
            change (if _ : point .second z = coordinatePoint then ∞
              else (affineCellEquiv ⟨point .second z, hne⟩ : ℂ)) = (z : OnePoint ℂ)
            rw [dif_neg hne]
            exact congrArg OnePoint.some (affineCellEquiv.right_inv z)
      right_inv := by
        intro projectivePoint
        by_cases hequal : projectivePoint = coordinatePoint
        · subst projectivePoint
          simp
        · simp only [dif_neg hequal, OnePoint.elim_some]
          exact congrArg Subtype.val
            (affineCellEquiv.left_inv ⟨projectivePoint, hequal⟩) }

/-- [definition] The receiver direction used to transport the topology. -/
def projectiveLineEquivOnePoint : ComplexProjectiveLine ≃ OnePoint ℂ :=
  onePointEquivProjectiveLine.symm

/-- [definition] The projective-line topology is the topology induced from its exact one-point
compactification coordinate. -/
noncomputable instance complexProjectiveLineTopology : TopologicalSpace ComplexProjectiveLine :=
  TopologicalSpace.induced projectiveLineEquivOnePoint inferInstance

/-- [proved-derived; formal-checked] The topology transport is an actual homeomorphism. -/
def projectiveLineHomeomorphOnePoint : ComplexProjectiveLine ≃ₜ OnePoint ℂ :=
  projectiveLineEquivOnePoint.toHomeomorphOfIsInducing
    (Topology.IsInducing.induced projectiveLineEquivOnePoint)

/-- [proved-derived; formal-checked] The projective line is compact in the transported topology. -/
noncomputable instance complexProjectiveLineCompact : CompactSpace ComplexProjectiveLine :=
  projectiveLineHomeomorphOnePoint.symm.compactSpace

/-- [proved-derived; formal-checked] The projective line is Hausdorff in the transported topology. -/
noncomputable instance complexProjectiveLineT2 : T2Space ComplexProjectiveLine :=
  projectiveLineHomeomorphOnePoint.symm.t2Space

/-- [proved-derived; formal-checked] The one-point compactification of `ℂ ≃ ℝ²` is the unit
two-sphere in `ℝ³`. -/
def onePointComplexHomeomorphTwoSphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by norm_num [Complex.finrank_real_complex])

/-- [proved-derived; formal-checked] The actual projectivization carrier is homeomorphic to `S²`. -/
def projectiveLineHomeomorphTwoSphere :
    ComplexProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  projectiveLineHomeomorphOnePoint.trans onePointComplexHomeomorphTwoSphere

/-- [proved-derived; formal-checked] The Hodge surface carrier is homeomorphic to `S² × S²`. -/
def surfaceHomeomorphSphereProduct :
    Surface ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  projectiveLineHomeomorphTwoSphere.prodCongr projectiveLineHomeomorphTwoSphere

section Audit

#print axioms onePointEquivProjectiveLine
#print axioms projectiveLineHomeomorphOnePoint
#print axioms complexProjectiveLineCompact
#print axioms complexProjectiveLineT2
#print axioms onePointComplexHomeomorphTwoSphere
#print axioms projectiveLineHomeomorphTwoSphere
#print axioms surfaceHomeomorphSphereProduct

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineTopology
