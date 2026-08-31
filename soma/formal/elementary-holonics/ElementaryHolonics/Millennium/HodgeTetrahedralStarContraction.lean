import ElementaryHolonics.Millennium.HodgeTetrahedralBoundaryRadial
import Mathlib.Topology.Homotopy.Affine

/-!
# Exact contraction of a three-label common star

Three tetrahedral labels can never exhaust the four boundary coordinates.  Their equal-weight
barycentre is supported only on those labels.  If a boundary point belongs to all three labelled
stars, every zero coordinate of that point is absent from the label word.  The affine segment from
the point to the label barycentre therefore retains that same zero coordinate at every time.

This constructs the common-star contraction required in degree two.  Applying the two-sided radial
reconstruction returns the contraction to the original sphere and preserves all three named open
stars throughout.

Truth status: introduced contraction carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact tetrahedral boundary reconstruction.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralStarContraction

open Set Topology
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralBoundaryCoordinates
open Soma.Holonics.Millennium.HodgeTetrahedralBoundaryRadial

/-- [definition] The equal-weight tetrahedral barycentre of an addressed three-label word.
Repeated labels retain their multiplicity. -/
def triangleLabelBarycenter (labels : Fin 3 → TetraVertex) : Tetrahedron :=
  ⟨fun vertex =>
      (∑ index : Fin 3, if labels index = vertex then (1 : ℝ) else 0) / 3,
    by
      intro vertex
      positivity,
    by
      rw [← Finset.sum_div]
      rw [Finset.sum_comm]
      simp⟩

@[simp]
theorem triangleLabelBarycenter_apply (labels : Fin 3 → TetraVertex)
    (vertex : TetraVertex) :
    triangleLabelBarycenter labels vertex =
      (∑ index : Fin 3, if labels index = vertex then (1 : ℝ) else 0) / 3 := rfl

/-- [proved-derived; formal-checked] Every label occurring in the word has positive barycentric
weight, including when labels repeat. -/
theorem triangleLabelBarycenter_label_pos (labels : Fin 3 → TetraVertex)
    (index : Fin 3) :
    0 < triangleLabelBarycenter labels (labels index) := by
  rw [triangleLabelBarycenter_apply]
  have termBound : (1 : ℝ) ≤
      ∑ candidate : Fin 3,
        if labels candidate = labels index then (1 : ℝ) else 0 := by
    have singleBound := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : Fin 3 =>
        if labels candidate = labels index then (1 : ℝ) else 0)
      (fun candidate _ => by
        by_cases same : labels candidate = labels index <;> simp [same])
      (Finset.mem_univ index)
    simpa using singleBound
  exact div_pos (lt_of_lt_of_le zero_lt_one termBound) (by norm_num)

/-- [proved-derived; formal-checked] A vertex absent from the three-label word has zero target
coordinate. -/
theorem triangleLabelBarycenter_eq_zero_of_absent
    (labels : Fin 3 → TetraVertex) (vertex : TetraVertex)
    (absent : ∀ index : Fin 3, vertex ≠ labels index) :
    triangleLabelBarycenter labels vertex = 0 := by
  rw [triangleLabelBarycenter_apply, Fin.sum_univ_three]
  simp [Ne.symm (absent 0), Ne.symm (absent 1), Ne.symm (absent 2)]

/-- [definition] Boundary points simultaneously occupying the three named open stars. -/
abbrev TriangleCommonStarBoundary (labels : Fin 3 → TetraVertex) :=
  {point : TetraBoundary // ∀ index : Fin 3, 0 < point.1.1 (labels index)}

/-- [definition] The affine segment from one common-star boundary point to the three-label
barycentre, regarded first as a point of the full tetrahedron. -/
def triangleStarLinePoint (labels : Fin 3 → TetraVertex) (time : unitInterval)
    (point : TriangleCommonStarBoundary labels) : Tetrahedron :=
  ⟨AffineMap.lineMap point.1.1.1 (triangleLabelBarycenter labels).1 time.1,
    (convex_stdSimplex ℝ (Fin 4)).lineMap_mem point.1.1.2
      (triangleLabelBarycenter labels).2 time.2⟩

@[simp]
theorem triangleStarLinePoint_apply (labels : Fin 3 → TetraVertex)
    (time : unitInterval) (point : TriangleCommonStarBoundary labels)
    (vertex : TetraVertex) :
    triangleStarLinePoint labels time point vertex =
      (1 - time.1) * point.1.1 vertex +
        time.1 * triangleLabelBarycenter labels vertex := by
  rw [triangleStarLinePoint]
  exact congrFun (AffineMap.lineMap_apply_module _ _ _)
    vertex

/-- [proved-derived; formal-checked] A zero coordinate of the source common-star point is absent
from all three labels. -/
theorem commonStar_zero_absent (labels : Fin 3 → TetraVertex)
    (point : TriangleCommonStarBoundary labels) (vertex : TetraVertex)
    (zeroLaw : point.1.1 vertex = 0) :
    ∀ index : Fin 3, vertex ≠ labels index := by
  intro index equalLabel
  subst vertex
  exact (ne_of_gt (point.2 index)) zeroLaw

/-- [proved-derived; formal-checked] The affine segment retains an actual zero coordinate, hence
never leaves the tetrahedron boundary. -/
theorem triangleStarLinePoint_has_zero (labels : Fin 3 → TetraVertex)
    (time : unitInterval) (point : TriangleCommonStarBoundary labels) :
    ∃ vertex : TetraVertex, triangleStarLinePoint labels time point vertex = 0 := by
  obtain ⟨vertex, zeroLaw⟩ := point.1.2
  refine ⟨vertex, ?_⟩
  rw [triangleStarLinePoint_apply, zeroLaw,
    triangleLabelBarycenter_eq_zero_of_absent labels vertex
      (commonStar_zero_absent labels point vertex zeroLaw)]
  ring

/-- [definition] The exact affine contraction as an addressed tetrahedral boundary point. -/
def triangleStarBoundaryContractionPoint (labels : Fin 3 → TetraVertex)
    (time : unitInterval) (point : TriangleCommonStarBoundary labels) : TetraBoundary :=
  ⟨triangleStarLinePoint labels time point,
    triangleStarLinePoint_has_zero labels time point⟩

/-- [definition] The complete continuous common-star contraction on the tetrahedral boundary. -/
def triangleStarBoundaryContraction (labels : Fin 3 → TetraVertex) :
    C(unitInterval × TriangleCommonStarBoundary labels, TetraBoundary) where
  toFun pair := triangleStarBoundaryContractionPoint labels pair.1 pair.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_pi fun vertex => by
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have timeContinuous : Continuous
          (fun pair : unitInterval × TriangleCommonStarBoundary labels => pair.1.1) :=
        continuous_subtype_val.comp continuous_fst
      have pointContinuous : Continuous
          (fun pair : unitInterval × TriangleCommonStarBoundary labels =>
            pair.2.1.1.1 vertex) :=
        (continuous_apply vertex).comp
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp
              (continuous_subtype_val.comp continuous_snd)))
      exact ((continuous_const.sub timeContinuous).mul pointContinuous).add
        (timeContinuous.mul continuous_const)

/-- [proved-derived; formal-checked] At time zero the boundary contraction is the source point. -/
theorem triangleStarBoundaryContraction_zero (labels : Fin 3 → TetraVertex)
    (point : TriangleCommonStarBoundary labels) :
    triangleStarBoundaryContraction labels (0, point) = point.1 := by
  apply Subtype.ext
  change triangleStarLinePoint labels 0 point = point.1.1
  apply stdSimplex.ext
  funext vertex
  rw [triangleStarLinePoint_apply]
  norm_num

/-- [proved-derived; formal-checked] At time one the contraction reaches the three-label
barycentre. -/
theorem triangleStarBoundaryContraction_one (labels : Fin 3 → TetraVertex)
    (point : TriangleCommonStarBoundary labels) :
    (triangleStarBoundaryContraction labels (1, point)).1 =
      triangleLabelBarycenter labels := by
  change triangleStarLinePoint labels 1 point = triangleLabelBarycenter labels
  apply stdSimplex.ext
  funext vertex
  rw [triangleStarLinePoint_apply]
  norm_num

/-- [proved-derived; formal-checked] Every selected label remains strictly positive throughout the
boundary contraction. -/
theorem triangleStarBoundaryContraction_label_pos
    (labels : Fin 3 → TetraVertex) (time : unitInterval)
    (point : TriangleCommonStarBoundary labels) (index : Fin 3) :
    0 < (triangleStarBoundaryContraction labels (time, point)).1 (labels index) := by
  change 0 < triangleStarLinePoint labels time point (labels index)
  rw [triangleStarLinePoint_apply]
  have sourcePositive := point.2 index
  have targetPositive := triangleLabelBarycenter_label_pos labels index
  have timeNonnegative := time.2.1
  have timeAtMostOne := time.2.2
  by_cases timeOne : time.1 = 1
  · rw [timeOne]
    simpa only [sub_self, zero_mul, one_mul, zero_add] using targetPositive
  · have timeBelowOne : time.1 < 1 := lt_of_le_of_ne timeAtMostOne timeOne
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr timeBelowOne) sourcePositive)
      (mul_nonneg timeNonnegative (le_of_lt targetPositive))

/-- [definition] Return the affine common-star contraction through the exact radial receiver. -/
def triangleStarSphereContraction (labels : Fin 3 → TetraVertex) :
    C(unitInterval × TriangleCommonStarBoundary labels, TwoSphere) :=
  boundaryRadial.comp (triangleStarBoundaryContraction labels)

/-- [proved-derived; formal-checked] The returned contraction remains in every one of the three
named sphere stars at every time. -/
theorem triangleStarSphereContraction_mem_vertexStar
    (labels : Fin 3 → TetraVertex) (time : unitInterval)
    (point : TriangleCommonStarBoundary labels) (index : Fin 3) :
    triangleStarSphereContraction labels (time, point) ∈ vertexStar (labels index) := by
  rw [triangleStarSphereContraction, ContinuousMap.comp_apply,
    boundaryRadial_mem_vertexStar_iff]
  exact triangleStarBoundaryContraction_label_pos labels time point index

/-- [proved-derived; formal-checked] At time zero the returned contraction is exactly the radial
image of the source boundary point. -/
theorem triangleStarSphereContraction_zero (labels : Fin 3 → TetraVertex)
    (point : TriangleCommonStarBoundary labels) :
    triangleStarSphereContraction labels (0, point) = boundaryRadial point.1 := by
  rw [triangleStarSphereContraction, ContinuousMap.comp_apply,
    triangleStarBoundaryContraction_zero]

section Audit

#print axioms triangleLabelBarycenter_label_pos
#print axioms triangleStarLinePoint_has_zero
#print axioms triangleStarBoundaryContraction
#print axioms triangleStarBoundaryContraction_label_pos
#print axioms triangleStarSphereContraction_mem_vertexStar

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralStarContraction
