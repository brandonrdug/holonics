import ElementaryHolonics.Millennium.HodgeRefinedTriangleClosedStar

/-!
# Exact tetrahedral boundary coordinates for the radial sphere

The four centered tetrahedral coordinates of a sphere point sum to zero and are not all zero.
Their minimum is therefore strictly negative.  Subtracting that minimum and dividing by its exact
total defect produces four nonnegative barycentric coordinates with sum one and at least one zero
coordinate.  Thus every sphere point has an exact address on the boundary of the standard
tetrahedron.

The decisive carrier law is that the open star of a tetrahedral vertex is precisely the locus
where the corresponding boundary coordinate is positive.  Common-star geometry is consequently
an affine positivity condition with a retained zero-coordinate seam, rather than an appeal to a
generic contractibility theorem.

Truth status: introduced coordinate carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact radial sphere and tetrahedral-star cover.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralBoundaryCoordinates

open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover

/-- [definition] The exact minimum of the four centered tetrahedral coordinates.  The nested
spelling exposes a continuous formula and avoids a choice-defined finite minimizer. -/
def sphereTetraMinimum (point : TwoSphere) : ℝ :=
  min (sphereTetraCoordinate 0 point)
    (min (sphereTetraCoordinate 1 point)
      (min (sphereTetraCoordinate 2 point) (sphereTetraCoordinate 3 point)))

/-- [proved-derived; formal-checked] The explicit minimum lies below every coordinate. -/
theorem sphereTetraMinimum_le_coordinate (point : TwoSphere) (vertex : TetraVertex) :
    sphereTetraMinimum point ≤ sphereTetraCoordinate vertex point := by
  fin_cases vertex <;> simp [sphereTetraMinimum]

/-- [proved-derived; formal-checked] One of the four addressed coordinates attains the explicit
minimum. -/
theorem exists_coordinate_eq_sphereTetraMinimum (point : TwoSphere) :
    ∃ vertex : TetraVertex,
      sphereTetraCoordinate vertex point = sphereTetraMinimum point := by
  rcases min_choice (sphereTetraCoordinate 0 point)
      (min (sphereTetraCoordinate 1 point)
        (min (sphereTetraCoordinate 2 point) (sphereTetraCoordinate 3 point))) with
    outer | outer
  · exact ⟨0, outer.symm⟩
  · rcases min_choice (sphereTetraCoordinate 1 point)
      (min (sphereTetraCoordinate 2 point) (sphereTetraCoordinate 3 point)) with
      middle | middle
    · exact ⟨1, by rw [sphereTetraMinimum, outer, middle]⟩
    · rcases min_choice (sphereTetraCoordinate 2 point)
        (sphereTetraCoordinate 3 point) with inner | inner
      · exact ⟨2, by rw [sphereTetraMinimum, outer, middle, inner]⟩
      · exact ⟨3, by rw [sphereTetraMinimum, outer, middle, inner]⟩

/-- [proved-derived; formal-checked] The minimum is strictly negative.  This is the exact
non-nullity which makes the boundary rebase invertible. -/
theorem sphereTetraMinimum_neg (point : TwoSphere) : sphereTetraMinimum point < 0 := by
  by_contra notNegative
  have minimumNonnegative : 0 ≤ sphereTetraMinimum point := le_of_not_gt notNegative
  have coordinateNonnegative (vertex : TetraVertex) :
      0 ≤ sphereTetraCoordinate vertex point :=
    minimumNonnegative.trans (sphereTetraMinimum_le_coordinate point vertex)
  have coordinateSum := sphereTetraCoordinate_sum_zero point
  rw [Fin.sum_univ_four] at coordinateSum
  have coordinateZeroZero : sphereTetraCoordinate 0 point = 0 := by
    linarith [coordinateNonnegative 0, coordinateNonnegative 1,
      coordinateNonnegative 2, coordinateNonnegative 3]
  have coordinateZeroOne : sphereTetraCoordinate 1 point = 0 := by
    linarith [coordinateNonnegative 0, coordinateNonnegative 1,
      coordinateNonnegative 2, coordinateNonnegative 3]
  have coordinateZeroTwo : sphereTetraCoordinate 2 point = 0 := by
    linarith [coordinateNonnegative 0, coordinateNonnegative 1,
      coordinateNonnegative 2, coordinateNonnegative 3]
  have coordinateZeroThree : sphereTetraCoordinate 3 point = 0 := by
    linarith [coordinateNonnegative 0, coordinateNonnegative 1,
      coordinateNonnegative 2, coordinateNonnegative 3]
  have coordinateZero (vertex : TetraVertex) :
      sphereTetraCoordinate vertex point = 0 := by
    fin_cases vertex
    · exact coordinateZeroZero
    · exact coordinateZeroOne
    · exact coordinateZeroTwo
    · exact coordinateZeroThree
  apply not_all_sphereTetraCoordinate_equal point
  intro vertex
  rw [coordinateZero vertex, coordinateZero 0]

/-- [proved-derived; formal-checked] The minimum varies continuously with the received sphere
point. -/
theorem continuous_sphereTetraMinimum : Continuous sphereTetraMinimum := by
  exact (continuous_sphereTetraCoordinate 0).min
    ((continuous_sphereTetraCoordinate 1).min
      ((continuous_sphereTetraCoordinate 2).min
        (continuous_sphereTetraCoordinate 3)))

/-- [definition] The positive exact denominator of the boundary-coordinate rebase. -/
def sphereTetraDefect (point : TwoSphere) : ℝ := -4 * sphereTetraMinimum point

/-- [proved-derived; formal-checked] The total tetrahedral defect is positive. -/
theorem sphereTetraDefect_pos (point : TwoSphere) : 0 < sphereTetraDefect point := by
  rw [sphereTetraDefect]
  linarith [sphereTetraMinimum_neg point]

/-- [definition] One barycentric boundary coordinate obtained by subtracting the minimum and
rebasing by the complete four-coordinate defect. -/
def sphereBoundaryCoordinateValue (point : TwoSphere) (vertex : TetraVertex) : ℝ :=
  (sphereTetraCoordinate vertex point - sphereTetraMinimum point) /
    sphereTetraDefect point

/-- [proved-derived; formal-checked] Every boundary coordinate is nonnegative. -/
theorem sphereBoundaryCoordinateValue_nonnegative (point : TwoSphere)
    (vertex : TetraVertex) : 0 ≤ sphereBoundaryCoordinateValue point vertex := by
  exact div_nonneg
    (sub_nonneg.mpr (sphereTetraMinimum_le_coordinate point vertex))
    (le_of_lt (sphereTetraDefect_pos point))

/-- [proved-derived; formal-checked] The four rebased coordinates sum exactly to one. -/
theorem sphereBoundaryCoordinateValue_sum (point : TwoSphere) :
    ∑ vertex : TetraVertex, sphereBoundaryCoordinateValue point vertex = 1 := by
  have coordinateSum := sphereTetraCoordinate_sum_zero point
  rw [Fin.sum_univ_four] at coordinateSum
  have defectNonzero : sphereTetraDefect point ≠ 0 :=
    ne_of_gt (sphereTetraDefect_pos point)
  rw [Fin.sum_univ_four]
  simp only [sphereBoundaryCoordinateValue]
  rw [← add_div, ← add_div, ← add_div]
  rw [div_eq_iff defectNonzero]
  rw [sphereTetraDefect]
  linarith

/-- [definition] The exact boundary address of a sphere point in the standard tetrahedron. -/
def sphereBoundaryCoordinate (point : TwoSphere) : Tetrahedron :=
  ⟨sphereBoundaryCoordinateValue point,
    sphereBoundaryCoordinateValue_nonnegative point,
    sphereBoundaryCoordinateValue_sum point⟩

@[simp]
theorem sphereBoundaryCoordinate_apply (point : TwoSphere) (vertex : TetraVertex) :
    sphereBoundaryCoordinate point vertex = sphereBoundaryCoordinateValue point vertex := rfl

/-- [proved-derived; formal-checked] Every sphere address lies on the tetrahedron boundary: an
actual minimizing coordinate is retained as a zero barycentric coordinate. -/
theorem sphereBoundaryCoordinate_has_zero (point : TwoSphere) :
    ∃ vertex : TetraVertex, sphereBoundaryCoordinate point vertex = 0 := by
  obtain ⟨vertex, minimumLaw⟩ := exists_coordinate_eq_sphereTetraMinimum point
  refine ⟨vertex, ?_⟩
  rw [sphereBoundaryCoordinate_apply, sphereBoundaryCoordinateValue, minimumLaw, sub_self,
    zero_div]

/-- [proved-derived; formal-checked] One boundary coordinate is positive exactly when its centered
tetrahedral coordinate lies strictly above the global minimum. -/
theorem sphereBoundaryCoordinate_pos_iff (point : TwoSphere) (vertex : TetraVertex) :
    0 < sphereBoundaryCoordinate point vertex ↔
      sphereTetraMinimum point < sphereTetraCoordinate vertex point := by
  rw [sphereBoundaryCoordinate_apply, sphereBoundaryCoordinateValue]
  exact (div_pos_iff_of_pos_right (sphereTetraDefect_pos point)).trans sub_pos

/-- [proved-derived; formal-checked] The open radial vertex star is precisely positivity of the
matching tetrahedral boundary coordinate. -/
theorem mem_vertexStar_iff_boundaryCoordinate_pos (point : TwoSphere)
    (vertex : TetraVertex) :
    point ∈ vertexStar vertex ↔ 0 < sphereBoundaryCoordinate point vertex := by
  rw [sphereBoundaryCoordinate_pos_iff]
  constructor
  · rintro ⟨lower, lowerLaw⟩
    exact (sphereTetraMinimum_le_coordinate point lower).trans_lt lowerLaw
  · intro aboveMinimum
    obtain ⟨lower, lowerLaw⟩ := exists_coordinate_eq_sphereTetraMinimum point
    exact ⟨lower, by rwa [lowerLaw]⟩

/-- [proved-derived; formal-checked] The complete sphere-to-boundary address is continuous. -/
theorem continuous_sphereBoundaryCoordinate : Continuous sphereBoundaryCoordinate := by
  apply Continuous.subtype_mk
  exact continuous_pi fun vertex =>
    ((continuous_sphereTetraCoordinate vertex).sub continuous_sphereTetraMinimum).div
      (continuous_const.mul continuous_sphereTetraMinimum)
      (fun point => by
        change sphereTetraDefect point ≠ 0
        exact ne_of_gt (sphereTetraDefect_pos point))

section Audit

#print axioms sphereTetraMinimum_neg
#print axioms sphereBoundaryCoordinateValue_sum
#print axioms sphereBoundaryCoordinate_has_zero
#print axioms mem_vertexStar_iff_boundaryCoordinate_pos
#print axioms continuous_sphereBoundaryCoordinate

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralBoundaryCoordinates
