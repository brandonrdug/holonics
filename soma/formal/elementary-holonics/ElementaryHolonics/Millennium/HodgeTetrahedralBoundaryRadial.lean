import ElementaryHolonics.Millennium.HodgeTetrahedralBoundaryCoordinates

/-!
# Radial reconstruction of the tetrahedral boundary

The boundary-coordinate chart is not merely a detector.  A boundary point retains a zero
coordinate, so its centered first three coordinates cannot all vanish.  Normalizing that exact
centered vector returns a sphere point.  The composite from the sphere to its tetrahedral boundary
address and back is the identity.

This is the reconstruction half of the common-star carrier: affine fillings may be constructed on
the tetrahedron boundary and returned to the original radial receiver without losing the sphere
point.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact boundary-coordinate construction.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralBoundaryRadial

open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralBoundaryCoordinates

/-- [definition] The geometric boundary of the standard tetrahedron, retaining an addressed zero
coordinate rather than quotienting the four faces. -/
abbrev TetraBoundary :=
  {point : Tetrahedron // ∃ vertex : TetraVertex, point vertex = 0}

/-- [definition] The centered ambient vector of a tetrahedral boundary point. -/
def boundaryCenteredVector (point : TetraBoundary) : AmbientThree :=
  WithLp.toLp 2 fun coordinate : Fin 3 =>
    point.1 coordinate.castSucc - (1 / 4 : ℝ)

@[simp]
theorem boundaryCenteredVector_apply (point : TetraBoundary) (coordinate : Fin 3) :
    boundaryCenteredVector point coordinate =
      point.1 coordinate.castSucc - (1 / 4 : ℝ) := rfl

/-- [proved-derived; formal-checked] A tetrahedral boundary point cannot be the barycentre, so its
centered ambient vector is nonzero. -/
theorem boundaryCenteredVector_ne_zero (point : TetraBoundary) :
    boundaryCenteredVector point ≠ 0 := by
  intro centeredZero
  have coordinateQuarter (coordinate : Fin 3) :
      point.1 coordinate.castSucc = (1 / 4 : ℝ) := by
    have coordinateZero := congrFun
      (congrArg WithLp.ofLp centeredZero) coordinate
    exact sub_eq_zero.mp (by simpa [boundaryCenteredVector] using coordinateZero)
  have coordinateThree : point.1 (3 : Fin 4) = (1 / 4 : ℝ) := by
    have coordinateSum := stdSimplex.sum_eq_one point.1
    rw [Fin.sum_univ_four] at coordinateSum
    have zeroLaw : point.1 (0 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using coordinateQuarter 0
    have oneLaw : point.1 (1 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using coordinateQuarter 1
    have twoLaw : point.1 (2 : Fin 4) = (1 / 4 : ℝ) := by
      simpa using coordinateQuarter 2
    linarith
  have everyCoordinateQuarter (vertex : TetraVertex) :
      point.1 vertex = (1 / 4 : ℝ) := by
    fin_cases vertex
    · simpa using coordinateQuarter 0
    · simpa using coordinateQuarter 1
    · simpa using coordinateQuarter 2
    · exact coordinateThree
  obtain ⟨zeroVertex, zeroLaw⟩ := point.2
  rw [everyCoordinateQuarter zeroVertex] at zeroLaw
  norm_num at zeroLaw

/-- [proved-derived; formal-checked] The centered boundary vector varies continuously. -/
theorem continuous_boundaryCenteredVector : Continuous boundaryCenteredVector := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun coordinate =>
    ((continuous_apply coordinate.castSucc).comp
      (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const)

/-- [definition] Radial return from the addressed tetrahedral boundary to the sphere. -/
def boundaryRadial : C(TetraBoundary, TwoSphere) where
  toFun point :=
    ⟨NormedSpace.normalize (boundaryCenteredVector point),
      mem_sphere_zero_iff_norm.2
        (NormedSpace.norm_normalize (boundaryCenteredVector_ne_zero point))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [show (fun point : TetraBoundary =>
        NormedSpace.normalize (boundaryCenteredVector point)) =
      fun point => ‖boundaryCenteredVector point‖⁻¹ • boundaryCenteredVector point by rfl]
    exact continuous_boundaryCenteredVector.norm.inv₀
      (fun point normZero =>
        boundaryCenteredVector_ne_zero point (norm_eq_zero.mp normZero)) |>.smul
      continuous_boundaryCenteredVector

/-- [definition] The continuous exact sphere address in the tetrahedral boundary. -/
def sphereBoundaryMap : C(TwoSphere, TetraBoundary) where
  toFun point := ⟨sphereBoundaryCoordinate point, sphereBoundaryCoordinate_has_zero point⟩
  continuous_toFun := Continuous.subtype_mk continuous_sphereBoundaryCoordinate _

/-- [proved-derived; formal-checked] Subtracting the tetrahedral barycentre from one boundary
coordinate returns the corresponding centered coordinate divided by the positive total defect. -/
theorem sphereBoundaryCoordinate_sub_quarter (point : TwoSphere)
    (vertex : TetraVertex) :
    sphereBoundaryCoordinate point vertex - (1 / 4 : ℝ) =
      sphereTetraCoordinate vertex point / sphereTetraDefect point := by
  rw [sphereBoundaryCoordinate_apply, sphereBoundaryCoordinateValue]
  have defectNonzero : sphereTetraDefect point ≠ 0 :=
    ne_of_gt (sphereTetraDefect_pos point)
  field_simp [defectNonzero]
  rw [sphereTetraDefect]
  ring

/-- [proved-derived; formal-checked] Centering the boundary address produces one positive scalar
multiple of the original ambient direction. -/
theorem boundaryCenteredVector_sphereBoundaryMap (point : TwoSphere) :
    boundaryCenteredVector (sphereBoundaryMap point) =
      (sphereTetraDefect point)⁻¹ • point.1 := by
  apply PiLp.ext
  intro coordinate
  rw [boundaryCenteredVector_apply]
  change sphereBoundaryCoordinate point coordinate.castSucc - (1 / 4 : ℝ) = _
  rw [sphereBoundaryCoordinate_sub_quarter]
  fin_cases coordinate <;>
    simp [sphereTetraCoordinate, div_eq_inv_mul]

/-- [proved-derived; formal-checked] The radial return exactly reconstructs every sphere point
from its tetrahedral boundary address. -/
theorem boundaryRadial_sphereBoundaryMap (point : TwoSphere) :
    boundaryRadial (sphereBoundaryMap point) = point := by
  apply Subtype.ext
  change NormedSpace.normalize
      (boundaryCenteredVector (sphereBoundaryMap point)) = point.1
  rw [boundaryCenteredVector_sphereBoundaryMap]
  rw [NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (sphereTetraDefect_pos point))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp point.2)

/-- [proved-derived; formal-checked] Radial return scales every centered tetrahedral coordinate by
the same positive normalization factor. -/
theorem sphereTetraCoordinate_boundaryRadial (point : TetraBoundary)
    (vertex : TetraVertex) :
    sphereTetraCoordinate vertex (boundaryRadial point) =
      ‖boundaryCenteredVector point‖⁻¹ *
        (point.1 vertex - (1 / 4 : ℝ)) := by
  have coordinateSum := stdSimplex.sum_eq_one point.1
  rw [Fin.sum_univ_four] at coordinateSum
  fin_cases vertex
  · simp [sphereTetraCoordinate, boundaryRadial, NormedSpace.normalize,
      boundaryCenteredVector]
  · simp [sphereTetraCoordinate, boundaryRadial, NormedSpace.normalize,
      boundaryCenteredVector]
  · simp [sphereTetraCoordinate, boundaryRadial, NormedSpace.normalize,
      boundaryCenteredVector]
  · change -(
        (‖boundaryCenteredVector point‖⁻¹ • boundaryCenteredVector point) (0 : Fin 3) +
        (‖boundaryCenteredVector point‖⁻¹ • boundaryCenteredVector point) (1 : Fin 3) +
        (‖boundaryCenteredVector point‖⁻¹ • boundaryCenteredVector point) (2 : Fin 3)) =
      ‖boundaryCenteredVector point‖⁻¹ * (point.1 (3 : Fin 4) - (1 / 4 : ℝ))
    simp only [PiLp.smul_apply, smul_eq_mul, boundaryCenteredVector_apply]
    have coordinateSumCast :
        point.1 (0 : Fin 3).castSucc + point.1 (1 : Fin 3).castSucc +
            point.1 (2 : Fin 3).castSucc + point.1 (3 : Fin 4) = 1 := by
      simpa using coordinateSum
    have scaledSum := congrArg
      (fun value : ℝ => ‖boundaryCenteredVector point‖⁻¹ * value)
      coordinateSumCast
    ring_nf at scaledSum ⊢
    linarith

/-- [proved-derived; formal-checked] The minimum centered coordinate of a returned boundary point
is exactly the common normalization factor times `-1/4`; the retained zero coordinate attains it. -/
theorem sphereTetraMinimum_boundaryRadial (point : TetraBoundary) :
    sphereTetraMinimum (boundaryRadial point) =
      ‖boundaryCenteredVector point‖⁻¹ * (-(1 / 4 : ℝ)) := by
  let scale : ℝ := ‖boundaryCenteredVector point‖⁻¹
  have scalePositive : 0 < scale := by
    exact inv_pos.mpr (norm_pos_iff.mpr (boundaryCenteredVector_ne_zero point))
  have lower (vertex : TetraVertex) :
      scale * (-(1 / 4 : ℝ)) ≤
        sphereTetraCoordinate vertex (boundaryRadial point) := by
    rw [sphereTetraCoordinate_boundaryRadial]
    exact mul_le_mul_of_nonneg_left
      (by have := stdSimplex.zero_le point.1 vertex; linarith) (le_of_lt scalePositive)
  obtain ⟨zeroVertex, zeroLaw⟩ := point.2
  apply le_antisymm
  · calc
      sphereTetraMinimum (boundaryRadial point) ≤
          sphereTetraCoordinate zeroVertex (boundaryRadial point) :=
        sphereTetraMinimum_le_coordinate _ _
      _ = scale * (-(1 / 4 : ℝ)) := by
        rw [sphereTetraCoordinate_boundaryRadial, zeroLaw]
        simp [scale]
  · rw [sphereTetraMinimum]
    exact le_min (lower 0) (le_min (lower 1) (le_min (lower 2) (lower 3)))

/-- [proved-derived; formal-checked] The defect of a radial boundary point is exactly its positive
normalization factor. -/
theorem sphereTetraDefect_boundaryRadial (point : TetraBoundary) :
    sphereTetraDefect (boundaryRadial point) = ‖boundaryCenteredVector point‖⁻¹ := by
  rw [sphereTetraDefect, sphereTetraMinimum_boundaryRadial]
  ring

/-- [proved-derived; formal-checked] The sphere address also reconstructs every addressed
tetrahedral boundary point after radial return. -/
theorem sphereBoundaryMap_boundaryRadial (point : TetraBoundary) :
    sphereBoundaryMap (boundaryRadial point) = point := by
  apply Subtype.ext
  apply stdSimplex.ext
  funext vertex
  change sphereBoundaryCoordinate (boundaryRadial point) vertex = point.1 vertex
  rw [sphereBoundaryCoordinate_apply, sphereBoundaryCoordinateValue,
    sphereTetraCoordinate_boundaryRadial, sphereTetraMinimum_boundaryRadial,
    sphereTetraDefect_boundaryRadial]
  have scaleNonzero : ‖boundaryCenteredVector point‖⁻¹ ≠ 0 :=
    ne_of_gt (inv_pos.mpr
      (norm_pos_iff.mpr (boundaryCenteredVector_ne_zero point)))
  rw [div_eq_iff scaleNonzero]
  ring

/-- [proved-derived; formal-checked] Star membership of a radial boundary point is exactly
positivity of its retained barycentric coordinate. -/
theorem boundaryRadial_mem_vertexStar_iff (point : TetraBoundary)
    (vertex : TetraVertex) :
    boundaryRadial point ∈ vertexStar vertex ↔ 0 < point.1 vertex := by
  rw [mem_vertexStar_iff_boundaryCoordinate_pos]
  have coordinateLaw :
      sphereBoundaryCoordinate (boundaryRadial point) vertex = point.1 vertex := by
    exact congrArg (fun addressed : TetraBoundary => addressed.1 vertex)
      (sphereBoundaryMap_boundaryRadial point)
  rw [coordinateLaw]

/-- [proved-derived; formal-checked] The radial two-sphere and the addressed boundary of the
standard tetrahedron are exactly homeomorphic through the retained minimum-coordinate chart. -/
def sphereHomeomorphTetraBoundary : TwoSphere ≃ₜ TetraBoundary where
  toEquiv :=
    { toFun := sphereBoundaryMap
      invFun := boundaryRadial
      left_inv := boundaryRadial_sphereBoundaryMap
      right_inv := sphereBoundaryMap_boundaryRadial }
  continuous_toFun := sphereBoundaryMap.continuous
  continuous_invFun := boundaryRadial.continuous

section Audit

#print axioms boundaryCenteredVector_ne_zero
#print axioms boundaryRadial
#print axioms sphereBoundaryMap
#print axioms boundaryCenteredVector_sphereBoundaryMap
#print axioms boundaryRadial_sphereBoundaryMap
#print axioms sphereTetraCoordinate_boundaryRadial
#print axioms sphereTetraMinimum_boundaryRadial
#print axioms sphereTetraDefect_boundaryRadial
#print axioms sphereBoundaryMap_boundaryRadial
#print axioms boundaryRadial_mem_vertexStar_iff
#print axioms sphereHomeomorphTetraBoundary

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralBoundaryRadial
