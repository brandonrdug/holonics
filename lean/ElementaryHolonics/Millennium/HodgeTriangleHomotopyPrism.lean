import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Millennium.HodgeRefinedTriangleAffineCarrier

/-!
# The retained degree-two singular prism

A homotopy of addressed singular triangles is not yet a chain equality.  The product
`I × Δ²` is triangulated here into its three ordered tetrahedra.  Internal faces cancel only
after their source maps are proved equal; the six side faces remain explicit.  Thus no reversed
parametrization or degenerate occurrence is silently quotiented away.

Truth status: introduced source maps and chains are `[definition]`; every theorem is
`[proved-derived; formal-checked]`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set Topology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology
open Soma.Holonics.Millennium.HodgeRadialCurrent
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier.CommonStarTriangle
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier
open Soma.Holonics.Millennium.HodgeRefinedTriangleAffineCarrier
open Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeRefinedCycleCarrier

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [definition] The one-simplex used as the retained time carrier.  This local name avoids
the unrelated categorical `Segment` whose topology is not the simplex topology. -/
abbrev PrismSegment := stdSimplex ℝ (Fin 2)

/-- [definition] Lower/upper time labels on the three tetrahedra of `I × Δ²`. -/
def prismTimeLabels : Fin 3 → Fin 4 → Fin 2 :=
  ![![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]]

/-- [definition] Triangle-vertex labels on the three tetrahedra of `I × Δ²`. -/
def prismTriangleLabels : Fin 3 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 1, 1, 2], ![0, 1, 2, 2]]

/-- [definition] The time-simplex coordinate of one prism tetrahedron. -/
def prismSegmentMap (cut : Fin 3) : C(Tetrahedron, PrismSegment) where
  toFun := stdSimplex.map (prismTimeLabels cut)
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] The triangle coordinate of one prism tetrahedron. -/
def prismTriangleMap (cut : Fin 3) : C(Tetrahedron, Triangle) where
  toFun := stdSimplex.map (prismTriangleLabels cut)
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] Read the upper barycentric coordinate of a segment as an exact unit-interval
coordinate. -/
def segmentTime : C(PrismSegment, unitInterval) where
  toFun point := ⟨point 1, stdSimplex.zero_le point 1, stdSimplex.le_one point 1⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val) _

/-- [definition] One of the three exact tetrahedral charts of the triangle cylinder. -/
def prismCylinderMap (cut : Fin 3) : C(Tetrahedron, unitInterval × Triangle) where
  toFun point := (segmentTime (prismSegmentMap cut point), prismTriangleMap cut point)
  continuous_toFun :=
    ((segmentTime.continuous.comp (prismSegmentMap cut).continuous).prodMk
      (prismTriangleMap cut).continuous)

/-- [definition] The constant-time inclusion of the source triangle into its cylinder. -/
def triangleCylinderEnd (time : unitInterval) : C(Triangle, unitInterval × Triangle) where
  toFun point := (time, point)
  continuous_toFun := continuous_const.prodMk continuous_id

/-- [proved-derived; formal-checked] Restricting a prism segment chart to a face composes its
ordered label word with the exact face injection. -/
theorem prismSegmentMap_face (cut : Fin 3) (face : Fin 4) :
    (prismSegmentMap cut).comp (simplexFaceMap (degree := 2) face) =
      ({ toFun := stdSimplex.map (prismTimeLabels cut ∘ face.succAbove)
         continuous_toFun := stdSimplex.continuous_map _ } : C(Triangle, PrismSegment)) := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (prismTimeLabels cut)
      (stdSimplex.map face.succAbove point) =
    stdSimplex.map (prismTimeLabels cut ∘ face.succAbove) point
  rw [stdSimplex.map_comp_apply]

/-- [proved-derived; formal-checked] The triangle coordinate carries the identical face law. -/
theorem prismTriangleMap_face (cut : Fin 3) (face : Fin 4) :
    (prismTriangleMap cut).comp (simplexFaceMap (degree := 2) face) =
      ({ toFun := stdSimplex.map (prismTriangleLabels cut ∘ face.succAbove)
         continuous_toFun := stdSimplex.continuous_map _ } : C(Triangle, Triangle)) := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (prismTriangleLabels cut)
      (stdSimplex.map face.succAbove point) =
    stdSimplex.map (prismTriangleLabels cut ∘ face.succAbove) point
  rw [stdSimplex.map_comp_apply]

/-- [proved-derived; formal-checked] The first internal face is one addressed cylinder triangle,
not two merely endpoint-equal shadows. -/
theorem prismCylinderMap_internal_first :
    (prismCylinderMap 0).comp (simplexFaceMap (degree := 2) 1) =
      (prismCylinderMap 1).comp (simplexFaceMap (degree := 2) 1) := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((prismSegmentMap 0).comp
        (simplexFaceMap (degree := 2) 1)) point) =
      segmentTime (((prismSegmentMap 1).comp
        (simplexFaceMap (degree := 2) 1)) point)
    rw [prismSegmentMap_face 0 1, prismSegmentMap_face 1 1]
    have hlabels : prismTimeLabels 0 ∘ Fin.succAbove 1 =
        prismTimeLabels 1 ∘ Fin.succAbove 1 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
  · change ((prismTriangleMap 0).comp
        (simplexFaceMap (degree := 2) 1)) point =
      ((prismTriangleMap 1).comp
        (simplexFaceMap (degree := 2) 1)) point
    rw [prismTriangleMap_face 0 1, prismTriangleMap_face 1 1]
    have hlabels : prismTriangleLabels 0 ∘ Fin.succAbove 1 =
        prismTriangleLabels 1 ∘ Fin.succAbove 1 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]

/-- [proved-derived; formal-checked] The second internal face is likewise one retained source
map. -/
theorem prismCylinderMap_internal_second :
    (prismCylinderMap 1).comp (simplexFaceMap (degree := 2) 2) =
      (prismCylinderMap 2).comp (simplexFaceMap (degree := 2) 2) := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((prismSegmentMap 1).comp
        (simplexFaceMap (degree := 2) 2)) point) =
      segmentTime (((prismSegmentMap 2).comp
        (simplexFaceMap (degree := 2) 2)) point)
    rw [prismSegmentMap_face 1 2, prismSegmentMap_face 2 2]
    have hlabels : prismTimeLabels 1 ∘ Fin.succAbove 2 =
        prismTimeLabels 2 ∘ Fin.succAbove 2 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
  · change ((prismTriangleMap 1).comp
        (simplexFaceMap (degree := 2) 2)) point =
      ((prismTriangleMap 2).comp
        (simplexFaceMap (degree := 2) 2)) point
    rw [prismTriangleMap_face 1 2, prismTriangleMap_face 2 2]
    have hlabels : prismTriangleLabels 1 ∘ Fin.succAbove 2 =
        prismTriangleLabels 2 ∘ Fin.succAbove 2 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]

/-- [proved-derived; formal-checked] The exposed face of the first prism tetrahedron is the exact
time-one triangle. -/
theorem prismCylinderMap_top :
    (prismCylinderMap 0).comp (simplexFaceMap (degree := 2) 0) =
      triangleCylinderEnd 1 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((prismSegmentMap 0).comp
        (simplexFaceMap (degree := 2) 0)) point) = 1
    rw [prismSegmentMap_face 0 0]
    apply Subtype.ext
    have hlabels : prismTimeLabels 0 ∘ Fin.succAbove 0 =
        fun _ => (1 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change (stdSimplex.map (fun _ : Fin 3 => (1 : Fin 2)) point) 1 = 1
    simp [FunOnFinite.linearMap_apply_apply, stdSimplex.sum_eq_one]
  · change ((prismTriangleMap 0).comp
        (simplexFaceMap (degree := 2) 0)) point = point
    rw [prismTriangleMap_face 0 0]
    have hlabels : prismTriangleLabels 0 ∘ Fin.succAbove 0 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change stdSimplex.map id point = point
    exact stdSimplex.map_id_apply point

/-- [proved-derived; formal-checked] The exposed face of the last prism tetrahedron is the exact
time-zero triangle. -/
theorem prismCylinderMap_bottom :
    (prismCylinderMap 2).comp (simplexFaceMap (degree := 2) 3) =
      triangleCylinderEnd 0 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((prismSegmentMap 2).comp
        (simplexFaceMap (degree := 2) 3)) point) = 0
    rw [prismSegmentMap_face 2 3]
    apply Subtype.ext
    have hlabels : prismTimeLabels 2 ∘ Fin.succAbove 3 =
        fun _ => (0 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change (stdSimplex.map (fun _ : Fin 3 => (0 : Fin 2)) point) 1 = 0
    simp [FunOnFinite.linearMap_apply_apply]
  · change ((prismTriangleMap 2).comp
        (simplexFaceMap (degree := 2) 3)) point = point
    rw [prismTriangleMap_face 2 3]
    have hlabels : prismTriangleLabels 2 ∘ Fin.succAbove 3 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change stdSimplex.map id point = point
    exact stdSimplex.map_id_apply point

/-- [definition] One singular tetrahedral occurrence obtained by transporting a cylinder chart
through the supplied homotopy. -/
def prismSimplex
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (cut : Fin 3) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm
      (homotopy.comp (prismCylinderMap cut))

/-- [definition] The triangle at a declared endpoint of the homotopy. -/
def homotopyEndSimplex
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (time : unitInterval) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      (homotopy.comp (triangleCylinderEnd time))

/-- [proved-derived; formal-checked] Restricting a transported prism simplex is literal source
composition; both boundary maps are retained. -/
theorem prismSimplex_face_eq
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (cut : Fin 3) (face : Fin 4) :
    TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2))
        (simplexFace face (prismSimplex homotopy cut)) =
      homotopy.comp ((prismCylinderMap cut).comp
        (simplexFaceMap (degree := 2) face)) := by
  rw [simplexFace_realization]
  simp only [prismSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  rfl

/-- [proved-derived; formal-checked] The first internal cylinder face remains one singular
triangle after transport through an arbitrary homotopy. -/
theorem prismSimplex_internal_first
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    simplexFace 1 (prismSimplex homotopy 0) =
      simplexFace 1 (prismSimplex homotopy 1) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [prismSimplex_face_eq, prismSimplex_face_eq,
    prismCylinderMap_internal_first]

/-- [proved-derived; formal-checked] The second internal cylinder face remains one singular
triangle after transport. -/
theorem prismSimplex_internal_second
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    simplexFace 2 (prismSimplex homotopy 1) =
      simplexFace 2 (prismSimplex homotopy 2) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [prismSimplex_face_eq, prismSimplex_face_eq,
    prismCylinderMap_internal_second]

/-- [proved-derived; formal-checked] The positive exposed face is exactly the declared upper
endpoint triangle. -/
theorem prismSimplex_top
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    simplexFace 0 (prismSimplex homotopy 0) = homotopyEndSimplex homotopy 1 := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [prismSimplex_face_eq]
  simp only [homotopyEndSimplex, Equiv.apply_symm_apply]
  rw [prismCylinderMap_top]

/-- [proved-derived; formal-checked] The negative exposed face is exactly the declared lower
endpoint triangle. -/
theorem prismSimplex_bottom
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    simplexFace 3 (prismSimplex homotopy 2) = homotopyEndSimplex homotopy 0 := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [prismSimplex_face_eq]
  simp only [homotopyEndSimplex, Equiv.apply_symm_apply]
  rw [prismCylinderMap_bottom]

/-- [definition] The three oriented tetrahedral occurrences in the degree-two homotopy prism. -/
def triangleHomotopyPrism
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) : SphereChain 3 :=
  simplexGenerator (prismSimplex homotopy 0) -
    simplexGenerator (prismSimplex homotopy 1) +
      simplexGenerator (prismSimplex homotopy 2)

/-- [definition] The two oriented side triangles over one source face of `Δ²`.  The three
cases retain the actual tetrahedron-face occurrences generated by the fixed triangulation of
`I × Δ²`; no endpoint-only quotient is taken. -/
def triangleFacePrism
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (face : Fin 3) : SphereChain 2 :=
  match face with
  | 0 =>
      simplexGenerator (simplexFace 0 (prismSimplex homotopy 1)) -
        simplexGenerator (simplexFace 0 (prismSimplex homotopy 2))
  | 1 =>
      simplexGenerator (simplexFace 2 (prismSimplex homotopy 0)) -
        simplexGenerator (simplexFace 1 (prismSimplex homotopy 2))
  | 2 =>
      simplexGenerator (simplexFace 3 (prismSimplex homotopy 0)) -
        simplexGenerator (simplexFace 3 (prismSimplex homotopy 1))

/-! ## Normalization of every lateral face through one addressed edge prism -/

/-- [definition] Lower/upper time labels on the two ordered triangles of `I × Δ¹`. -/
def edgePrismTimeLabels : Fin 2 → Fin 3 → Fin 2 :=
  ![![0, 1, 1], ![0, 0, 1]]

/-- [definition] Edge-vertex labels on the two ordered triangles of `I × Δ¹`. -/
def edgePrismSourceLabels : Fin 2 → Fin 3 → Fin 2 :=
  ![![0, 0, 1], ![0, 1, 1]]

/-- [definition] The time coordinate of one ordered edge-prism triangle. -/
def edgePrismSegmentMap (cut : Fin 2) : C(Triangle, PrismSegment) where
  toFun := stdSimplex.map (edgePrismTimeLabels cut)
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] The source-edge coordinate of one ordered edge-prism triangle. -/
def edgePrismSourceMap (cut : Fin 2) : C(Triangle, PrismSegment) where
  toFun := stdSimplex.map (edgePrismSourceLabels cut)
  continuous_toFun := stdSimplex.continuous_map _

/-- [definition] One of the two exact triangle charts of the edge cylinder. -/
def edgePrismCylinderMap (cut : Fin 2) :
    C(Triangle, unitInterval × PrismSegment) where
  toFun point :=
    (segmentTime (edgePrismSegmentMap cut point), edgePrismSourceMap cut point)
  continuous_toFun :=
    ((segmentTime.continuous.comp (edgePrismSegmentMap cut).continuous).prodMk
      (edgePrismSourceMap cut).continuous)

/-- [definition] One singular triangle obtained by transporting an edge-cylinder chart. -/
def edgePrismSimplex
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (cut : Fin 2) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      (homotopy.comp (edgePrismCylinderMap cut))

/-- [definition] The canonical oriented two-triangle prism of an addressed edge homotopy. -/
def edgeHomotopyPrism
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) : SphereChain 2 :=
  simplexGenerator (edgePrismSimplex homotopy 0) -
    simplexGenerator (edgePrismSimplex homotopy 1)

/-- [definition] The lower or upper horizontal edge of the exact edge cylinder. -/
def edgeCylinderEndMap (timeVertex : Fin 2) :
    C(PrismSegment, unitInterval × PrismSegment) where
  toFun point := (segmentTime (stdSimplex.vertex timeVertex), point)
  continuous_toFun := continuous_const.prodMk continuous_id

/-- [definition] One vertical edge of the exact edge cylinder. -/
def edgeCylinderVertexMap (sourceVertex : Fin 2) :
    C(PrismSegment, unitInterval × PrismSegment) where
  toFun point := (segmentTime point, stdSimplex.vertex sourceVertex)
  continuous_toFun := segmentTime.continuous.prodMk continuous_const

/-- [definition] The singular horizontal endpoint of an edge homotopy. -/
def edgeHomotopyEndSimplex
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (timeVertex : Fin 2) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
      (homotopy.comp (edgeCylinderEndMap timeVertex))

/-- [definition] The singular vertical path traced by one endpoint of an edge homotopy. -/
def edgeHomotopyVertexSimplex
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (sourceVertex : Fin 2) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
      (homotopy.comp (edgeCylinderVertexMap sourceVertex))

/-- [proved-derived; formal-checked] Restricting the time coordinate of an edge-prism chart
composes its ordered label word with the exact face injection. -/
theorem edgePrismSegmentMap_face (cut : Fin 2) (face : Fin 3) :
    (edgePrismSegmentMap cut).comp (simplexFaceMap (degree := 1) face) =
      ({ toFun := stdSimplex.map (edgePrismTimeLabels cut ∘ face.succAbove)
         continuous_toFun := stdSimplex.continuous_map _ } : C(PrismSegment, PrismSegment)) := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (edgePrismTimeLabels cut)
      (stdSimplex.map face.succAbove point) =
    stdSimplex.map (edgePrismTimeLabels cut ∘ face.succAbove) point
  rw [stdSimplex.map_comp_apply]

/-- [proved-derived; formal-checked] The source coordinate of the edge-prism chart carries the
same addressed face law. -/
theorem edgePrismSourceMap_face (cut : Fin 2) (face : Fin 3) :
    (edgePrismSourceMap cut).comp (simplexFaceMap (degree := 1) face) =
      ({ toFun := stdSimplex.map (edgePrismSourceLabels cut ∘ face.succAbove)
         continuous_toFun := stdSimplex.continuous_map _ } : C(PrismSegment, PrismSegment)) := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (edgePrismSourceLabels cut)
      (stdSimplex.map face.succAbove point) =
    stdSimplex.map (edgePrismSourceLabels cut ∘ face.succAbove) point
  rw [stdSimplex.map_comp_apply]

private theorem edgePrismCylinderMap_face_zero_zero :
    (edgePrismCylinderMap 0).comp (simplexFaceMap (degree := 1) 0) =
      edgeCylinderEndMap 1 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((edgePrismSegmentMap 0).comp
        (simplexFaceMap (degree := 1) 0)) point) =
      segmentTime (stdSimplex.vertex 1)
    rw [edgePrismSegmentMap_face]
    apply Subtype.ext
    have hlabels : edgePrismTimeLabels 0 ∘ Fin.succAbove 0 =
        fun _ => (1 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change (stdSimplex.map (fun _ : Fin 2 => (1 : Fin 2)) point) 1 = 1
    simp [FunOnFinite.linearMap_apply_apply, stdSimplex.sum_eq_one]
  · change ((edgePrismSourceMap 0).comp
        (simplexFaceMap (degree := 1) 0)) point = point
    rw [edgePrismSourceMap_face]
    have hlabels : edgePrismSourceLabels 0 ∘ Fin.succAbove 0 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    exact stdSimplex.map_id_apply point

private theorem edgePrismCylinderMap_face_zero_two :
    (edgePrismCylinderMap 0).comp (simplexFaceMap (degree := 1) 2) =
      edgeCylinderVertexMap 0 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((edgePrismSegmentMap 0).comp
        (simplexFaceMap (degree := 1) 2)) point) = segmentTime point
    rw [edgePrismSegmentMap_face]
    have hlabels : edgePrismTimeLabels 0 ∘ Fin.succAbove 2 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    exact congrArg segmentTime (stdSimplex.map_id_apply point)
  · change ((edgePrismSourceMap 0).comp
        (simplexFaceMap (degree := 1) 2)) point = stdSimplex.vertex 0
    rw [edgePrismSourceMap_face]
    have hlabels : edgePrismSourceLabels 0 ∘ Fin.succAbove 2 =
        fun _ => (0 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    apply stdSimplex.ext
    funext coordinate
    fin_cases coordinate <;>
      simp [FunOnFinite.linearMap_apply_apply, stdSimplex.sum_eq_one]

private theorem edgePrismCylinderMap_face_one_zero :
    (edgePrismCylinderMap 1).comp (simplexFaceMap (degree := 1) 0) =
      edgeCylinderVertexMap 1 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((edgePrismSegmentMap 1).comp
        (simplexFaceMap (degree := 1) 0)) point) = segmentTime point
    rw [edgePrismSegmentMap_face]
    have hlabels : edgePrismTimeLabels 1 ∘ Fin.succAbove 0 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    exact congrArg segmentTime (stdSimplex.map_id_apply point)
  · change ((edgePrismSourceMap 1).comp
        (simplexFaceMap (degree := 1) 0)) point = stdSimplex.vertex 1
    rw [edgePrismSourceMap_face]
    have hlabels : edgePrismSourceLabels 1 ∘ Fin.succAbove 0 =
        fun _ => (1 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    apply stdSimplex.ext
    funext coordinate
    fin_cases coordinate <;>
      simp [FunOnFinite.linearMap_apply_apply, stdSimplex.sum_eq_one]

private theorem edgePrismCylinderMap_face_one_two :
    (edgePrismCylinderMap 1).comp (simplexFaceMap (degree := 1) 2) =
      edgeCylinderEndMap 0 := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((edgePrismSegmentMap 1).comp
        (simplexFaceMap (degree := 1) 2)) point) =
      segmentTime (stdSimplex.vertex 0)
    rw [edgePrismSegmentMap_face]
    apply Subtype.ext
    have hlabels : edgePrismTimeLabels 1 ∘ Fin.succAbove 2 =
        fun _ => (0 : Fin 2) := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    change (stdSimplex.map (fun _ : Fin 2 => (0 : Fin 2)) point) 1 = 0
    simp [FunOnFinite.linearMap_apply_apply]
  · change ((edgePrismSourceMap 1).comp
        (simplexFaceMap (degree := 1) 2)) point = point
    rw [edgePrismSourceMap_face]
    have hlabels : edgePrismSourceLabels 1 ∘ Fin.succAbove 2 = id := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
    exact stdSimplex.map_id_apply point

private theorem edgePrismCylinderMap_internal :
    (edgePrismCylinderMap 0).comp (simplexFaceMap (degree := 1) 1) =
      (edgePrismCylinderMap 1).comp (simplexFaceMap (degree := 1) 1) := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime (((edgePrismSegmentMap 0).comp
        (simplexFaceMap (degree := 1) 1)) point) =
      segmentTime (((edgePrismSegmentMap 1).comp
        (simplexFaceMap (degree := 1) 1)) point)
    rw [edgePrismSegmentMap_face, edgePrismSegmentMap_face]
    have hlabels : edgePrismTimeLabels 0 ∘ Fin.succAbove 1 =
        edgePrismTimeLabels 1 ∘ Fin.succAbove 1 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]
  · change ((edgePrismSourceMap 0).comp
        (simplexFaceMap (degree := 1) 1)) point =
      ((edgePrismSourceMap 1).comp
        (simplexFaceMap (degree := 1) 1)) point
    rw [edgePrismSourceMap_face, edgePrismSourceMap_face]
    have hlabels : edgePrismSourceLabels 0 ∘ Fin.succAbove 1 =
        edgePrismSourceLabels 1 ∘ Fin.succAbove 1 := by
      funext vertex
      fin_cases vertex <;> rfl
    rw [hlabels]

private theorem edgePrismSimplex_face_eq
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (cut : Fin 2) (face : Fin 3)
    (edgeMap : C(PrismSegment, unitInterval × PrismSegment))
    (mapLaw : (edgePrismCylinderMap cut).comp
      (simplexFaceMap (degree := 1) face) = edgeMap) :
    simplexFace face (edgePrismSimplex homotopy cut) =
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1))).symm
          (homotopy.comp edgeMap) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization]
  simp only [edgePrismSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  apply congrArg homotopy
  exact DFunLike.congr_fun mapLaw point

/-- [proved-derived; formal-checked] The exact oriented boundary of an edge homotopy prism is
upper edge minus lower edge, plus the initial endpoint path minus the terminal endpoint path.
The diagonal seam is retained until its two occurrences cancel. -/
theorem boundary_edgeHomotopyPrism
    (homotopy : C(unitInterval × PrismSegment,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    SphereSingularChainComplex.d 2 1 (edgeHomotopyPrism homotopy) =
      simplexGenerator (edgeHomotopyEndSimplex homotopy 1) -
        simplexGenerator (edgeHomotopyEndSimplex homotopy 0) +
          simplexGenerator (edgeHomotopyVertexSimplex homotopy 0) -
            simplexGenerator (edgeHomotopyVertexSimplex homotopy 1) := by
  rw [edgeHomotopyPrism, map_sub]
  simp only [boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_three]
  rw [edgePrismSimplex_face_eq homotopy 0 0 _
      edgePrismCylinderMap_face_zero_zero,
    edgePrismSimplex_face_eq homotopy 0 2 _
      edgePrismCylinderMap_face_zero_two,
    edgePrismSimplex_face_eq homotopy 1 0 _
      edgePrismCylinderMap_face_one_zero,
    edgePrismSimplex_face_eq homotopy 1 2 _
      edgePrismCylinderMap_face_one_two]
  have internalFace :
      simplexFace 1 (edgePrismSimplex homotopy 0) =
        simplexFace 1 (edgePrismSimplex homotopy 1) := by
    apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 1))).injective
    repeat rw [simplexFace_realization]
    simp only [edgePrismSimplex, Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro point
    apply congrArg homotopy
    exact DFunLike.congr_fun edgePrismCylinderMap_internal point
  rw [internalFace]
  norm_num [edgeHomotopyEndSimplex, edgeHomotopyVertexSimplex]
  module

/-- [proved-derived; formal-checked] A lateral tetrahedron face is the canonical edge-cylinder
chart whenever its two ordered label words agree.  Both time and source incidence are retained. -/
theorem prismCylinderMap_face_eq_edgePrismCylinderMap
    (cut : Fin 3) (tetraFace : Fin 4) (edgeCut : Fin 2) (triangleFace : Fin 3)
    (timeLaw : prismTimeLabels cut ∘ tetraFace.succAbove =
      edgePrismTimeLabels edgeCut)
    (sourceLaw : prismTriangleLabels cut ∘ tetraFace.succAbove =
      triangleFace.succAbove ∘ edgePrismSourceLabels edgeCut) :
    (prismCylinderMap cut).comp (simplexFaceMap (degree := 2) tetraFace) =
      (triangleCylinderFace triangleFace).comp (edgePrismCylinderMap edgeCut) := by
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · change segmentTime
        (stdSimplex.map (prismTimeLabels cut)
          (stdSimplex.map tetraFace.succAbove point)) =
      segmentTime (stdSimplex.map (edgePrismTimeLabels edgeCut) point)
    rw [stdSimplex.map_comp_apply, timeLaw]
  · change stdSimplex.map (prismTriangleLabels cut)
        (stdSimplex.map tetraFace.succAbove point) =
      stdSimplex.map triangleFace.succAbove
        (stdSimplex.map (edgePrismSourceLabels edgeCut) point)
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, sourceLaw]

/-- [proved-derived; formal-checked] Transporting the preceding source identity through an
arbitrary sphere homotopy identifies the actual lateral singular triangle with its normalized
edge-prism occurrence. -/
theorem prismSimplex_side_eq_edgePrismSimplex
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (cut : Fin 3) (tetraFace : Fin 4) (edgeCut : Fin 2) (triangleFace : Fin 3)
    (timeLaw : prismTimeLabels cut ∘ tetraFace.succAbove =
      edgePrismTimeLabels edgeCut)
    (sourceLaw : prismTriangleLabels cut ∘ tetraFace.succAbove =
      triangleFace.succAbove ∘ edgePrismSourceLabels edgeCut) :
    simplexFace tetraFace (prismSimplex homotopy cut) =
      edgePrismSimplex (homotopy.comp (triangleCylinderFace triangleFace)) edgeCut := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [prismSimplex_face_eq]
  simp [edgePrismSimplex]
  rw [prismCylinderMap_face_eq_edgePrismCylinderMap cut tetraFace edgeCut triangleFace
      timeLaw sourceLaw]

/-- [proved-derived; formal-checked] The two side occurrences over any triangle face are exactly
one canonical edge prism of the restricted homotopy.  Thus the lateral word depends on the shared
addressed edge rather than on its parent triangle. -/
theorem triangleFacePrism_eq_edgeHomotopyPrism
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere))
    (face : Fin 3) :
    triangleFacePrism homotopy face =
      edgeHomotopyPrism (homotopy.comp (triangleCylinderFace face)) := by
  fin_cases face
  · simp only [triangleFacePrism, edgeHomotopyPrism]
    congr 1
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl
  · simp only [triangleFacePrism, edgeHomotopyPrism]
    congr 1
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl
  · simp only [triangleFacePrism, edgeHomotopyPrism]
    congr 1
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl
    · apply congrArg simplexGenerator
      apply prismSimplex_side_eq_edgePrismSimplex
      · funext vertex
        fin_cases vertex <;> rfl
      · funext vertex
        fin_cases vertex <;> rfl

/-- [proved-derived; formal-checked] Within the uniform refined carrier family, equal addressed
source edges return literally equal lateral prism currents even when they occur in different
parent triangles and at different face indices. -/
theorem refinedAffineCarrierFamily_facePrism_congr
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (first second : (refinedTriangleComplex chain family.scale).Cell)
    (firstFace secondFace : Fin 3)
    (sourceLaw :
      (refinedTriangleSourceMap first).comp
          (simplexFaceMap (degree := 1) firstFace) =
        (refinedTriangleSourceMap second).comp
          (simplexFaceMap (degree := 1) secondFace)) :
    triangleFacePrism (family.carrier first).affineSphereHomotopy firstFace =
      triangleFacePrism (family.carrier second).affineSphereHomotopy secondFace := by
  rw [triangleFacePrism_eq_edgeHomotopyPrism,
    triangleFacePrism_eq_edgeHomotopyPrism]
  apply congrArg edgeHomotopyPrism
  exact family.homotopy_face_congr first second firstFace secondFace sourceLaw

/-- [definition] One addressed edge occurrence of the fixed refined triangle population.  The
parent cell and face index remain in the occurrence even when another occurrence has the same
singular edge. -/
abbrev RefinedTriangleFace {chain : SphereChain 2} {scale : ℕ} :=
  RefinedTriangleCell chain scale × Fin 3

/-- [definition] The exact rational weight of one refined descendant occurrence.  It retains
both the coefficient of its supported parent and the orientation of its complete refinement word. -/
def refinedTriangleCoefficient {chain : SphereChain 2} {scale : ℕ}
    (cell : RefinedTriangleCell chain scale) : ℚ :=
  sphereChainCoefficient 2 chain cell.1.1 * triangleWordSign cell.2

/-- [proved-derived; formal-checked] The complete addressed refined-cell population reconstructs
the fixed-depth barycentric refinement exactly.  No descendant is inferred from an endpoint or
discarded through a zero/duplicate receiver. -/
theorem sum_refinedTriangleCoefficient_simplexGenerator
    (chain : SphereChain 2) (scale : ℕ) :
    (∑ cell : RefinedTriangleCell chain scale,
      refinedTriangleCoefficient cell •
        simplexGenerator (refinedTriangleSimplex cell)) =
      iteratedBarycentricTriangleSubdivision scale chain := by
  classical
  have supportReconstruction :
      (∑ source : ↑(sphereChainSupport 2 chain),
        sphereChainCoefficient 2 chain source.1 •
          simplexGenerator source.1) = chain := by
    have reconstruction :=
      sum_support_sphereChainCoefficient_simplexGenerator 2 chain
    rw [← Finset.sum_attach, Finset.attach_eq_univ] at reconstruction
    exact reconstruction
  calc
    (∑ cell : RefinedTriangleCell chain scale,
        refinedTriangleCoefficient cell •
          simplexGenerator (refinedTriangleSimplex cell)) =
        ∑ source : ↑(sphereChainSupport 2 chain), ∑ word : TriangleWord scale,
          (sphereChainCoefficient 2 chain source.1 * triangleWordSign word) •
            simplexGenerator (triangleWordSubsimplex word source.1) := by
      rw [Fintype.sum_prod_type]
      simp only [refinedTriangleCoefficient, refinedTriangleSimplex]
    _ = ∑ source : ↑(sphereChainSupport 2 chain),
        iteratedBarycentricTriangleSubdivision scale
          (sphereChainCoefficient 2 chain source.1 •
            simplexGenerator source.1) := by
      apply Fintype.sum_congr _ _
      intro source
      rw [iteratedBarycentricTriangleSubdivision_smul,
        triangleWordExpansion, Finset.smul_sum]
      simp only [mul_smul]
    _ = iteratedBarycentricTriangleSubdivision scale
        (∑ source : ↑(sphereChainSupport 2 chain),
          sphereChainCoefficient 2 chain source.1 •
            simplexGenerator source.1) := by
      symm
      exact iteratedBarycentricTriangleSubdivision_sum scale _
    _ = iteratedBarycentricTriangleSubdivision scale chain := by
      rw [supportReconstruction]

/-- [definition] The actual singular edge carried by one refined parent-face occurrence. -/
def refinedTriangleFaceSimplex {chain : SphereChain 2} {scale : ℕ}
    (occurrence : RefinedTriangleFace (chain := chain) (scale := scale)) :
    SphereSingularSimplex 1 :=
  simplexFace occurrence.2 (refinedTriangleSimplex occurrence.1)

/-- [definition] A receiver on arbitrary singular edges which returns the prism of a represented
refined face and zero outside the represented population.  Choice does not lose lineage: the
next theorem proves that every possible representative returns the same complete prism current. -/
def representedEdgePrism {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (simplex : SphereSingularSimplex 1) : SphereChain 2 := by
  classical
  if represented : ∃ occurrence : RefinedTriangleFace
      (chain := chain) (scale := family.scale),
      refinedTriangleFaceSimplex occurrence = simplex then
    let occurrence := Classical.choose represented
    exact triangleFacePrism
      (family.carrier occurrence.1).affineSphereHomotopy occurrence.2
  else
    exact 0

/-- [proved-derived; formal-checked] Every represented face evaluates to its own retained prism,
independently of which equal addressed edge was selected by the receiver. -/
theorem representedEdgePrism_refinedFace {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (occurrence : RefinedTriangleFace
      (chain := chain) (scale := family.scale)) :
    representedEdgePrism family (refinedTriangleFaceSimplex occurrence) =
      triangleFacePrism
        (family.carrier occurrence.1).affineSphereHomotopy occurrence.2 := by
  classical
  rw [representedEdgePrism]
  split_ifs with represented
  · let selected := Classical.choose represented
    have selectedLaw : refinedTriangleFaceSimplex selected =
        refinedTriangleFaceSimplex occurrence :=
      Classical.choose_spec represented
    have realizationLaw := congrArg
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1))) selectedLaw
    have sourceLaw :
        (refinedTriangleSourceMap selected.1).comp
            (simplexFaceMap (degree := 1) selected.2) =
          (refinedTriangleSourceMap occurrence.1).comp
            (simplexFaceMap (degree := 1) occurrence.2) := by
      change
        ((TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk 2)))
            (refinedTriangleSimplex selected.1)).comp
              (simplexFaceMap (degree := 1) selected.2) =
        ((TopCat.toSSetObjEquiv sphereTopCat
          (Opposite.op (SimplexCategory.mk 2)))
            (refinedTriangleSimplex occurrence.1)).comp
              (simplexFaceMap (degree := 1) occurrence.2)
      simpa only [refinedTriangleFaceSimplex, simplexFace_realization] using realizationLaw
    exact refinedAffineCarrierFamily_facePrism_congr family
      selected.1 occurrence.1 selected.2 occurrence.2 sourceLaw
  · exact False.elim (represented ⟨occurrence, rfl⟩)

/-- [definition] Rational coefficient transport into one represented edge prism. -/
def representedEdgePrismCoefficient (value : SphereChain 2) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
        rfl }

/-- [definition] Coproduct-linear extension of the represented-edge receiver. -/
def representedEdgePrismMorphism {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 2 :=
  Limits.Sigma.desc fun simplex =>
    representedEdgePrismCoefficient (representedEdgePrism family simplex)

@[simp]
theorem representedEdgePrismMorphism_simplexGenerator
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (simplex : SphereSingularSimplex 1) :
    representedEdgePrismMorphism family (simplexGenerator simplex) =
      representedEdgePrism family simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 1 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => representedEdgePrismCoefficient
          (representedEdgePrism family source))) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- [definition] The complete retained lateral boundary of the prism.  The six occurrences are
not replaced by an endpoint relation: later source-face compatibility must cancel them. -/
def triangleHomotopyLateralBoundary
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) : SphereChain 2 :=
  simplexGenerator (simplexFace 2 (prismSimplex homotopy 0)) -
    simplexGenerator (simplexFace 3 (prismSimplex homotopy 0)) -
    simplexGenerator (simplexFace 0 (prismSimplex homotopy 1)) +
    simplexGenerator (simplexFace 3 (prismSimplex homotopy 1)) +
    simplexGenerator (simplexFace 0 (prismSimplex homotopy 2)) -
    simplexGenerator (simplexFace 1 (prismSimplex homotopy 2))

/-- [proved-derived; formal-checked] The six retained lateral occurrences are exactly the
alternating source-boundary word of the three two-triangle face prisms.  This is the degree-two
instance of the prism identity's `-P(∂c)` term. -/
theorem triangleHomotopyLateralBoundary_eq_facePrisms
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    triangleHomotopyLateralBoundary homotopy =
      -triangleFacePrism homotopy 0 +
        triangleFacePrism homotopy 1 -
          triangleFacePrism homotopy 2 := by
  rw [triangleHomotopyLateralBoundary]
  simp only [triangleFacePrism]
  module

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The complete lateral current of one refined cell factors
through the ordinary singular boundary of that same addressed source occurrence.  The minus sign
is the prism convention `upper - lower - P(∂source)`. -/
theorem triangleHomotopyLateralBoundary_refinedCell
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cell : RefinedTriangleCell chain family.scale) :
    triangleHomotopyLateralBoundary
        (family.carrier cell).affineSphereHomotopy =
      -representedEdgePrismMorphism family
        (SphereSingularChainComplex.d 2 1
          (simplexGenerator (refinedTriangleSimplex cell))) := by
  rw [triangleHomotopyLateralBoundary_eq_facePrisms,
    boundary_simplexGenerator, map_sum]
  simp only [map_smul, representedEdgePrismMorphism_simplexGenerator]
  rw [Fin.sum_univ_three]
  have hface (face : Fin 3) :
      representedEdgePrism family
          (simplexFace face (refinedTriangleSimplex cell)) =
        triangleFacePrism
          (family.carrier cell).affineSphereHomotopy face := by
    exact representedEdgePrism_refinedFace family (cell, face)
  rw [hface 0, hface 1, hface 2]
  norm_num
  module

/-- [definition] The coefficient-weighted lateral return of the complete refined triangle
population. -/
def refinedPrismLateralCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      triangleHomotopyLateralBoundary
        (family.carrier cell).affineSphereHomotopy

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The total lateral return is exactly the represented-edge
image of the complete refined singular boundary.  This is the global local-to-global factorization:
the future edge receiver sees no parent-triangle copies beyond the ordinary boundary current. -/
theorem refinedPrismLateralCurrent_eq_boundary
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedPrismLateralCurrent family =
      -representedEdgePrismMorphism family
        (SphereSingularChainComplex.d 2 1
          (iteratedBarycentricTriangleSubdivision family.scale chain)) := by
  rw [refinedPrismLateralCurrent,
    ← sum_refinedTriangleCoefficient_simplexGenerator chain family.scale]
  simp only [map_sum, map_smul]
  simp_rw [triangleHomotopyLateralBoundary_refinedCell family]
  simp only [smul_neg, Finset.sum_neg_distrib]

/-- [proved-derived; formal-checked] A source two-cycle therefore has zero complete lateral prism
return after the one uniform refinement.  Cancellation is inherited from the source boundary law,
not established by an enumerated face-pair campaign. -/
theorem refinedPrismLateralCurrent_eq_zero
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    refinedPrismLateralCurrent family = 0 := by
  rw [refinedPrismLateralCurrent_eq_boundary,
    boundary_iteratedBarycentricTriangleSubdivision, cycle,
    iteratedBarycentricEdgeSubdivision_zero, map_zero]
  exact neg_zero

/-- [proved-derived; formal-checked] Exact singular-prism reconstruction.  The boundary is the
upper receiver minus the lower receiver plus the complete six-face reconstruction fibre. -/
theorem boundary_triangleHomotopyPrism
    (homotopy : C(unitInterval × Triangle,
      HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    SphereSingularChainComplex.d 3 2 (triangleHomotopyPrism homotopy) =
      simplexGenerator (homotopyEndSimplex homotopy 1) -
        simplexGenerator (homotopyEndSimplex homotopy 0) +
          triangleHomotopyLateralBoundary homotopy := by
  rw [triangleHomotopyPrism, map_add, map_sub]
  simp only [boundary_simplexGenerator]
  repeat rw [Fin.sum_univ_four]
  rw [prismSimplex_internal_first, prismSimplex_internal_second,
    prismSimplex_top, prismSimplex_bottom]
  rw [triangleHomotopyLateralBoundary]
  norm_num
  module

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The lower endpoint of a refined carrier prism is the actual
addressed refined source simplex, not merely a pointwise-equal replacement. -/
theorem homotopyEndSimplex_refinedCarrier_zero
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cell : RefinedTriangleCell chain family.scale) :
    homotopyEndSimplex (family.carrier cell).affineSphereHomotopy 0 =
      refinedTriangleSimplex cell := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp only [homotopyEndSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  change (family.carrier cell).affineSphereHomotopy (0, point) =
    refinedTriangleSourceMap cell point
  exact family.homotopy_zero cell point

/-- [definition] The complete coefficient-weighted three-current of the refined affine carrier
family. -/
def refinedPrismCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 3 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      triangleHomotopyPrism (family.carrier cell).affineSphereHomotopy

/-- [definition] The complete upper affine-label current returned by the same retained prism
population.  Repeated-label degeneracies remain explicit at this receiver. -/
def refinedPrismUpperCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      simplexGenerator
        (homotopyEndSimplex (family.carrier cell).affineSphereHomotopy 1)

/-- [definition] The same upper current written directly in the affine-label chart.  This is a
raw singular current: equal or repeated labels are retained as singular occurrences. -/
def rawAffineLabelSimplex (labels : Fin 3 → TetraVertex) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
    (lowLabelSphereMap 2 (by omega) labels)

/-- [definition] The raw affine label occurrence in degree zero. -/
def rawAffineLabelVertex (label : TetraVertex) : SphereSingularSimplex 0 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).symm
    (lowLabelSphereMap 0 (by omega) (fun _ : Fin 1 => label))

/-- [definition] The raw affine label occurrence in degree one. -/
def rawAffineLabelEdge (labels : Fin 2 → TetraVertex) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
    (lowLabelSphereMap 1 (by omega) labels)

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] Restricting a raw affine label triangle gives the raw affine
label edge with the exact ordered face injection. -/
theorem rawAffineLabelSimplex_face (labels : Fin 3 → TetraVertex) (face : Fin 3) :
    simplexFace face (rawAffineLabelSimplex labels) =
      rawAffineLabelEdge (labels ∘ face.succAbove) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  rw [simplexFace_realization]
  simp only [rawAffineLabelSimplex, rawAffineLabelEdge, Equiv.apply_symm_apply]
  change
    (lowLabelSphereMap 2 (by omega) labels).comp (simplexFaceMap face) =
      lowLabelSphereMap 1 (by omega) (labels ∘ face.succAbove)
  rw [lowLabelSphereMap_face (by omega) labels face]

/-- [proved-derived; formal-checked] The raw affine label triangle has its complete alternating
boundary in terms of the raw affine label edges, including all repeated-label faces. -/
theorem rawAffineLabelSimplex_boundary (labels : Fin 3 → TetraVertex) :
    SphereSingularChainComplex.d 2 1
        (simplexGenerator (rawAffineLabelSimplex labels)) =
      simplexGenerator (rawAffineLabelEdge (labels ∘ (0 : Fin 3).succAbove)) -
        simplexGenerator (rawAffineLabelEdge (labels ∘ (1 : Fin 3).succAbove)) +
          simplexGenerator (rawAffineLabelEdge (labels ∘ (2 : Fin 3).succAbove)) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_three]
  norm_num
  rw [rawAffineLabelSimplex_face, rawAffineLabelSimplex_face,
    rawAffineLabelSimplex_face]
  have hfaceZero : labels ∘ (0 : Fin 3).succAbove = labels ∘ Fin.succ := by
    funext index
    fin_cases index <;> rfl
  rw [hfaceZero]
  simp only [sub_eq_add_neg]

/-- [proved-derived; formal-checked] The constant raw triangle `[a,a,a]` is an explicit filler for
the constant raw edge `[a,a]`; the constant singular occurrence is not declared zero. -/
theorem rawAffineLabelConstantTriangle_boundary (label : TetraVertex) :
    SphereSingularChainComplex.d 2 1
        (simplexGenerator (rawAffineLabelSimplex ![label, label, label])) =
      simplexGenerator (rawAffineLabelEdge ![label, label]) := by
  rw [rawAffineLabelSimplex_boundary]
  norm_num [Function.comp_apply, Fin.succAbove, sub_eq_add_neg]
  have h0 : (![label, label, label] : Fin 3 → TetraVertex) ∘ Fin.succ =
      ![label, label] := by
    funext index
    fin_cases index <;> rfl
  have h1 : (![label, label, label] : Fin 3 → TetraVertex) ∘
      (1 : Fin 3).succAbove = ![label, label] := by
    funext index
    fin_cases index <;> rfl
  have h2 : (![label, label, label] : Fin 3 → TetraVertex) ∘
      (2 : Fin 3).succAbove = ![label, label] := by
    funext index
    fin_cases index <;> rfl
  rw [h0, h1, h2]
  abel

/-- [proved-derived; formal-checked] The non-monotone fold `[a,b,a]` retains its middle constant
edge term explicitly.  This is the exact two-dimensional correction datum for reversed pairs. -/
theorem rawAffineLabelFoldTriangle_boundary (first second : TetraVertex) :
    SphereSingularChainComplex.d 2 1
        (simplexGenerator (rawAffineLabelSimplex ![first, second, first])) =
      simplexGenerator (rawAffineLabelEdge ![second, first]) -
        simplexGenerator (rawAffineLabelEdge ![first, first]) +
          simplexGenerator (rawAffineLabelEdge ![first, second]) := by
  rw [rawAffineLabelSimplex_boundary]
  norm_num [Function.comp_apply, Fin.succAbove, sub_eq_add_neg]
  have h0 : (![first, second, first] : Fin 3 → TetraVertex) ∘ Fin.succ =
      ![second, first] := by
    funext index
    fin_cases index <;> rfl
  have h1 : (![first, second, first] : Fin 3 → TetraVertex) ∘
      (1 : Fin 3).succAbove = ![first, first] := by
    funext index
    fin_cases index <;> rfl
  have h2 : (![first, second, first] : Fin 3 → TetraVertex) ∘
      (2 : Fin 3).succAbove = ![first, second] := by
    funext index
    fin_cases index <;> rfl
  rw [h0, h1, h2]

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] Restricting a raw affine label edge gives the corresponding
raw affine label vertex.  This retains the ordered face injection, including repeated labels. -/
theorem rawAffineLabelEdge_face (labels : Fin 2 → TetraVertex) (face : Fin 2) :
    simplexFace face (rawAffineLabelEdge labels) =
      rawAffineLabelVertex ((labels ∘ face.succAbove) 0) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).injective
  rw [simplexFace_realization]
  simp only [rawAffineLabelEdge, rawAffineLabelVertex, Equiv.apply_symm_apply]
  change
    (lowLabelSphereMap 1 (by omega) labels).comp (simplexFaceMap face) =
      lowLabelSphereMap 0 (by omega)
        (fun _ : Fin 1 => (labels ∘ face.succAbove) 0)
  rw [lowLabelSphereMap_face (by omega) labels face]
  congr 1
  funext index
  fin_cases index
  rfl

/-- [proved-derived; formal-checked] The raw affine label edge has its exact ordered endpoint
boundary, even on a repeated-label fold. -/
theorem rawAffineLabelEdge_boundary (labels : Fin 2 → TetraVertex) :
    SphereSingularChainComplex.d 1 0
        (simplexGenerator (rawAffineLabelEdge labels)) =
      simplexGenerator (rawAffineLabelVertex (labels 1)) -
        simplexGenerator (rawAffineLabelVertex (labels 0)) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_two]
  norm_num
  rw [rawAffineLabelEdge_face, rawAffineLabelEdge_face]
  simp [Function.comp_apply, Fin.succAbove, sub_eq_add_neg]

/-- [proved-derived; formal-checked] Restricting the canonical ordered affine label face along
one of its addressed edges is exactly that radial singular edge.  This is an equality of the
complete source maps, not merely of endpoints. -/
theorem rawAffineLabelEdge_succAbove_succAbove
    (face : Fin 4) (localFace : Fin 3) :
    rawAffineLabelEdge (face.succAbove ∘ localFace.succAbove) =
      simplexFace localFace (radialSingularSimplex face) := by
  calc
    rawAffineLabelEdge (face.succAbove ∘ localFace.succAbove) =
        simplexFace localFace (rawAffineLabelSimplex face.succAbove) :=
      (rawAffineLabelSimplex_face face.succAbove localFace).symm
    _ = simplexFace localFace (radialSingularSimplex face) := by
      rw [rawAffineLabelSimplex,
        lowLabelSphereSimplex_succAbove_eq_radialSingularSimplex]

/-- [proved-derived; formal-checked] Every increasing tetrahedral endpoint word realizes the
already-owned addressed radial edge simplex.  The six cases differ only in which radial face
presents the shared edge; the ordered label word itself is invariant. -/
theorem rawAffineLabelEdge_edgeEndpoint (edge : TetraEdge) :
    rawAffineLabelEdge (edgeEndpoint edge) = edgeSimplex edge := by
  cases edge with
  | e01 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (2 : Fin 4) (2 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl
  | e02 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (1 : Fin 4) (2 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl
  | e03 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (1 : Fin 4) (1 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl
  | e12 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (0 : Fin 4) (2 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl
  | e13 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (0 : Fin 4) (1 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl
  | e23 =>
      rw [edgeSimplex]
      convert rawAffineLabelEdge_succAbove_succAbove (0 : Fin 4) (0 : Fin 3) using 1
      apply congrArg rawAffineLabelEdge
      funext index
      fin_cases index <;> rfl

/-- [definition] The exact degree-one normalization current for one ordered pair of labels.
Increasing pairs already use the canonical radial chart.  Equal pairs retain one constant
triangle, while decreasing pairs retain the fold and the constant triangle which cancels its
middle edge. -/
def rawAffineLabelEdgeCorrection (first second : TetraVertex) : SphereChain 2 :=
  if first = second then
    simplexGenerator (rawAffineLabelSimplex ![first, first, first])
  else if first < second then
    0
  else
    simplexGenerator (rawAffineLabelSimplex ![first, second, first]) +
      simplexGenerator (rawAffineLabelSimplex ![first, first, first])

/-- [proved-derived; formal-checked] The correction current returns the complete difference
between the raw ordered affine edge and the realized finite oriented edge.  Reversal is therefore
not identified with a sign: the fold occurrence is the current which transports between the two
receiver presentations. -/
theorem rawAffineLabelEdgeCorrection_boundary (first second : TetraVertex) :
    SphereSingularChainComplex.d 2 1
        (rawAffineLabelEdgeCorrection first second) =
      simplexGenerator (rawAffineLabelEdge ![first, second]) -
        edgeRealization (labelledSimplexCarry 1 ![first, second]) := by
  have h01 : rawAffineLabelEdge ![(0 : TetraVertex), (1 : TetraVertex)] =
      edgeSimplex .e01 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e01 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  have h02 : rawAffineLabelEdge ![(0 : TetraVertex), (2 : TetraVertex)] =
      edgeSimplex .e02 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e02 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  have h03 : rawAffineLabelEdge ![(0 : TetraVertex), (3 : TetraVertex)] =
      edgeSimplex .e03 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e03 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  have h12 : rawAffineLabelEdge ![(1 : TetraVertex), (2 : TetraVertex)] =
      edgeSimplex .e12 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e12 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  have h13 : rawAffineLabelEdge ![(1 : TetraVertex), (3 : TetraVertex)] =
      edgeSimplex .e13 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e13 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  have h23 : rawAffineLabelEdge ![(2 : TetraVertex), (3 : TetraVertex)] =
      edgeSimplex .e23 := by
    convert rawAffineLabelEdge_edgeEndpoint TetraEdge.e23 using 1
    apply congrArg rawAffineLabelEdge
    funext index
    fin_cases index <;> rfl
  by_cases same : first = second
  · subst second
    rw [rawAffineLabelEdgeCorrection, if_pos rfl,
      rawAffineLabelConstantTriangle_boundary]
    fin_cases first <;>
      simp [orientedEdgeCarry, edgeRealization, edgeInitial, edgeTerminal,
        Fin.ext_iff]
  · by_cases increasing : first < second
    · rw [rawAffineLabelEdgeCorrection, if_neg same, if_pos increasing, map_zero]
      fin_cases first <;> fin_cases second <;>
        simp_all [orientedEdgeCarry, edgeRealization, edgeInitial, edgeTerminal,
          Fin.ext_iff, h01, h02, h03, h12, h13, h23]
    · rw [rawAffineLabelEdgeCorrection, if_neg same, if_neg increasing, map_add,
        rawAffineLabelFoldTriangle_boundary,
        rawAffineLabelConstantTriangle_boundary]
      fin_cases first <;> fin_cases second <;>
        simp_all [orientedEdgeCarry, edgeRealization, edgeInitial, edgeTerminal,
          Fin.ext_iff, h01, h02, h03, h12, h13, h23] <;>
        module

/-- [definition] The ordered label-pair normalization is an elementary boundary holon.  Its
source is the realized finite oriented edge, its target is the raw affine singular edge, and its
received current retains the fold/constant reconstruction fibre. -/
def affineLabelEdgeNormalizationHolon :
    Soma.Holonics.BoundaryHolon (SphereChain 1) (SphereChain 2) where
  Occurrence := TetraVertex × TetraVertex
  source occurrence :=
    edgeRealization (labelledSimplexCarry 1 ![occurrence.1, occurrence.2])
  target occurrence :=
    simplexGenerator (rawAffineLabelEdge ![occurrence.1, occurrence.2])
  receive occurrence := rawAffineLabelEdgeCorrection occurrence.1 occurrence.2
  boundary := (SphereSingularChainComplex.d 2 1).hom.toAddMonoidHom
  returnsBoundary := by
    intro occurrence
    exact rawAffineLabelEdgeCorrection_boundary occurrence.1 occurrence.2

/-- [definition] The degree-two normalization defect after the three edge corrections have been
subtracted.  It remains an addressed singular two-chain, including every repeated-label face. -/
def rawAffineLabelSimplexNormalizationDefect (labels : Fin 3 → TetraVertex) : SphereChain 2 :=
  simplexGenerator (rawAffineLabelSimplex labels) -
      faceRealization (labelledSimplexCarry 2 labels) -
    (rawAffineLabelEdgeCorrection ((labels ∘ (0 : Fin 3).succAbove) 0)
        ((labels ∘ (0 : Fin 3).succAbove) 1) -
      rawAffineLabelEdgeCorrection ((labels ∘ (1 : Fin 3).succAbove) 0)
        ((labels ∘ (1 : Fin 3).succAbove) 1) +
      rawAffineLabelEdgeCorrection ((labels ∘ (2 : Fin 3).succAbove) 0)
        ((labels ∘ (2 : Fin 3).succAbove) 1))

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The degree-two normalization defect is closed.  Its boundary
vanishes by the raw affine face law, the finite face-realization boundary law, and the three exact
degree-one correction boundaries. -/
theorem rawAffineLabelSimplexNormalizationDefect_boundary_zero
    (labels : Fin 3 → TetraVertex) :
    SphereSingularChainComplex.d 2 1
        (rawAffineLabelSimplexNormalizationDefect labels) = 0 := by
  unfold rawAffineLabelSimplexNormalizationDefect
  simp only [map_sub, map_add]
  rw [rawAffineLabelSimplex_boundary, faceRealization_boundary,
    rawAffineLabelEdgeCorrection_boundary,
    rawAffineLabelEdgeCorrection_boundary,
    rawAffineLabelEdgeCorrection_boundary]
  have hpair0 : (![ (labels ∘ (0 : Fin 3).succAbove) 0,
      (labels ∘ (0 : Fin 3).succAbove) 1] : Fin 2 → TetraVertex) =
      labels ∘ (0 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  have hpair1 : (![ (labels ∘ (1 : Fin 3).succAbove) 0,
      (labels ∘ (1 : Fin 3).succAbove) 1] : Fin 2 → TetraVertex) =
      labels ∘ (1 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  have hpair2 : (![ (labels ∘ (2 : Fin 3).succAbove) 0,
      (labels ∘ (2 : Fin 3).succAbove) 1] : Fin 2 → TetraVertex) =
      labels ∘ (2 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  rw [hpair0, hpair1, hpair2]
  change
    _ - edgeRealization
          (faceBoundary (labelledSimplexCarry 2 labels)) -
        (_ - _ + (_ - _)) = 0
  rw [show faceBoundary (labelledSimplexCarry 2 labels) =
      orientedEdgeCarry (labels 1) (labels 2) -
        orientedEdgeCarry (labels 0) (labels 2) +
          orientedEdgeCarry (labels 0) (labels 1) by
    change faceBoundary (orientedFaceCarry (labels 0) (labels 1) (labels 2)) = _
    rw [faceBoundary_orientedFaceCarry]]
  have hcarry0 : labelledSimplexCarry 1
      (labels ∘ (0 : Fin 3).succAbove) =
      orientedEdgeCarry (labels 1) (labels 2) := by
    change orientedEdgeCarry _ _ = _
    congr 1 <;> fin_cases labels <;> rfl
  have hcarry1 : labelledSimplexCarry 1
      (labels ∘ (1 : Fin 3).succAbove) =
      orientedEdgeCarry (labels 0) (labels 2) := by
    change orientedEdgeCarry _ _ = _
    congr 1 <;> fin_cases labels <;> rfl
  have hcarry2 : labelledSimplexCarry 1
      (labels ∘ (2 : Fin 3).succAbove) =
      orientedEdgeCarry (labels 0) (labels 1) := by
    change orientedEdgeCarry _ _ = _
    congr 1 <;> fin_cases labels <;> rfl
  rw [hcarry0, hcarry1, hcarry2]
  simp only [map_sub, map_add]
  simp only [sub_eq_add_neg]
  abel

def rawAffineLabelUpperCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
    ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      simplexGenerator
        (rawAffineLabelSimplex
          (refinedCellLabels lebesgue family.labeling cell))

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The prism's upper singular current is exactly the raw
affine-label current.  No repeated-label or degenerate singular occurrence is removed here. -/
theorem refinedPrismUpperCurrent_eq_rawAffineLabelUpperCurrent
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedPrismUpperCurrent family = rawAffineLabelUpperCurrent family := by
  rw [refinedPrismUpperCurrent, rawAffineLabelUpperCurrent]
  apply Fintype.sum_congr _ _
  intro cell
  congr 1
  apply congrArg simplexGenerator
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp only [homotopyEndSimplex, rawAffineLabelSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro point
  exact family.homotopy_one cell point

/-! The raw upper singular current and its finite point-carry receiver are kept separate.  The
receiver is the lawful normalization target: repeated labels yield the zero oriented face current,
while their raw singular occurrences remain in `refinedPrismUpperCurrent` and are not erased. -/

/-- [definition] The finite upper receiver obtained by carrying the complete refined source
population through its actual point labels. -/
def refinedPrismUpperFaceCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
      tetrahedralChainComplex.X 2 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      labelledSimplexCarry 2 (refinedCellLabels lebesgue family.labeling cell)

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The finite upper receiver is exactly the point-natural carry
of the complete refined source current.  This equality retains orientation and sends repeated
label words through the existing zero oriented-face law. -/
theorem refinedPrismUpperFaceCurrent_eq_pointCarryRefinedSource
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedPrismUpperFaceCurrent family =
      pointCarryMorphism
        (refinedClosedStarPointLabeling lebesgue family.labeling) 2
        (iteratedBarycentricTriangleSubdivision family.scale chain) := by
  rw [refinedPrismUpperFaceCurrent,
    ← sum_refinedTriangleCoefficient_simplexGenerator chain family.scale]
  simp only [map_sum, map_smul, pointCarryMorphism_simplexGenerator]
  apply Fintype.sum_congr _ _
  intro cell
  have hpoint := pointCarryMorphism_simplexGenerator
    (refinedClosedStarPointLabeling lebesgue family.labeling) 2
    (refinedTriangleSimplex cell)
  rw [hpoint]
  change refinedTriangleCoefficient cell •
      labelledSimplexCarry 2 (refinedCellLabels lebesgue family.labeling cell) =
    refinedTriangleCoefficient cell •
      labelledSimplexCarry 2
        (simplexPointLabels
          (refinedClosedStarPointLabeling lebesgue family.labeling)
          (refinedTriangleSimplex cell))
  rw [refinedCellLabels_eq_simplexPointLabels]

/-- [proved-derived; formal-checked] The normalized upper face is not a second carrier: it is
exactly the already-owned refined-cycle point current at the affine family's retained scale. -/
theorem refinedPrismUpperFaceCurrent_eq_refinedCyclePointCurrent
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedPrismUpperFaceCurrent family =
      refinedCyclePointCurrent
        (refinedClosedStarPointLabeling lebesgue family.labeling)
        family.scale chain := by
  simpa only [refinedCyclePointCurrent] using
    refinedPrismUpperFaceCurrent_eq_pointCarryRefinedSource family

/-- [proved-derived; formal-checked] A singular two-cycle returns a closed normalized upper
current.  Closure is inherited through the exact receiver equality, not reproved by a
subject-specific cancellation. -/
theorem refinedPrismUpperFaceCurrent_boundary_zero
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    faceBoundary (refinedPrismUpperFaceCurrent family) = 0 := by
  rw [refinedPrismUpperFaceCurrent_eq_refinedCyclePointCurrent family]
  exact refinedCyclePointCurrent_boundary_zero
    (refinedClosedStarPointLabeling lebesgue family.labeling)
    family.scale chain cycle

/-- [proved-derived; formal-checked] The normalized upper current of a singular sphere cycle is
forced onto the one-dimensional fundamental face line. -/
theorem refinedPrismUpperFaceCurrent_coordinates
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    refinedPrismUpperFaceCurrent family =
      refinedPrismUpperFaceCurrent family 0 • fundamentalFaceChain := by
  rw [refinedPrismUpperFaceCurrent_eq_refinedCyclePointCurrent family]
  exact refinedCyclePointCurrent_coordinates
    (refinedClosedStarPointLabeling lebesgue family.labeling)
    family.scale chain cycle

/-- [proved-derived; formal-checked] Realization of the normalized affine upper receiver is the
same exact coefficient on the explicit radial fundamental sphere cycle. -/
theorem faceRealization_refinedPrismUpperFaceCurrent
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    faceRealization (refinedPrismUpperFaceCurrent family) =
      refinedPrismUpperFaceCurrent family 0 • sphereFundamentalCandidate := by
  rw [refinedPrismUpperFaceCurrent_eq_refinedCyclePointCurrent family]
  exact faceRealization_refinedCyclePointCurrent
    (refinedClosedStarPointLabeling lebesgue family.labeling)
    family.scale chain cycle

/-- [definition] The complete lower source current returned by the same retained prism
population. -/
def refinedPrismLowerCurrent {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      simplexGenerator
        (homotopyEndSimplex (family.carrier cell).affineSphereHomotopy 0)

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] The lower prism receiver reconstructs the complete fixed-depth
refined source current exactly. -/
theorem refinedPrismLowerCurrent_eq_refinement
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedPrismLowerCurrent family =
      iteratedBarycentricTriangleSubdivision family.scale chain := by
  rw [refinedPrismLowerCurrent,
    ← sum_refinedTriangleCoefficient_simplexGenerator chain family.scale]
  apply Fintype.sum_congr _ _
  intro cell
  rw [homotopyEndSimplex_refinedCarrier_zero family cell]

set_option backward.isDefEq.respectTransparency.types true in
/-- [proved-derived; formal-checked] Summing the exact local prism identities preserves all three
global faces: upper receiver, lower receiver, and lateral reconstruction fibre. -/
theorem boundary_refinedPrismCurrent
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.d 3 2 (refinedPrismCurrent family) =
      refinedPrismUpperCurrent family - refinedPrismLowerCurrent family +
        refinedPrismLateralCurrent family := by
  rw [refinedPrismCurrent, map_sum]
  simp only [map_smul]
  simp_rw [boundary_triangleHomotopyPrism]
  rw [refinedPrismUpperCurrent, refinedPrismLowerCurrent,
    refinedPrismLateralCurrent]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] For a genuine source cycle, the assembled common-star prism
is an explicit homology from the complete refined source current to the affine-label current. -/
theorem boundary_refinedPrismCurrent_of_cycle
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    SphereSingularChainComplex.d 3 2 (refinedPrismCurrent family) =
      refinedPrismUpperCurrent family -
        iteratedBarycentricTriangleSubdivision family.scale chain := by
  rw [boundary_refinedPrismCurrent,
    refinedPrismLowerCurrent_eq_refinement,
    refinedPrismLateralCurrent_eq_zero family cycle, add_zero]

/-! ## The same construction as one elementary holonic occurrence population -/

set_option backward.isDefEq.respectTransparency.types true in
/--
Each refined triangle is an occurrence of one boundary holon.  Its incoming face is the weighted
source triangle, its outgoing face retains both the weighted affine-label triangle and the lateral
current, and its received current is the weighted prism.  No face cancellation is built into the
object; it follows from the local prism boundary law and, globally, from the generic holon theorem.
-/
def trianglePrismHolon
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    Soma.Holonics.BoundaryHolon (SphereChain 2) (SphereChain 3) where
  Occurrence := RefinedTriangleCell chain family.scale
  source cell := refinedTriangleCoefficient cell •
    simplexGenerator
      (homotopyEndSimplex (family.carrier cell).affineSphereHomotopy 0)
  target cell :=
    refinedTriangleCoefficient cell •
        simplexGenerator
          (homotopyEndSimplex (family.carrier cell).affineSphereHomotopy 1) +
      refinedTriangleCoefficient cell •
        triangleHomotopyLateralBoundary (family.carrier cell).affineSphereHomotopy
  receive cell := refinedTriangleCoefficient cell •
    triangleHomotopyPrism (family.carrier cell).affineSphereHomotopy
  boundary := (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom
  returnsBoundary := by
    intro cell
    change (SphereSingularChainComplex.d 3 2).hom
        (refinedTriangleCoefficient cell •
          triangleHomotopyPrism (family.carrier cell).affineSphereHomotopy) = _
    rw [map_smul, boundary_triangleHomotopyPrism]
    module

instance trianglePrismHolon_fintype
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    Fintype (trianglePrismHolon family).Occurrence := by
  change Fintype (RefinedTriangleCell chain family.scale)
  infer_instance

/-- The holon's complete received current is definitionally the assembled prism current. -/
theorem trianglePrismHolon_totalCurrent
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    (trianglePrismHolon family).totalCurrent = refinedPrismCurrent family := rfl

/-- The holon's complete incoming face is definitionally the retained lower current. -/
theorem trianglePrismHolon_totalSource
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    (trianglePrismHolon family).totalSource = refinedPrismLowerCurrent family := rfl

/-- The complete outgoing face retains both the upper and lateral receiver currents. -/
theorem trianglePrismHolon_totalTarget
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    (trianglePrismHolon family).totalTarget =
      refinedPrismUpperCurrent family + refinedPrismLateralCurrent family := by
  unfold Soma.Holonics.BoundaryHolon.totalTarget trianglePrismHolon
  rw [Finset.sum_add_distrib]
  rfl

/--
The generic boundary-holon local-to-global theorem reconstructs the full common-star prism law.
This is the same exact output as `boundary_refinedPrismCurrent`, now derived through the elementary
holon interface rather than by a construction-specific summation proof.
-/
theorem trianglePrismHolon_returns_globalBoundary
    {chain : SphereChain 2}
    {lebesgue :
      Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.d 3 2 (refinedPrismCurrent family) =
      refinedPrismUpperCurrent family - refinedPrismLowerCurrent family +
        refinedPrismLateralCurrent family := by
  have returned :=
    Soma.Holonics.BoundaryHolon.boundary_totalCurrent (trianglePrismHolon family)
  rw [trianglePrismHolon_totalCurrent,
    trianglePrismHolon_totalSource,
    trianglePrismHolon_totalTarget] at returned
  change SphereSingularChainComplex.d 3 2 (refinedPrismCurrent family) = _ at returned
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using returned

#print axioms prismCylinderMap_internal_first
#print axioms prismCylinderMap_internal_second
#print axioms triangleHomotopyLateralBoundary_eq_facePrisms
#print axioms triangleFacePrism_eq_edgeHomotopyPrism
#print axioms refinedAffineCarrierFamily_facePrism_congr
#print axioms sum_refinedTriangleCoefficient_simplexGenerator
#print axioms representedEdgePrism_refinedFace
#print axioms rawAffineLabelSimplex_face
#print axioms rawAffineLabelSimplex_boundary
#print axioms rawAffineLabelConstantTriangle_boundary
#print axioms rawAffineLabelFoldTriangle_boundary
#print axioms rawAffineLabelSimplexNormalizationDefect_boundary_zero
#print axioms rawAffineLabelEdge_face
#print axioms rawAffineLabelEdge_boundary
#print axioms refinedPrismUpperCurrent_eq_rawAffineLabelUpperCurrent
#print axioms refinedPrismUpperFaceCurrent_eq_pointCarryRefinedSource
#print axioms refinedPrismUpperFaceCurrent_eq_refinedCyclePointCurrent
#print axioms refinedPrismUpperFaceCurrent_boundary_zero
#print axioms refinedPrismUpperFaceCurrent_coordinates
#print axioms faceRealization_refinedPrismUpperFaceCurrent
#print axioms triangleHomotopyLateralBoundary_refinedCell
#print axioms refinedPrismLateralCurrent_eq_boundary
#print axioms refinedPrismLateralCurrent_eq_zero
#print axioms boundary_triangleHomotopyPrism
#print axioms homotopyEndSimplex_refinedCarrier_zero
#print axioms refinedPrismLowerCurrent_eq_refinement
#print axioms boundary_refinedPrismCurrent
#print axioms boundary_refinedPrismCurrent_of_cycle
#print axioms trianglePrismHolon
#print axioms trianglePrismHolon_totalCurrent
#print axioms trianglePrismHolon_totalTarget
#print axioms trianglePrismHolon_returns_globalBoundary

end Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism
