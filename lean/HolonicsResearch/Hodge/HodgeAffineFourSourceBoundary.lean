import HolonicsResearch.Hodge.HodgeAffineDegreeThreeReception

/-!
# The actual affine degree-four source returns its refined exterior.

This is one source owner of the canonical affine complex. Existing declarations
keep their namespace; the canonical entry imports the complete source family.
-/

noncomputable section

namespace Holonics.Hodge.HodgeBarycentricAffineSourceComplex

open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeStellarSubdivision
open Holonics.Hodge.HodgeStellarSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricEdgeSubdivision
open Holonics.Hodge.HodgeBarycentricTriangleSubdivision
open Holonics.Hodge.HodgeBarycentricSubdivisionHomotopy
open Holonics.Hodge.HodgeBarycentricDegreeTwoFilling

open CategoryTheory

open Holonics.Hodge.HodgeTetrahedralStellarSubdivision
open Holonics.Hodge.HodgeBarycentricTetrahedron

/-! ### Complete face pushforward before affine cone reception

The degree-three proofs above are preserved byte for byte.  These dimension-independent
source equations are consumed by the prepared degree-four continuation below; the sampled
continuous-base exterior obstruction still applies.  No filling hypothesis is added.
-/

theorem sourceSimplexFace_coordinate {degree : ℕ}
    (face : Fin (degree + 2)) (point : stdSimplex ℝ (Fin (degree + 1)))
    (index : Fin (degree + 2)) :
    simplexFaceMap (degree := degree) face point index =
      ∑ source : Fin (degree + 1),
        if face.succAbove source = index then point source else 0 := by
  change FunOnFinite.linearMap ℝ ℝ face.succAbove point index = _
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]

theorem sourceSimplexFace_vertex {degree : ℕ}
    (face : Fin (degree + 2)) (vertex : Fin (degree + 1)) :
    simplexFaceMap (degree := degree) face (stdSimplex.vertex vertex) =
      stdSimplex.vertex (face.succAbove vertex) := by
  change stdSimplex.map (SimplexCategory.δ face).toOrderHom
    (stdSimplex.vertex vertex) = stdSimplex.vertex (face.succAbove vertex)
  rw [stdSimplex.map_vertex]
  rfl

/-- The complete weighted source population is carried through the face injection. -/
theorem sourceSimplexFace_weighted_sum {degree : ℕ}
    (face : Fin (degree + 2)) (point : stdSimplex ℝ (Fin (degree + 1)))
    (weights : Fin (degree + 2) → ℝ) :
    (∑ index : Fin (degree + 2),
      simplexFaceMap (degree := degree) face point index * weights index) =
      ∑ vertex : Fin (degree + 1), point vertex * weights (face.succAbove vertex) := by
  simp_rw [sourceSimplexFace_coordinate]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertex _
  exact Finset.sum_ite_eq_of_mem Finset.univ (face.succAbove vertex)
    (fun index => point vertex * weights index) (Finset.mem_univ _)

/-- One face insertion commutes with the complete affine producing sum. -/
theorem sourceSimplexFace_affine_sum {degree count : ℕ}
    (face : Fin (degree + 2)) (point : stdSimplex ℝ (Fin (degree + 1)))
    (weights : Fin count → ℝ) (vertices : Fin count → stdSimplex ℝ (Fin (degree + 1)))
    (hpoint : ∀ coordinate, point coordinate =
      ∑ vertex : Fin count, weights vertex * vertices vertex coordinate)
    (coordinate : Fin (degree + 2)) :
    simplexFaceMap (degree := degree) face point coordinate =
      ∑ vertex : Fin count,
        weights vertex * simplexFaceMap (degree := degree) face (vertices vertex) coordinate := by
  rw [sourceSimplexFace_coordinate]
  simp_rw [hpoint, sourceSimplexFace_coordinate]
  calc
    (∑ source : Fin (degree + 1),
        if face.succAbove source = coordinate then
          ∑ vertex : Fin count, weights vertex * vertices vertex source else 0) =
        ∑ source : Fin (degree + 1), ∑ vertex : Fin count,
          if face.succAbove source = coordinate then weights vertex * vertices vertex source else 0 := by
      apply Finset.sum_congr rfl
      intro source _
      split_ifs <;> simp
    _ = ∑ vertex : Fin count, ∑ source : Fin (degree + 1),
          if face.succAbove source = coordinate then weights vertex * vertices vertex source else 0 :=
      Finset.sum_comm
    _ = ∑ vertex : Fin count, weights vertex *
        ∑ source : Fin (degree + 1),
          if face.succAbove source = coordinate then vertices vertex source else 0 := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]

/-- A successor omission retains the apex and transports every other producing vertex. -/
theorem sourceConeVertices_face_succ {degree target : ℕ}
    (apex : stdSimplex ℝ (Fin target))
    (base : C(stdSimplex ℝ (Fin (degree + 2)), stdSimplex ℝ (Fin target)))
    (omitted : Fin (degree + 2)) (vertex : Fin (degree + 2)) :
    (Fin.cases apex (fun source : Fin (degree + 2) => base (stdSimplex.vertex source)) :
        Fin (degree + 3) → stdSimplex ℝ (Fin target)) (omitted.succ.succAbove vertex) =
      (Fin.cases apex (fun source : Fin (degree + 1) =>
        (base.comp (simplexFaceMap (degree := degree) omitted)) (stdSimplex.vertex source)) :
        Fin (degree + 2) → stdSimplex ℝ (Fin target)) vertex := by
  refine Fin.cases ?_ (fun source => ?_) vertex
  · rw [Fin.succ_succAbove_zero]
    rfl
  · rw [Fin.succ_succAbove_succ]
    dsimp only
    simp only [Fin.cases_succ, ContinuousMap.comp_apply, sourceSimplexFace_vertex]

theorem sourceSumFive {M : Type*} [AddCommMonoid M] (f : Fin 5 → M) :
    ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have h0 : (0 : Fin 4).succ = (1 : Fin 5) := by decide
  have h1 : (1 : Fin 4).succ = (2 : Fin 5) := by decide
  have h2 : (2 : Fin 4).succ = (3 : Fin 5) := by decide
  have h3 : (3 : Fin 4).succ = (4 : Fin 5) := by decide
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  simp only [h0, h1, h2, h3, add_assoc, add_left_comm, add_comm]

/-! ## The actual geometric degree-four refinement

This continuation belongs to the same affine source owner.  It cones the complete refined
exterior at the equal-weight four-simplex barycentre.  It requires the prepared free degree-three
source square, not a hypothetical sphere filling.  Its 120 source cells have a complete boundary
return; no mesh-shrinkage or SphereH4 admission follows from the construction alone.
-/

def fourSimplexBarycenter : stdSimplex ℝ (Fin 5) :=
  ⟨fun _ => (5 : ℝ)⁻¹, by
    constructor
    · intro coordinate
      positivity
    · rw [Fin.sum_univ_succ, Fin.sum_univ_four]
      norm_num⟩

def tetrahedronToFourSimplexAffineMap (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) :
    C(Tetrahedron, stdSimplex ℝ (Fin 5)) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 4, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 5, ∑ vertex : Fin 4, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 4, ∑ coordinate : Fin 5,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 4, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

@[simp] theorem tetrahedronToFourSimplexAffineMap_apply
    (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) (point : Tetrahedron) (coordinate : Fin 5) :
    tetrahedronToFourSimplexAffineMap vertices point coordinate =
      ∑ vertex : Fin 4, point vertex * vertices vertex coordinate := rfl

@[simp] theorem tetrahedronToFourSimplexAffineMap_vertex
    (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) (vertex : Fin 4) :
    tetrahedronToFourSimplexAffineMap vertices (stdSimplex.vertex vertex) = vertices vertex := by
  apply stdSimplex.ext
  funext coordinate
  rw [tetrahedronToFourSimplexAffineMap_apply, Fin.sum_univ_four]
  fin_cases vertex <;> simp

def fourSimplexAffineMap (vertices : Fin 5 → stdSimplex ℝ (Fin 5)) :
    C(stdSimplex ℝ (Fin 5), stdSimplex ℝ (Fin 5)) where
  toFun point := ⟨fun coordinate => ∑ vertex : Fin 5, point vertex * vertices vertex coordinate, by
    constructor
    · intro coordinate
      exact Finset.sum_nonneg fun vertex _ =>
        mul_nonneg (stdSimplex.zero_le point vertex) (stdSimplex.zero_le (vertices vertex) coordinate)
    · calc
        ∑ coordinate : Fin 5, ∑ vertex : Fin 5, point vertex * vertices vertex coordinate =
            ∑ vertex : Fin 5, ∑ coordinate : Fin 5,
              point vertex * vertices vertex coordinate := Finset.sum_comm
        _ = ∑ vertex : Fin 5, point vertex * 1 := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
        _ = 1 := by simp [stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun coordinate =>
      continuous_finset_sum _ fun vertex _ =>
        ((continuous_apply vertex).comp continuous_subtype_val).mul continuous_const

def fourSourceConeMap (base : C(Tetrahedron, stdSimplex ℝ (Fin 5))) :
    C(stdSimplex ℝ (Fin 5), stdSimplex ℝ (Fin 5)) :=
  fourSimplexAffineMap
    (Fin.cases fourSimplexBarycenter fun vertex : Fin 4 => base (stdSimplex.vertex vertex))

def fourSourceTriangleConeMap (base : C(Triangle, stdSimplex ℝ (Fin 5))) :
    C(Tetrahedron, stdSimplex ℝ (Fin 5)) :=
  tetrahedronToFourSimplexAffineMap
    (Fin.cases fourSimplexBarycenter fun vertex : Fin 3 => base (stdSimplex.vertex vertex))

theorem fourSourceConeMap_face_zero_affine (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) :
    (fourSourceConeMap (tetrahedronToFourSimplexAffineMap vertices)).comp
        (simplexFaceMap (degree := 3) 0) = tetrahedronToFourSimplexAffineMap vertices := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 5, simplexFaceMap (degree := 3) 0 point vertex *
      (Fin.cases fourSimplexBarycenter (fun vertex : Fin 4 =>
        tetrahedronToFourSimplexAffineMap vertices (stdSimplex.vertex vertex)) :
        Fin 5 → stdSimplex ℝ (Fin 5)) vertex coordinate) =
    ∑ vertex : Fin 4, point vertex * vertices vertex coordinate
  rw [sourceSimplexFace_weighted_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [Fin.zero_succAbove]
  dsimp only
  simp only [Fin.cases_succ, tetrahedronToFourSimplexAffineMap_vertex]

theorem fourSourceConeMap_face_succ (base : C(Tetrahedron, stdSimplex ℝ (Fin 5)))
    (omitted : Fin 4) :
    (fourSourceConeMap base).comp (simplexFaceMap (degree := 3) omitted.succ) =
      fourSourceTriangleConeMap (base.comp (simplexFaceMap (degree := 2) omitted)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change (∑ vertex : Fin 5, simplexFaceMap (degree := 3) omitted.succ point vertex *
      (Fin.cases fourSimplexBarycenter (fun vertex : Fin 4 => base (stdSimplex.vertex vertex)) :
        Fin 5 → stdSimplex ℝ (Fin 5)) vertex coordinate) =
    ∑ vertex : Fin 4, point vertex *
      (Fin.cases fourSimplexBarycenter (fun vertex : Fin 3 =>
        (base.comp (simplexFaceMap (degree := 2) omitted)) (stdSimplex.vertex vertex)) :
        Fin 4 → stdSimplex ℝ (Fin 5)) vertex coordinate
  rw [sourceSimplexFace_weighted_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  exact congrArg (fun target : stdSimplex ℝ (Fin 5) => point vertex * target coordinate)
    (sourceConeVertices_face_succ fourSimplexBarycenter base omitted vertex)

abbrev SourceFourCellChain := C(stdSimplex ℝ (Fin 5), stdSimplex ℝ (Fin 5)) →₀ ℚ
abbrev SourceFourFaceChain := C(Tetrahedron, stdSimplex ℝ (Fin 5)) →₀ ℚ
abbrev SourceFourTriangleChain := C(Triangle, stdSimplex ℝ (Fin 5)) →₀ ℚ

def sourceFourBoundary : SourceFourCellChain →ₗ[ℚ] SourceFourFaceChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 5, (-1 : ℚ) ^ (face : ℕ) •
      Finsupp.single (base.comp (simplexFaceMap (degree := 3) face)) 1

def sourceFourFaceBoundary : SourceFourFaceChain →ₗ[ℚ] SourceFourTriangleChain :=
  Finsupp.linearCombination ℚ fun base =>
    ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
      Finsupp.single (base.comp (simplexFaceMap (degree := 2) face)) 1

def sourceFourCone : SourceFourFaceChain →ₗ[ℚ] SourceFourCellChain :=
  Finsupp.linearCombination ℚ fun base => Finsupp.single (fourSourceConeMap base) 1

def sourceFourTriangleCone : SourceFourTriangleChain →ₗ[ℚ] SourceFourFaceChain :=
  Finsupp.linearCombination ℚ fun base => Finsupp.single (fourSourceTriangleConeMap base) 1

def sourceFourFaceTransport (outerFace : Fin 5) : SourceTetrahedronChain →ₗ[ℚ] SourceFourFaceChain :=
  Finsupp.linearCombination ℚ fun base =>
    Finsupp.single ((simplexFaceMap (degree := 3) outerFace).comp base) 1

def sourceFourTriangleTransport (outerFace : Fin 5) :
    SourceTetrahedronFaceChain →ₗ[ℚ] SourceFourTriangleChain :=
  Finsupp.linearCombination ℚ fun base =>
    Finsupp.single ((simplexFaceMap (degree := 3) outerFace).comp base) 1

/-- The degree-three free square is consumed before any sphere receiver is applied. -/
theorem sourceFourFaceBoundary_faceTransport (outerFace : Fin 5) (current : SourceTetrahedronChain) :
    sourceFourFaceBoundary (sourceFourFaceTransport outerFace current) =
      sourceFourTriangleTransport outerFace (sourceTetrahedronBoundary current) := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp only [map_add, hleft, hright]
  | single base coefficient =>
      simp [sourceFourFaceBoundary, sourceFourFaceTransport, sourceFourTriangleTransport,
        sourceTetrahedronBoundary_single, sourceTetrahedronFaceGenerator, ContinuousMap.comp_assoc]

def sourceFourDoubleFace (outerFace : Fin 5) (innerFace : Fin 4) :
    C(Triangle, stdSimplex ℝ (Fin 5)) :=
  (simplexFaceMap (degree := 3) outerFace).comp (simplexFaceMap (degree := 2) innerFace)

theorem sourceFourDoubleFace_eq_of_omission
    (leftOuter rightOuter : Fin 5) (leftInner rightInner : Fin 4)
    (homission : leftOuter.succAbove ∘ leftInner.succAbove =
      rightOuter.succAbove ∘ rightInner.succAbove) :
    sourceFourDoubleFace leftOuter leftInner = sourceFourDoubleFace rightOuter rightInner := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map (SimplexCategory.δ leftOuter).toOrderHom
      (stdSimplex.map (SimplexCategory.δ leftInner).toOrderHom point) =
    stdSimplex.map (SimplexCategory.δ rightOuter).toOrderHom
      (stdSimplex.map (SimplexCategory.δ rightInner).toOrderHom point)
  simp only [SimplexCategory.δ]
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hmap :
      (SimplexCategory.Hom.toOrderHom
        (SimplexCategory.mkHom leftOuter.succAboveOrderEmb.toOrderHom)) ∘
        (SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom leftInner.succAboveOrderEmb.toOrderHom)) =
      (SimplexCategory.Hom.toOrderHom
        (SimplexCategory.mkHom rightOuter.succAboveOrderEmb.toOrderHom)) ∘
        (SimplexCategory.Hom.toOrderHom
          (SimplexCategory.mkHom rightInner.succAboveOrderEmb.toOrderHom)) := by
    funext vertex
    have hvertex := congrFun homission vertex
    simpa only [Function.comp_apply, SimplexCategory.mkHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
      Fin.succAboveOrderEmb_apply] using hvertex
  rw [hmap]

/-! The ten omission pairs are retained explicitly, with no orientation quotient. -/

theorem sourceFourDoubleFace_01 : sourceFourDoubleFace 0 0 = sourceFourDoubleFace 1 0 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_02 : sourceFourDoubleFace 0 1 = sourceFourDoubleFace 2 0 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_03 : sourceFourDoubleFace 0 2 = sourceFourDoubleFace 3 0 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_04 : sourceFourDoubleFace 0 3 = sourceFourDoubleFace 4 0 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_12 : sourceFourDoubleFace 1 1 = sourceFourDoubleFace 2 1 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_13 : sourceFourDoubleFace 1 2 = sourceFourDoubleFace 3 1 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_14 : sourceFourDoubleFace 1 3 = sourceFourDoubleFace 4 1 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_23 : sourceFourDoubleFace 2 2 = sourceFourDoubleFace 3 2 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_24 : sourceFourDoubleFace 2 3 = sourceFourDoubleFace 4 2 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl
theorem sourceFourDoubleFace_34 : sourceFourDoubleFace 3 3 = sourceFourDoubleFace 4 3 := by
  apply sourceFourDoubleFace_eq_of_omission
  funext vertex
  fin_cases vertex <;> rfl

def sourceFourExteriorSubdivision : SourceFourFaceChain :=
  ∑ outerFace : Fin 5, (-1 : ℚ) ^ (outerFace : ℕ) •
    sourceFourFaceTransport outerFace sourceTetrahedronSubdivision

theorem sourceFourTriangleTransport_faceTriangle (outerFace : Fin 5) (innerFace : Fin 4)
    (base : C(Triangle, Triangle)) :
    sourceFourTriangleTransport outerFace
        (sourceFaceTriangleTransport innerFace (sourceTriangleGenerator base)) =
      Finsupp.single ((sourceFourDoubleFace outerFace innerFace).comp base) 1 := by
  simp [sourceFourTriangleTransport, sourceFaceTriangleTransport, sourceTriangleGenerator,
    sourceTetrahedronFaceGenerator, sourceFourDoubleFace, ContinuousMap.comp_assoc]

/-- The coherently refined exterior is closed as a free source current. -/
theorem sourceFourFaceBoundary_exteriorSubdivision :
    sourceFourFaceBoundary sourceFourExteriorSubdivision = 0 := by
  classical
  simp only [sourceFourExteriorSubdivision, map_sum, map_smul,
    sourceFourFaceBoundary_faceTransport, sourceTetrahedronBoundary_subdivision,
    map_sum, map_smul, sourceTriangleSubdivision, sourceFourTriangleTransport_faceTriangle]
  rw [sourceSumFive]
  repeat rw [Fin.sum_univ_four]
  repeat rw [Fin.sum_univ_three]
  repeat rw [Fin.sum_univ_two]
  simp_rw [sourceFourDoubleFace_01, sourceFourDoubleFace_02, sourceFourDoubleFace_03,
    sourceFourDoubleFace_04, sourceFourDoubleFace_12, sourceFourDoubleFace_13,
    sourceFourDoubleFace_14, sourceFourDoubleFace_23, sourceFourDoubleFace_24,
    sourceFourDoubleFace_34]
  norm_num
  module

theorem sourceFourBoundary_cone_affine (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) :
    sourceFourBoundary
        (sourceFourCone (Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1)) =
      Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1 -
        sourceFourTriangleCone
          (sourceFourFaceBoundary (Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1)) := by
  classical
  simp only [sourceFourCone, sourceFourBoundary, sourceFourFaceBoundary,
    Finsupp.linearCombination_single, one_smul]
  rw [Fin.sum_univ_succ, fourSourceConeMap_face_zero_affine]
  simp_rw [fourSourceConeMap_face_succ]
  simp only [map_sum, map_smul, sourceFourTriangleCone,
    Finsupp.linearCombination_single, one_smul]
  repeat rw [Fin.sum_univ_four]
  norm_num
  module

theorem liftedTetrahedronAffineMap_eq_fourAffine (outerFace : Fin 5) (vertices : Fin 4 → Tetrahedron) :
    (simplexFaceMap (degree := 3) outerFace).comp (tetrahedronAffineMap vertices) =
      tetrahedronToFourSimplexAffineMap
        (fun vertex => simplexFaceMap (degree := 3) outerFace (vertices vertex)) := by
  apply ContinuousMap.ext
  intro point
  apply stdSimplex.ext
  funext coordinate
  change simplexFaceMap (degree := 3) outerFace (tetrahedronAffineMap vertices point) coordinate =
    ∑ vertex : Fin 4, point vertex * simplexFaceMap (degree := 3) outerFace (vertices vertex) coordinate
  exact sourceSimplexFace_affine_sum outerFace (tetrahedronAffineMap vertices point)
    (fun vertex => point vertex) vertices
    (fun _ => tetrahedronAffineMap_apply vertices point _) coordinate

def sourceFourConeReturnDefect : SourceFourFaceChain →ₗ[ℚ] SourceFourFaceChain :=
  sourceFourBoundary.comp sourceFourCone - LinearMap.id +
    sourceFourTriangleCone.comp sourceFourFaceBoundary

theorem sourceFourConeReturnDefect_affine (vertices : Fin 4 → stdSimplex ℝ (Fin 5)) :
    sourceFourConeReturnDefect (Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1) = 0 := by
  change sourceFourBoundary
      (sourceFourCone (Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1)) -
    Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1 +
      sourceFourTriangleCone
        (sourceFourFaceBoundary (Finsupp.single (tetrahedronToFourSimplexAffineMap vertices) 1)) = 0
  rw [sourceFourBoundary_cone_affine]
  module

theorem sourceFourConeReturnDefect_exteriorSubdivision :
    sourceFourConeReturnDefect sourceFourExteriorSubdivision = 0 := by
  classical
  simp only [sourceFourExteriorSubdivision, sourceTetrahedronSubdivision,
    map_sum, map_smul, sourceTetrahedronGenerator, sourceFourFaceTransport,
    Finsupp.linearCombination_single, one_smul, barycentricTetrahedronMap]
  simp_rw [liftedTetrahedronAffineMap_eq_fourAffine]
  simp only [sourceFourConeReturnDefect_affine, smul_zero, Finset.sum_const_zero]

/-- The actual 5·24 = 120 geometric cells, not the recursive algebraic degree-four surrogate. -/
def sourceFourSubdivision : SourceFourCellChain := sourceFourCone sourceFourExteriorSubdivision

theorem sourceFourBoundary_subdivision :
    sourceFourBoundary sourceFourSubdivision = sourceFourExteriorSubdivision := by
  have hreturn := sourceFourConeReturnDefect_exteriorSubdivision
  change sourceFourBoundary (sourceFourCone sourceFourExteriorSubdivision) -
    sourceFourExteriorSubdivision +
      sourceFourTriangleCone (sourceFourFaceBoundary sourceFourExteriorSubdivision) = 0 at hreturn
  rw [sourceFourFaceBoundary_exteriorSubdivision, map_zero, add_zero] at hreturn
  exact sub_eq_zero.mp hreturn


end Holonics.Hodge.HodgeBarycentricAffineSourceComplex

#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.fourSourceConeMap_face_zero_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.fourSourceConeMap_face_succ
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourFaceBoundary_faceTransport
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourFaceBoundary_exteriorSubdivision
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourBoundary_cone_affine
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourConeReturnDefect_exteriorSubdivision
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceFourBoundary_subdivision
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceSimplexFace_coordinate
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceSimplexFace_vertex
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceSimplexFace_weighted_sum
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceSimplexFace_affine_sum
#print axioms Holonics.Hodge.HodgeBarycentricAffineSourceComplex.sourceConeVertices_face_succ
