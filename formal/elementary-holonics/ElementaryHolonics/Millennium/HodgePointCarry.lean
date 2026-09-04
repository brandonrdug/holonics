import ElementaryHolonics.Millennium.HodgeRadialSpernerCarry
import ElementaryHolonics.Millennium.HodgeBarycentricChainSupport

/-!
# Point-natural tetrahedral current on the sphere

A label belongs to an actual sphere point, not to a cell-local copy of that point.  Therefore
every shared vertex has one label before any chain is assembled.  Pulling this label through the
vertices of a singular simplex commutes with every simplicial face exactly.  In degrees zero, one,
and two, the resulting finite tetrahedral current consequently commutes with boundary without any
global degree-three admissibility hypothesis.

The Lebesgue-star label constructed for the finite refinement is an instance of this carrier: the
centre of its positive ball lies in the selected open star.  Degree-three admissibility remains a
local theorem about sufficiently small tetrahedra and is deliberately not stored here.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact singular-simplex realization and finite
tetrahedral incidence laws.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgePointCarry

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision
open Soma.Holonics.Millennium.HodgeRadialSpernerCarry
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedronCoverSmallness

/-- [definition] One globally shared tetrahedral-star label on every actual sphere point. -/
structure StarPointLabeling where
  label : HodgeTwoSphereFundamentalCycle.TwoSphere → TetraVertex
  carried : ∀ point, point ∈ vertexStar (label point)

/-- [proved-derived; formal-checked] A positive Lebesgue-star aperture supplies a point-natural
label by evaluating its retained star choice at the point itself. -/
def StarLebesgueLabel.toStarPointLabeling (lebesgue : StarLebesgueLabel) :
    StarPointLabeling where
  label := lebesgue.label
  carried point := by
    apply lebesgue.ball_carried point
    simpa [Metric.mem_ball] using lebesgue.radiusPositive

/-- [definition] The actual sphere point at one addressed vertex of a singular simplex. -/
def simplexVertexPoint {degree : ℕ} (simplex : SphereSingularSimplex degree)
    (vertex : Fin (degree + 1)) : HodgeTwoSphereFundamentalCycle.TwoSphere :=
  TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk degree)) simplex (stdSimplex.vertex vertex)

/-- [proved-derived; formal-checked] A face map sends an addressed standard-simplex vertex to
the corresponding retained vertex of the parent simplex. -/
theorem simplexFaceMap_vertex {degree : ℕ} (face : Fin (degree + 2))
    (vertex : Fin (degree + 1)) :
    simplexFaceMap face (stdSimplex.vertex vertex) =
      stdSimplex.vertex (face.succAbove vertex) := by
  have vertexLaw :
      (SimplexCategory.δ face).toOrderHom vertex = face.succAbove vertex := rfl
  change stdSimplex.map (SimplexCategory.δ face).toOrderHom
      (stdSimplex.vertex vertex) = stdSimplex.vertex (face.succAbove vertex)
  rw [stdSimplex.map_vertex, vertexLaw]

/-- [proved-derived; formal-checked] Vertex occurrences are literally shared across the source
face operation. -/
theorem simplexVertexPoint_face {degree : ℕ}
    (simplex : SphereSingularSimplex (degree + 1))
    (face : Fin (degree + 2)) (vertex : Fin (degree + 1)) :
    simplexVertexPoint (simplexFace face simplex) vertex =
      simplexVertexPoint simplex (face.succAbove vertex) := by
  rw [simplexVertexPoint, simplexFace_realization]
  change
    (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk (degree + 1))) simplex)
        (simplexFaceMap face (stdSimplex.vertex vertex)) =
      simplexVertexPoint simplex (face.succAbove vertex)
  rw [simplexFaceMap_vertex]
  rfl

/-- [definition] Pull one global point label back to the ordered vertices of a singular simplex. -/
def simplexPointLabels (labeling : StarPointLabeling) {degree : ℕ}
    (simplex : SphereSingularSimplex degree) : Fin (degree + 1) → TetraVertex :=
  fun vertex => labeling.label (simplexVertexPoint simplex vertex)

/-- [proved-derived; formal-checked] Point-natural labels commute with every source face. -/
theorem simplexPointLabels_face (labeling : StarPointLabeling) {degree : ℕ}
    (simplex : SphereSingularSimplex (degree + 1)) (face : Fin (degree + 2)) :
    simplexPointLabels labeling (simplexFace face simplex) =
      simplexPointLabels labeling simplex ∘ face.succAbove := by
  funext vertex
  simp only [simplexPointLabels, Function.comp_apply, simplexVertexPoint_face]

/-- [definition] The finite tetrahedral current carried by the point labels of one singular
simplex. -/
def pointCarry (labeling : StarPointLabeling) (degree : ℕ)
    (simplex : SphereSingularSimplex degree) : tetrahedralChainComplex.X degree :=
  labelledSimplexCarry degree (simplexPointLabels labeling simplex)

/-- [proved-derived; formal-checked] In degrees below three, point carry commutes with the complete
alternating singular boundary.  This is the exact local constitutive law used by the relative
Sperner passage. -/
theorem pointCarry_boundary_low (labeling : StarPointLabeling) (degree : ℕ)
    (degreeBelowThree : degree < 2)
    (simplex : SphereSingularSimplex (degree + 1)) :
    tetrahedralChainComplex.d (degree + 1) degree
        (pointCarry labeling (degree + 1) simplex) =
      ∑ face : Fin (degree + 2), (-1 : ℚ) ^ (face : ℕ) •
        pointCarry labeling degree (simplexFace face simplex) := by
  rw [pointCarry, labelledSimplexCarry_boundary degree]
  · apply Finset.sum_congr rfl
    intro face _
    rw [pointCarry]
    rw [show
      faceLabels (simplexPointLabels labeling simplex) face =
        simplexPointLabels labeling (simplexFace face simplex) by
      simpa only [faceLabels] using
        (simplexPointLabels_face labeling simplex face).symm]
  · intro degreeThree
    omega

/-- [definition] Coproduct-linear extension of the point-natural current in one degree. -/
abbrev pointCarryMorphism (labeling : StarPointLabeling) (degree : ℕ) :
    SphereSingularChainComplex.X degree ⟶ tetrahedralChainComplex.X degree :=
  linearizeCarrier degree (pointCarry labeling degree)

@[simp]
theorem pointCarryMorphism_simplexGenerator (labeling : StarPointLabeling) (degree : ℕ)
    (simplex : SphereSingularSimplex degree) :
    pointCarryMorphism labeling degree (simplexGenerator simplex) =
      pointCarry labeling degree simplex := by
  exact linearizeCarrier_simplexGenerator degree (pointCarry labeling degree) simplex

/-- [proved-derived; formal-checked] The linear point current commutes with the singular boundary
through the complete `2 → 1 → 0` truncation. -/
theorem pointCarryMorphism_comm_low (labeling : StarPointLabeling) (degree : ℕ)
    (degreeBelowThree : degree < 2) :
    pointCarryMorphism labeling (degree + 1) ≫
        tetrahedralChainComplex.d (degree + 1) degree =
      SphereSingularChainComplex.d (degree + 1) degree ≫
        pointCarryMorphism labeling degree := by
  apply Sigma.hom_ext
  intro simplex
  change Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient) simplex ≫
        (Sigma.desc (fun source => carriedCoefficient (pointCarry labeling (degree + 1) source)) ≫
          tetrahedralChainComplex.d (degree + 1) degree) =
      Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient) simplex ≫
        (SphereSingularChainComplex.d (degree + 1) degree ≫
          Sigma.desc (fun source => carriedCoefficient (pointCarry labeling degree source)))
  rw [← Category.assoc, Sigma.ι_desc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change ℚ at coefficient
  simp only [ConcreteCategory.comp_apply]
  have hleft :
      (ConcreteCategory.hom
        (carriedCoefficient (pointCarry labeling (degree + 1) simplex))) coefficient =
        coefficient • pointCarry labeling (degree + 1) simplex := rfl
  rw [hleft]
  rw [sigmaInjection_eq_smul_simplexGenerator (degree + 1) simplex coefficient]
  change tetrahedralChainComplex.d (degree + 1) degree
      (coefficient • pointCarry labeling (degree + 1) simplex) =
    pointCarryMorphism labeling degree
      (SphereSingularChainComplex.d (degree + 1) degree
        (coefficient • simplexGenerator simplex))
  rw [map_smul, map_smul, boundary_simplexGenerator, map_smul, map_sum]
  simp only [map_smul]
  rw [pointCarry_boundary_low labeling degree degreeBelowThree simplex]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pointCarryMorphism_simplexGenerator]

/-- [proved-derived; formal-checked] The degree-two point current of the singular boundary of a
two-chain is its finite face boundary. -/
theorem pointCarryMorphism_boundary_two (labeling : StarPointLabeling)
    (chain : SphereChain 2) :
    pointCarryMorphism labeling 1
        (SphereSingularChainComplex.d 2 1 chain) =
      faceBoundary (pointCarryMorphism labeling 2 chain) := by
  have square := congrArg
    (fun morphism : SphereSingularChainComplex.X 2 ⟶ tetrahedralChainComplex.X 1 =>
      morphism chain)
    (pointCarryMorphism_comm_low labeling 1 (by omega))
  convert square.symm using 1 <;>
    simp [ConcreteCategory.comp_apply, tetrahedralChainComplex_d_one] <;> rfl

/-- [proved-derived; formal-checked] The point current of the singular boundary of a one-chain is
its finite vertex boundary. -/
theorem pointCarryMorphism_boundary_one (labeling : StarPointLabeling)
    (chain : SphereChain 1) :
    pointCarryMorphism labeling 0
        (SphereSingularChainComplex.d 1 0 chain) =
      vertexBoundary (pointCarryMorphism labeling 1 chain) := by
  have square := congrArg
    (fun morphism : SphereSingularChainComplex.X 1 ⟶ tetrahedralChainComplex.X 0 =>
      morphism chain)
    (pointCarryMorphism_comm_low labeling 0 (by omega))
  convert square.symm using 1 <;>
    simp [ConcreteCategory.comp_apply, tetrahedralChainComplex_d_zero] <;> rfl

/-- [proved-derived; formal-checked] An admissible labelled singular tetrahedron returns zero
point current on its complete alternating boundary. -/
theorem pointCarry_boundary_three_eq_zero (labeling : StarPointLabeling)
    (simplex : SphereSingularSimplex 3)
    (admissible : FourLabelsAdmissible
      (simplexPointLabels labeling simplex 0)
      (simplexPointLabels labeling simplex 1)
      (simplexPointLabels labeling simplex 2)
      (simplexPointLabels labeling simplex 3)) :
    pointCarryMorphism labeling 2
        (SphereSingularChainComplex.d 3 2 (simplexGenerator simplex)) = 0 := by
  rw [boundary_simplexGenerator, map_sum]
  simp only [map_smul, pointCarryMorphism_simplexGenerator, pointCarry]
  have boundaryLaw := labelledSimplexCarry_boundary 2
    (simplexPointLabels labeling simplex) (fun _ => admissible)
  rw [tetrahedralChainComplex_d_three_two] at boundaryLaw
  convert boundaryLaw.symm using 1 <;>
    simp [map_sum, map_smul, map_zero, faceLabels,
      simplexPointLabels_face labeling simplex, labelledSimplexCarry]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (ConcreteCategory.hom
      (Sigma.ι (fun _ : SphereSingularSimplex 2 => rationalCoefficient)
        (simplexFace i simplex))) (1 : ℚ) =
      simplexGenerator (simplexFace i simplex) by rfl]
  rw [pointCarryMorphism_simplexGenerator]
  change (-1 : ℚ) ^ (i : ℕ) •
      labelledSimplexCarry 2 (simplexPointLabels labeling (simplexFace i simplex)) =
    (-1 : ℚ) ^ (i : ℕ) •
      orientedFaceCarry (simplexPointLabels labeling simplex (i.succAbove 0))
        (simplexPointLabels labeling simplex (i.succAbove 1))
    (simplexPointLabels labeling simplex (i.succAbove 2))
  rw [simplexPointLabels_face labeling simplex i]
  rw [labelledSimplexCarry_two]
  simp only [Function.comp_apply]

/-- [proved-derived; formal-checked] If one singular tetrahedron image lies in a radius-third
Lebesgue ball, its four point labels have an actual common star point and hence are admissible.
The two travelled radius-third legs remain strictly below the original radius. -/
theorem fourLabelsAdmissible_of_range_subset_ball
    (lebesgue : StarLebesgueLabel) (simplex : SphereSingularSimplex 3)
    (center : HodgeTwoSphereFundamentalCycle.TwoSphere)
    (small : Set.range
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 3)) simplex) ⊆
          (Metric.ball center (lebesgue.radius / 3) :
            Set HodgeTwoSphereFundamentalCycle.TwoSphere)) :
    FourLabelsAdmissible
      (simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) simplex 0)
      (simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) simplex 1)
      (simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) simplex 2)
      (simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) simplex 3) := by
  let common : HodgeTwoSphereFundamentalCycle.TwoSphere :=
    TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 3)) simplex tetrahedronBarycenter
  apply fourLabelsAdmissible_of_commonStarPoint
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) simplex) common
  intro index
  apply lebesgue.ball_carried (simplexVertexPoint simplex index)
  rw [Metric.mem_ball]
  have commonInRange : common ∈ Set.range
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 3)) simplex) :=
    ⟨tetrahedronBarycenter, rfl⟩
  have centerPoint := small commonInRange
  have centerVertex := small ⟨stdSimplex.vertex index, rfl⟩
  change common ∈ Metric.ball center (lebesgue.radius / 3) at centerPoint
  rw [Metric.mem_ball] at centerPoint
  change simplexVertexPoint simplex index ∈
    Metric.ball center (lebesgue.radius / 3) at centerVertex
  rw [Metric.mem_ball] at centerVertex
  have centerToCommon : dist center common < lebesgue.radius / 3 := by
    simpa only [dist_comm] using centerPoint
  have centerToVertex :
      dist center (simplexVertexPoint simplex index) < lebesgue.radius / 3 := by
    simpa only [dist_comm] using centerVertex
  calc
    dist common (simplexVertexPoint simplex index) ≤
      dist common center +
        dist center (simplexVertexPoint simplex index) := dist_triangle _ _ _
    _ < lebesgue.radius := by
      linarith [centerPoint, centerToVertex, lebesgue.radiusPositive]

/-- [uniform-scale-theorem; formal-checked] One exact barycentric depth places every addressed
descendant of every genuinely supported boundary tetrahedron inside a radius-third Lebesgue ball.
The occurrence and complete address word remain in the return. -/
theorem exists_scale_boundary_support_words_ball
    (boundaryWitness : SphereChain 3) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ, ∀ occurrence : ↑(sphereChainSupport 3 boundaryWitness),
      ∀ word : List BarycentricTetrahedronAddress,
        word.length = scale → ∃ center : HodgeTwoSphereFundamentalCycle.TwoSphere,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 3)) occurrence.1).comp
                (barycentricTetrahedronWordMap word)) ⊆
            (Metric.ball center (lebesgue.radius / 3) :
              Set HodgeTwoSphereFundamentalCycle.TwoSphere) := by
  have ballOpen : ∀ center : HodgeTwoSphereFundamentalCycle.TwoSphere,
      IsOpen (Metric.ball center (lebesgue.radius / 3)) :=
    fun _ => Metric.isOpen_ball
  have ballCover : Set.univ ⊆
      ⋃ center : HodgeTwoSphereFundamentalCycle.TwoSphere,
        Metric.ball center (lebesgue.radius / 3) := by
    intro point _
    rw [Set.mem_iUnion]
    refine ⟨point, ?_⟩
    rw [Metric.mem_ball, dist_self]
    linarith [lebesgue.radiusPositive]
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_finite_sphereTetrahedron_family_barycentric_descendants_subordinate
      (fun occurrence : ↑(sphereChainSupport 3 boundaryWitness) => occurrence.1)
      (fun center : HodgeTwoSphereFundamentalCycle.TwoSphere =>
        (Metric.ball center (lebesgue.radius / 3) :
          Set HodgeTwoSphereFundamentalCycle.TwoSphere))
      ballOpen ballCover
  exact ⟨scale, fun occurrence word wordLength =>
    scaleLaw occurrence word (by omega)⟩

/-- [definition] Every genuinely supported tetrahedral occurrence of a chain obeys the local
four-label nerve law. -/
def SupportAdmissible (labeling : StarPointLabeling) (chain : SphereChain 3) : Prop :=
  ∀ occurrence : ↑(sphereChainSupport 3 chain),
    FourLabelsAdmissible
      (simplexPointLabels labeling occurrence.1 0)
      (simplexPointLabels labeling occurrence.1 1)
      (simplexPointLabels labeling occurrence.1 2)
      (simplexPointLabels labeling occurrence.1 3)

/-- [proved-derived; formal-checked] Local admissibility on the genuine finite support forces the
point current of the complete singular boundary to vanish.  Coefficients and source occurrences
are reconstructed exactly before the local zero law is applied. -/
theorem pointCarry_boundary_chain_eq_zero_of_support_admissible
    (labeling : StarPointLabeling) (chain : SphereChain 3)
    (admissible : SupportAdmissible labeling chain) :
    pointCarryMorphism labeling 2
        (SphereSingularChainComplex.d 3 2 chain) = 0 := by
  classical
  rw [← sum_support_sphereChainCoefficient_simplexGenerator 3 chain]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro simplex simplexInSupport
  rw [map_smul, map_smul]
  rw [pointCarry_boundary_three_eq_zero labeling simplex]
  · exact smul_zero _
  · exact admissible ⟨simplex, simplexInSupport⟩

/-- [proved-derived; formal-checked] Every addressed simplex vertex is carried by the open star
selected at that exact sphere point. -/
theorem simplexVertexPoint_mem_labelStar (lebesgue : StarLebesgueLabel)
    {degree : ℕ} (simplex : SphereSingularSimplex degree)
    (index : Fin (degree + 1)) :
    simplexVertexPoint simplex index ∈
      vertexStar
        (simplexPointLabels
          (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
            lebesgue) simplex index) :=
  (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
    lebesgue).carried _

/-- [proved-derived; formal-checked] A vertex realized on one radial face cannot receive the
omitted tetrahedral label. -/
theorem pointLabel_ne_of_vertex_on_radialFace (lebesgue : StarLebesgueLabel)
    (face : Fin 4) (simplex : SphereSingularSimplex 2) (index : Fin 3)
    (source : Triangle)
    (realized : simplexVertexPoint simplex index = radialFace face source) :
    simplexPointLabels
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) simplex index ≠ face := by
  apply radial_carried_label_ne_opposite face _ source
  rw [← realized]
  exact simplexVertexPoint_mem_labelStar lebesgue simplex index

/-- [proved-derived; formal-checked] If all three vertices of a singular triangle are realized on
the radial face opposite `face`, its point current is supported only on that addressed finite
face. -/
theorem pointCarry_supported_on_radialFace (lebesgue : StarLebesgueLabel)
    (face : Fin 4) (simplex : SphereSingularSimplex 2)
    (onFace : ∀ index : Fin 3, ∃ source : Triangle,
      simplexVertexPoint simplex index = radialFace face source)
    (observed : Fin 4) (different : observed ≠ face) :
    pointCarry
        (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
          lebesgue) 2 simplex observed = 0 := by
  rcases onFace 0 with ⟨sourceZero, sourceZeroLaw⟩
  rcases onFace 1 with ⟨sourceOne, sourceOneLaw⟩
  rcases onFace 2 with ⟨sourceTwo, sourceTwoLaw⟩
  exact orientedFaceCarry_supported_on_face face
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) simplex 0)
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) simplex 1)
    (simplexPointLabels
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) simplex 2)
    (pointLabel_ne_of_vertex_on_radialFace lebesgue face simplex 0
      sourceZero sourceZeroLaw)
    (pointLabel_ne_of_vertex_on_radialFace lebesgue face simplex 1
      sourceOne sourceOneLaw)
    (pointLabel_ne_of_vertex_on_radialFace lebesgue face simplex 2
      sourceTwo sourceTwoLaw)
    observed different

section Audit

#print axioms StarLebesgueLabel.toStarPointLabeling
#print axioms simplexFaceMap_vertex
#print axioms simplexVertexPoint_face
#print axioms simplexPointLabels_face
#print axioms pointCarry_boundary_low
#print axioms pointCarryMorphism_comm_low
#print axioms pointCarryMorphism_boundary_two
#print axioms pointCarryMorphism_boundary_one
#print axioms pointCarry_boundary_three_eq_zero
#print axioms fourLabelsAdmissible_of_range_subset_ball
#print axioms exists_scale_boundary_support_words_ball
#print axioms pointCarry_boundary_chain_eq_zero_of_support_admissible
#print axioms pointCarry_supported_on_radialFace

end Audit

end Soma.Holonics.Millennium.HodgePointCarry
