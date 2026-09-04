import ElementaryHolonics.Millennium.HodgeTetrahedralStarContraction

/-!
# Face-natural affine carrier for common-star triangles

The local contraction becomes globally useful only when its target respects source faces.  For an
ordered low-degree label word, `stdSimplex.map` is the exact affine target: it transports source
barycentric coordinates to the tetrahedral vertices named by the labels, with repetitions retained.
Because at most three labels occur, one tetrahedral coordinate is absent and the map lands on the
boundary.  Its restriction to every source face is definitionally the affine map of the restricted
label word.

For a sphere triangle whose complete image lies in each of its three labelled stars, the straight
boundary segment from the exact sphere address to this affine label map retains the source zero
coordinate.  Radial return therefore gives a continuous homotopy from the source triangle to the
face-natural affine approximation.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the exact boundary homeomorphism and common-star
incidence law.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier

open Set Topology
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralBoundaryCoordinates
open Soma.Holonics.Millennium.HodgeTetrahedralBoundaryRadial

/-- [definition] The exact affine map presented by an ordered label word. -/
def lowLabelAffineMap (degree : ℕ) (labels : Fin (degree + 1) → TetraVertex) :
    C(stdSimplex ℝ (Fin (degree + 1)), Tetrahedron) where
  toFun := stdSimplex.map labels
  continuous_toFun := stdSimplex.continuous_map labels

/-- [proved-derived; formal-checked] A label word of degree at most two omits at least one of the
four tetrahedral vertices. -/
theorem exists_omitted_label (degree : ℕ) (belowThree : degree < 3)
    (labels : Fin (degree + 1) → TetraVertex) :
    ∃ omitted : TetraVertex, ∀ index, labels index ≠ omitted := by
  have notSurjective : ¬Function.Surjective labels := by
    intro surjective
    have cardBound := Fintype.card_le_of_surjective labels surjective
    simp only [Fintype.card_fin] at cardBound
    omega
  change ¬∀ omitted, ∃ index, labels index = omitted at notSurjective
  push_neg at notSurjective
  exact notSurjective

/-- [definition] The canonical omitted-vertex receiver for a three-label word.  The choice is
made from the finite existence theorem and carries no new geometric data. -/
def omittedLabel (labels : Fin 3 → TetraVertex) : TetraVertex :=
  Classical.choose (exists_omitted_label 2 (by omega) labels)

/-- [proved-derived; formal-checked] Every entry of a three-label word differs from its retained
omitted vertex. -/
theorem label_ne_omittedLabel (labels : Fin 3 → TetraVertex) (index : Fin 3) :
    labels index ≠ omittedLabel labels := by
  exact Classical.choose_spec (exists_omitted_label 2 (by omega) labels) index

/-- [definition] A lawful local apex for a three-label word. -/
def labelApex (labels : Fin 3 → TetraVertex) : TetraVertex := labels 0

/-- [proved-derived; formal-checked] The chosen local apex is distinct from the omitted vertex. -/
theorem labelApex_ne_omittedLabel (labels : Fin 3 → TetraVertex) :
    labelApex labels ≠ omittedLabel labels := by
  exact label_ne_omittedLabel labels 0

/-- [proved-derived; formal-checked] The affine label map has an addressed zero coordinate at every
source point. -/
theorem lowLabelAffineMap_has_zero (degree : ℕ) (belowThree : degree < 3)
    (labels : Fin (degree + 1) → TetraVertex)
    (point : stdSimplex ℝ (Fin (degree + 1))) :
    ∃ omitted : TetraVertex, lowLabelAffineMap degree labels point omitted = 0 := by
  obtain ⟨omitted, omittedLaw⟩ := exists_omitted_label degree belowThree labels
  refine ⟨omitted, ?_⟩
  change FunOnFinite.linearMap ℝ ℝ labels point omitted = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have filteredEmpty :
      Finset.univ.filter (fun index => labels index = omitted) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro index _
    exact omittedLaw index
  rw [filteredEmpty]
  simp

/-- [definition] The affine label map with its retained tetrahedral-boundary address. -/
def lowLabelBoundaryMap (degree : ℕ) (belowThree : degree < 3)
    (labels : Fin (degree + 1) → TetraVertex) :
    C(stdSimplex ℝ (Fin (degree + 1)), TetraBoundary) where
  toFun point :=
    ⟨lowLabelAffineMap degree labels point,
      lowLabelAffineMap_has_zero degree belowThree labels point⟩
  continuous_toFun := Continuous.subtype_mk (lowLabelAffineMap degree labels).continuous _

/-- [definition] Radial realization of the low-degree affine label word. -/
def lowLabelSphereMap (degree : ℕ) (belowThree : degree < 3)
    (labels : Fin (degree + 1) → TetraVertex) :
    C(stdSimplex ℝ (Fin (degree + 1)), TwoSphere) :=
  boundaryRadial.comp (lowLabelBoundaryMap degree belowThree labels)

/-! The canonical ordered-label subcase is an exact receiver return.  It is useful as a
normalization test because it contains no permutation or repeated-label quotient: the affine
label map is literally one radial face map. -/

/-- [proved-derived; formal-checked] The low-label sphere map with the ordered complement of an
omitted tetrahedral vertex is exactly the corresponding radial face map. -/
theorem lowLabelSphereMap_succAbove_eq_radialFace (face : Fin 4) :
    lowLabelSphereMap 2 (by omega) face.succAbove =
      HodgeTwoSphereFundamentalCycle.radialFace face := by
  apply ContinuousMap.ext
  intro point
  apply Subtype.ext
  change NormedSpace.normalize
      (boundaryCenteredVector
        ⟨lowLabelAffineMap 2 face.succAbove point, _⟩) =
    NormedSpace.normalize (centeredFaceVector face point)
  congr 1

/-- [proved-derived; formal-checked] The corresponding canonical ordered-label singular simplex
is the addressed radial singular simplex. -/
theorem lowLabelSphereSimplex_succAbove_eq_radialSingularSimplex (face : Fin 4) :
    (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).symm
        (lowLabelSphereMap 2 (by omega) face.succAbove) =
      radialSingularSimplex face := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [lowLabelSphereMap_succAbove_eq_radialFace]
  rfl

/-- [proved-derived; formal-checked] The affine label target commutes exactly with every source
face. -/
theorem lowLabelAffineMap_face {degree : ℕ}
    (labels : Fin (degree + 2) → TetraVertex) (face : Fin (degree + 2)) :
    (lowLabelAffineMap (degree + 1) labels).comp (simplexFaceMap face) =
      lowLabelAffineMap degree (labels ∘ face.succAbove) := by
  apply ContinuousMap.ext
  intro point
  change stdSimplex.map labels (stdSimplex.map face.succAbove point) =
    stdSimplex.map (labels ∘ face.succAbove) point
  rw [stdSimplex.map_comp_apply]

/-- [proved-derived; formal-checked] The boundary and radial target retain the same exact face law;
proof witnesses for omitted coordinates carry no additional geometry. -/
theorem lowLabelSphereMap_face {degree : ℕ} (parentBelowThree : degree + 1 < 3)
    (labels : Fin (degree + 2) → TetraVertex) (face : Fin (degree + 2)) :
    (lowLabelSphereMap (degree + 1) parentBelowThree labels).comp (simplexFaceMap face) =
      lowLabelSphereMap degree (Nat.lt_trans (Nat.lt_succ_self degree) parentBelowThree)
        (labels ∘ face.succAbove) := by
  apply ContinuousMap.ext
  intro point
  apply congrArg boundaryRadial
  apply Subtype.ext
  exact ContinuousMap.congr_fun (lowLabelAffineMap_face labels face) point

/-! ## A degree-three affine label occurrence

The omitted coordinate is retained in the type of the occurrence.  This is the smallest
sphere-valued cone carrier needed by a later prism owner: its faces are the existing low-degree
label maps, while no singular-chain normalization is built into the occurrence. -/

/-- [definition] A four-label affine tetrahedron with one explicitly retained omitted vertex. -/
structure DegreeThreeAffineLabel where
  labels : Fin 4 → TetraVertex
  omitted : TetraVertex
  omitted_absent : ∀ index : Fin 4, labels index ≠ omitted

namespace DegreeThreeAffineLabel

/-- [definition] The affine map of the four-label word into the tetrahedron. -/
def affineMap (carrier : DegreeThreeAffineLabel) :
    C(Tetrahedron, Tetrahedron) :=
  lowLabelAffineMap 3 carrier.labels

/-- [proved-derived; formal-checked] The retained omitted coordinate is zero throughout the
affine tetrahedron map. -/
theorem affineMap_omitted_zero (carrier : DegreeThreeAffineLabel)
    (point : Tetrahedron) : carrier.affineMap point carrier.omitted = 0 := by
  change FunOnFinite.linearMap ℝ ℝ carrier.labels point carrier.omitted = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have filteredEmpty :
      Finset.univ.filter (fun index => carrier.labels index = carrier.omitted) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro index _
    exact carrier.omitted_absent index
  rw [filteredEmpty]
  simp

/-- [definition] The affine label map with its addressed zero-coordinate boundary witness. -/
def boundaryMap (carrier : DegreeThreeAffineLabel) :
    C(Tetrahedron, TetraBoundary) where
  toFun point := ⟨carrier.affineMap point, ⟨carrier.omitted,
    carrier.affineMap_omitted_zero point⟩⟩
  continuous_toFun := Continuous.subtype_mk carrier.affineMap.continuous _

/-- [definition] The sphere-valued degree-three affine label occurrence. -/
def sphereMap (carrier : DegreeThreeAffineLabel) :
    C(Tetrahedron, TwoSphere) :=
  boundaryRadial.comp carrier.boundaryMap

/-- [proved-derived; formal-checked] The degree-three affine sphere map restricts on every
source face to the existing low-label sphere map for the restricted ordered word. -/
theorem sphereMap_face (carrier : DegreeThreeAffineLabel) (face : Fin 4) :
    carrier.sphereMap.comp (simplexFaceMap face) =
      lowLabelSphereMap 2 (by omega) (carrier.labels ∘ face.succAbove) := by
  apply ContinuousMap.ext
  intro point
  rw [sphereMap, ContinuousMap.comp_apply, lowLabelSphereMap, ContinuousMap.comp_apply]
  apply congrArg boundaryRadial
  apply Subtype.ext
  exact ContinuousMap.congr_fun (lowLabelAffineMap_face carrier.labels face) point

/-- [definition] The degree-three affine label occurrence as a singular three-simplex. -/
def sphereSimplex (carrier : DegreeThreeAffineLabel) :
    SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm carrier.sphereMap

/-- [proved-derived; formal-checked] The addressed singular faces of the degree-three occurrence
are exactly the restricted low-label singular simplices. -/
theorem sphereSimplex_face (carrier : DegreeThreeAffineLabel) (face : Fin 4) :
    simplexFace face carrier.sphereSimplex =
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2))).symm
        (lowLabelSphereMap 2 (by omega) (carrier.labels ∘ face.succAbove)) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  rw [simplexFace_realization]
  simp only [sphereSimplex, Equiv.apply_symm_apply]
  exact carrier.sphereMap_face face

/-! ## Prefix cone specialization

The omitted coordinate remains explicit when one apex label is prefixed to an ordered triangle
word.  This retains the complete four-face singular boundary without any normalization quotient. -/

/-- [definition] Prefix one apex label to an ordered degree-two label word while retaining an
explicit omitted vertex. -/
def prefixCarrier (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    DegreeThreeAffineLabel where
  labels := Fin.cases apex labels
  omitted := omitted
  omitted_absent := by
    intro index
    refine Fin.cases apex_absent ?_ index
    intro tail
    exact labels_absent tail

@[simp]
theorem prefix_labels_zero (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels 0 = apex := rfl

@[simp]
theorem prefix_labels_succ (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted)
    (index : Fin 3) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels index.succ =
      labels index := rfl

/-- [definition] An unnormalized degree-two raw affine-label singular simplex. -/
def rawAffineLabelSimplex (labels : Fin 3 → TetraVertex) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      (lowLabelSphereMap 2 (by omega) labels)

/-- [proved-derived; formal-checked] The four ordered label words on a prefix occurrence retain
their exact face injections. -/
theorem prefix_face_word_zero (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (0 : Fin 4).succAbove = labels := by
  funext index
  fin_cases index <;> rfl

theorem prefix_face_word_one (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (1 : Fin 4).succAbove = ![apex, labels 1, labels 2] := by
  funext index
  fin_cases index <;> rfl

theorem prefix_face_word_two (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (2 : Fin 4).succAbove = ![apex, labels 0, labels 2] := by
  funext index
  fin_cases index <;> rfl

theorem prefix_face_word_three (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    (prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (3 : Fin 4).succAbove = ![apex, labels 0, labels 1] := by
  funext index
  fin_cases index <;> rfl

/-- [definition] The singular two-simplex carried by one addressed face of a prefix occurrence. -/
def prefixFaceSimplex (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted)
    (face : Fin 4) : SphereSingularSimplex 2 :=
  rawAffineLabelSimplex
    ((prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘ face.succAbove)

/-- [proved-derived; formal-checked] Every face of the prefix occurrence is the corresponding
restricted low-label singular simplex, with its ordered face injection retained. -/
theorem prefixSphereSimplex_face (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) (face : Fin 4) :
    simplexFace face
        (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      prefixFaceSimplex apex omitted labels apex_absent labels_absent face := by
  exact (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex_face face

/-- [proved-derived; formal-checked] The exterior face of a prefix occurrence is exactly the
original ordered degree-two low-label triangle. -/
theorem prefixSphereSimplex_face_zero (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    simplexFace 0
        (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2))).symm
        (lowLabelSphereMap 2 (by omega) labels) := by
  rw [prefixSphereSimplex_face]
  apply congrArg (fun map : C(Triangle, TwoSphere) =>
    (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).symm map)
  apply ContinuousMap.ext
  intro point
  congr 1

/-- [proved-derived; formal-checked] The prefix carrier's four face words are the exterior word,
the two middle folds, and the final exterior word, with all ordered occurrences retained. -/
theorem prefix_face_words (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    ((prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (0 : Fin 4).succAbove = labels) ∧
      ((prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (1 : Fin 4).succAbove = ![apex, labels 1, labels 2]) ∧
      ((prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (2 : Fin 4).succAbove = ![apex, labels 0, labels 2]) ∧
      ((prefixCarrier apex omitted labels apex_absent labels_absent).labels ∘
        (3 : Fin 4).succAbove = ![apex, labels 0, labels 1]) := by
  exact ⟨prefix_face_word_zero apex omitted labels apex_absent labels_absent,
    prefix_face_word_one apex omitted labels apex_absent labels_absent,
    prefix_face_word_two apex omitted labels apex_absent labels_absent,
    prefix_face_word_three apex omitted labels apex_absent labels_absent⟩

/-- [proved-derived; formal-checked] The prefix occurrence boundary is the explicit alternating
combination of its raw exterior triangle and the three retained apex-prefix face triangles. -/
theorem boundary_prefixSphereSimplex_eq_rawAffineLabelSimplex
    (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    SphereSingularChainComplex.d 3 2
        (simplexGenerator
          (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex) =
      simplexGenerator (rawAffineLabelSimplex labels) -
        simplexGenerator (rawAffineLabelSimplex ![apex, labels 1, labels 2]) +
        simplexGenerator (rawAffineLabelSimplex ![apex, labels 0, labels 2]) -
        simplexGenerator (rawAffineLabelSimplex ![apex, labels 0, labels 1]) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_four]
  rw [show simplexFace 0
      (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      rawAffineLabelSimplex labels by
    rw [prefixSphereSimplex_face]
    unfold prefixFaceSimplex
    rw [prefix_face_word_zero apex omitted labels apex_absent labels_absent]]
  rw [show simplexFace 1
      (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      rawAffineLabelSimplex ![apex, labels 1, labels 2] by
    rw [prefixSphereSimplex_face]
    unfold prefixFaceSimplex
    rw [prefix_face_word_one apex omitted labels apex_absent labels_absent]]
  rw [show simplexFace 2
      (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      rawAffineLabelSimplex ![apex, labels 0, labels 2] by
    rw [prefixSphereSimplex_face]
    unfold prefixFaceSimplex
    rw [prefix_face_word_two apex omitted labels apex_absent labels_absent]]
  rw [show simplexFace 3
      (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex =
      rawAffineLabelSimplex ![apex, labels 0, labels 1] by
    rw [prefixSphereSimplex_face]
    unfold prefixFaceSimplex
    rw [prefix_face_word_three apex omitted labels apex_absent labels_absent]]
  norm_num
  abel

/-- [proved-derived; formal-checked] The prefix occurrence has the exact alternating singular
boundary of its four retained low-label face occurrences. -/
theorem boundary_prefixSphereSimplex (apex omitted : TetraVertex) (labels : Fin 3 → TetraVertex)
    (apex_absent : apex ≠ omitted)
    (labels_absent : ∀ index : Fin 3, labels index ≠ omitted) :
    SphereSingularChainComplex.d 3 2
        (simplexGenerator
          (prefixCarrier apex omitted labels apex_absent labels_absent).sphereSimplex) =
      ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
        simplexGenerator
          (prefixFaceSimplex apex omitted labels apex_absent labels_absent face) := by
  rw [boundary_simplexGenerator]
  apply Finset.sum_congr rfl
  intro face _
  rw [prefixSphereSimplex_face]

end DegreeThreeAffineLabel

/-- [definition] One sphere triangle together with three labels whose open stars contain its
complete image. -/
structure CommonStarTriangle where
  source : C(Triangle, TwoSphere)
  labels : Fin 3 → TetraVertex
  carried : ∀ point index, source point ∈ vertexStar (labels index)

namespace CommonStarTriangle

/-- [definition] Exact tetrahedral-boundary address of the source triangle. -/
def sourceBoundaryMap (carrier : CommonStarTriangle) : C(Triangle, TetraBoundary) :=
  sphereBoundaryMap.comp carrier.source

/-- [proved-derived; formal-checked] Every selected label coordinate of the source boundary address
is strictly positive. -/
theorem sourceBoundaryMap_label_pos (carrier : CommonStarTriangle)
    (point : Triangle) (index : Fin 3) :
    0 < (carrier.sourceBoundaryMap point).1 (carrier.labels index) := by
  change 0 < sphereBoundaryCoordinate (carrier.source point) (carrier.labels index)
  exact (mem_vertexStar_iff_boundaryCoordinate_pos
    (carrier.source point) (carrier.labels index)).mp (carrier.carried point index)

/-- [proved-derived; formal-checked] Any zero source coordinate is absent from the three-label
word. -/
theorem source_zero_absent (carrier : CommonStarTriangle) (point : Triangle)
    (vertex : TetraVertex) (zeroLaw : (carrier.sourceBoundaryMap point).1 vertex = 0) :
    ∀ index : Fin 3, vertex ≠ carrier.labels index := by
  intro index equalLabel
  subst vertex
  exact (ne_of_gt (carrier.sourceBoundaryMap_label_pos point index)) zeroLaw

/-- [definition] Pointwise affine passage from the exact source boundary address to the
face-natural label target. -/
def affineLinePoint (carrier : CommonStarTriangle) (time : unitInterval)
    (point : Triangle) : Tetrahedron :=
  ⟨AffineMap.lineMap (carrier.sourceBoundaryMap point).1.1
      (lowLabelAffineMap 2 carrier.labels point).1 time.1,
    (convex_stdSimplex ℝ (Fin 4)).lineMap_mem
      (carrier.sourceBoundaryMap point).1.2
      (lowLabelAffineMap 2 carrier.labels point).2 time.2⟩

@[simp]
theorem affineLinePoint_apply (carrier : CommonStarTriangle) (time : unitInterval)
    (point : Triangle) (vertex : TetraVertex) :
    carrier.affineLinePoint time point vertex =
      (1 - time.1) * (carrier.sourceBoundaryMap point).1 vertex +
        time.1 * lowLabelAffineMap 2 carrier.labels point vertex := by
  rw [affineLinePoint]
  exact congrFun (AffineMap.lineMap_apply_module _ _ _) vertex

/-- [proved-derived; formal-checked] The pointwise affine passage retains one exact zero coordinate
throughout. -/
theorem affineLinePoint_has_zero (carrier : CommonStarTriangle) (time : unitInterval)
    (point : Triangle) :
    ∃ vertex : TetraVertex, carrier.affineLinePoint time point vertex = 0 := by
  obtain ⟨vertex, zeroLaw⟩ := (carrier.sourceBoundaryMap point).2
  refine ⟨vertex, ?_⟩
  rw [carrier.affineLinePoint_apply, zeroLaw]
  have targetZero : lowLabelAffineMap 2 carrier.labels point vertex = 0 := by
    change FunOnFinite.linearMap ℝ ℝ carrier.labels point vertex = 0
    rw [FunOnFinite.linearMap_apply_apply]
    have filteredEmpty :
        Finset.univ.filter (fun index => carrier.labels index = vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro index _
      exact Ne.symm (carrier.source_zero_absent point vertex zeroLaw index)
    rw [filteredEmpty]
    simp
  rw [targetZero]
  ring

/-- [definition] The complete continuous affine passage on the tetrahedral boundary. -/
def affineBoundaryHomotopy (carrier : CommonStarTriangle) :
    C(unitInterval × Triangle, TetraBoundary) where
  toFun pair :=
    ⟨carrier.affineLinePoint pair.1 pair.2,
      carrier.affineLinePoint_has_zero pair.1 pair.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_pi fun vertex => by
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have timeContinuous : Continuous (fun pair : unitInterval × Triangle => pair.1.1) :=
        continuous_subtype_val.comp continuous_fst
      have sourceContinuous : Continuous
          (fun pair : unitInterval × Triangle =>
            (carrier.sourceBoundaryMap pair.2).1.1 vertex) :=
        (continuous_apply vertex).comp
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp
              (carrier.sourceBoundaryMap.continuous.comp continuous_snd)))
      have targetContinuous : Continuous
          (fun pair : unitInterval × Triangle =>
            lowLabelAffineMap 2 carrier.labels pair.2 vertex) :=
        ((continuous_apply vertex).comp continuous_subtype_val).comp
          ((lowLabelAffineMap 2 carrier.labels).continuous.comp continuous_snd)
      exact ((continuous_const.sub timeContinuous).mul sourceContinuous).add
        (timeContinuous.mul targetContinuous)

/-- [definition] Radial return of the face-natural affine passage to the sphere. -/
def affineSphereHomotopy (carrier : CommonStarTriangle) :
    C(unitInterval × Triangle, TwoSphere) :=
  boundaryRadial.comp carrier.affineBoundaryHomotopy

/-- [definition] The addressed inclusion of one source edge throughout the homotopy cylinder. -/
def triangleCylinderFace (face : Fin 3) :
    C(unitInterval × stdSimplex ℝ (Fin 2), unitInterval × Triangle) where
  toFun pair := (pair.1, simplexFaceMap (degree := 1) face pair.2)
  continuous_toFun :=
    continuous_fst.prodMk
      ((simplexFaceMap (degree := 1) face).continuous.comp continuous_snd)

/-- [proved-derived; formal-checked] The returned affine passage starts at the original sphere
triangle exactly. -/
theorem affineSphereHomotopy_zero (carrier : CommonStarTriangle) (point : Triangle) :
    carrier.affineSphereHomotopy (0, point) = carrier.source point := by
  rw [affineSphereHomotopy, ContinuousMap.comp_apply]
  change boundaryRadial
      ⟨carrier.affineLinePoint 0 point, carrier.affineLinePoint_has_zero 0 point⟩ = _
  have boundaryZero :
      (⟨carrier.affineLinePoint 0 point,
          carrier.affineLinePoint_has_zero 0 point⟩ : TetraBoundary) =
        carrier.sourceBoundaryMap point := by
    apply Subtype.ext
    apply stdSimplex.ext
    funext vertex
    rw [affineLinePoint_apply]
    norm_num
  rw [boundaryZero, sourceBoundaryMap, ContinuousMap.comp_apply,
    boundaryRadial_sphereBoundaryMap]

/-- [proved-derived; formal-checked] At time one the returned passage is the face-natural affine
label realization. -/
theorem affineSphereHomotopy_one (carrier : CommonStarTriangle) (point : Triangle) :
    carrier.affineSphereHomotopy (1, point) =
      lowLabelSphereMap 2 (by omega) carrier.labels point := by
  rw [affineSphereHomotopy, ContinuousMap.comp_apply]
  apply congrArg boundaryRadial
  change
    (⟨carrier.affineLinePoint 1 point,
        carrier.affineLinePoint_has_zero 1 point⟩ : TetraBoundary) =
      lowLabelBoundaryMap 2 (by omega) carrier.labels point
  apply Subtype.ext
  apply stdSimplex.ext
  funext vertex
  rw [affineLinePoint_apply]
  norm_num
  rfl

/-- [proved-derived; formal-checked] The affine carrier is natural on shared addressed source
faces.  Equality of the actual edge source maps and of the ordered endpoint labels forces equality
of the complete edge homotopies; endpoint equality alone is not used. -/
theorem affineSphereHomotopy_face_congr
    (first second : CommonStarTriangle) (firstFace secondFace : Fin 3)
    (sourceLaw :
      first.source.comp (simplexFaceMap (degree := 1) firstFace) =
        second.source.comp (simplexFaceMap (degree := 1) secondFace))
    (labelLaw : first.labels ∘ firstFace.succAbove =
      second.labels ∘ secondFace.succAbove) :
    first.affineSphereHomotopy.comp (triangleCylinderFace firstFace) =
      second.affineSphereHomotopy.comp (triangleCylinderFace secondFace) := by
  have sourceBoundaryLaw :
      first.sourceBoundaryMap.comp (simplexFaceMap (degree := 1) firstFace) =
        second.sourceBoundaryMap.comp (simplexFaceMap (degree := 1) secondFace) := by
    rw [sourceBoundaryMap, sourceBoundaryMap,
      ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, sourceLaw]
  have targetLaw :
      (lowLabelAffineMap 2 first.labels).comp
          (simplexFaceMap (degree := 1) firstFace) =
        (lowLabelAffineMap 2 second.labels).comp
          (simplexFaceMap (degree := 1) secondFace) := by
    rw [lowLabelAffineMap_face, lowLabelAffineMap_face, labelLaw]
  apply ContinuousMap.ext
  intro pair
  apply congrArg boundaryRadial
  apply Subtype.ext
  apply stdSimplex.ext
  funext vertex
  change first.affineLinePoint pair.1
      (simplexFaceMap (degree := 1) firstFace pair.2) vertex =
    second.affineLinePoint pair.1
      (simplexFaceMap (degree := 1) secondFace pair.2) vertex
  rw [first.affineLinePoint_apply, second.affineLinePoint_apply]
  have sourcePointLaw := ContinuousMap.congr_fun sourceBoundaryLaw pair.2
  change first.sourceBoundaryMap
      (simplexFaceMap (degree := 1) firstFace pair.2) =
    second.sourceBoundaryMap
      (simplexFaceMap (degree := 1) secondFace pair.2) at sourcePointLaw
  have sourceCoordinateLaw := congrArg
    (fun point : TetraBoundary => point.1 vertex) sourcePointLaw
  have targetPointLaw := ContinuousMap.congr_fun targetLaw pair.2
  change lowLabelAffineMap 2 first.labels
      (simplexFaceMap (degree := 1) firstFace pair.2) =
    lowLabelAffineMap 2 second.labels
      (simplexFaceMap (degree := 1) secondFace pair.2) at targetPointLaw
  have targetCoordinateLaw := congrArg
    (fun point : Tetrahedron => point vertex) targetPointLaw
  rw [sourceCoordinateLaw, targetCoordinateLaw]

end CommonStarTriangle

/-! ## The degree-one common-star carrier

The edge carrier is not an endpoint quotient of the triangle construction.  It retains the
actual singular edge, its two globally addressed labels, and the assertion that the complete
edge image lies in both selected stars.  This is precisely the incidence needed for the
degree-one prism and its endpoint-path cancellation. -/

/-- [definition] One sphere edge together with two labels whose open stars contain its complete
image. -/
structure CommonStarEdge where
  source : C(stdSimplex ℝ (Fin 2), TwoSphere)
  labels : Fin 2 → TetraVertex
  carried : ∀ point index, source point ∈ vertexStar (labels index)

namespace CommonStarEdge

/-- [definition] Exact tetrahedral-boundary address of the source edge. -/
def sourceBoundaryMap (carrier : CommonStarEdge) :
    C(stdSimplex ℝ (Fin 2), TetraBoundary) :=
  sphereBoundaryMap.comp carrier.source

/-- [proved-derived; formal-checked] Every selected endpoint-label coordinate is positive over
the complete edge image. -/
theorem sourceBoundaryMap_label_pos (carrier : CommonStarEdge)
    (point : stdSimplex ℝ (Fin 2)) (index : Fin 2) :
    0 < (carrier.sourceBoundaryMap point).1 (carrier.labels index) := by
  change 0 < sphereBoundaryCoordinate (carrier.source point) (carrier.labels index)
  exact (mem_vertexStar_iff_boundaryCoordinate_pos
    (carrier.source point) (carrier.labels index)).mp (carrier.carried point index)

/-- [proved-derived; formal-checked] A zero source coordinate is absent from both endpoint
labels. -/
theorem source_zero_absent (carrier : CommonStarEdge)
    (point : stdSimplex ℝ (Fin 2)) (vertex : TetraVertex)
    (zeroLaw : (carrier.sourceBoundaryMap point).1 vertex = 0) :
    ∀ index : Fin 2, vertex ≠ carrier.labels index := by
  intro index equalLabel
  subst vertex
  exact (ne_of_gt (carrier.sourceBoundaryMap_label_pos point index)) zeroLaw

/-- [definition] Pointwise affine passage from the exact source boundary address to the ordered
two-label target. -/
def affineLinePoint (carrier : CommonStarEdge) (time : unitInterval)
    (point : stdSimplex ℝ (Fin 2)) : Tetrahedron :=
  ⟨AffineMap.lineMap (carrier.sourceBoundaryMap point).1.1
      (lowLabelAffineMap 1 carrier.labels point).1 time.1,
    (convex_stdSimplex ℝ (Fin 4)).lineMap_mem
      (carrier.sourceBoundaryMap point).1.2
      (lowLabelAffineMap 1 carrier.labels point).2 time.2⟩

@[simp]
theorem affineLinePoint_apply (carrier : CommonStarEdge) (time : unitInterval)
    (point : stdSimplex ℝ (Fin 2)) (vertex : TetraVertex) :
    carrier.affineLinePoint time point vertex =
      (1 - time.1) * (carrier.sourceBoundaryMap point).1 vertex +
        time.1 * lowLabelAffineMap 1 carrier.labels point vertex := by
  rw [affineLinePoint]
  exact congrFun (AffineMap.lineMap_apply_module _ _ _) vertex

/-- [proved-derived; formal-checked] The affine passage retains one exact boundary coordinate
throughout. -/
theorem affineLinePoint_has_zero (carrier : CommonStarEdge) (time : unitInterval)
    (point : stdSimplex ℝ (Fin 2)) :
    ∃ vertex : TetraVertex, carrier.affineLinePoint time point vertex = 0 := by
  obtain ⟨vertex, zeroLaw⟩ := (carrier.sourceBoundaryMap point).2
  refine ⟨vertex, ?_⟩
  rw [carrier.affineLinePoint_apply, zeroLaw]
  have targetZero : lowLabelAffineMap 1 carrier.labels point vertex = 0 := by
    change FunOnFinite.linearMap ℝ ℝ carrier.labels point vertex = 0
    rw [FunOnFinite.linearMap_apply_apply]
    have filteredEmpty :
        Finset.univ.filter (fun index => carrier.labels index = vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro index _
      exact Ne.symm (carrier.source_zero_absent point vertex zeroLaw index)
    rw [filteredEmpty]
    simp
  rw [targetZero]
  ring

/-- [definition] The complete continuous boundary passage for one addressed edge. -/
def affineBoundaryHomotopy (carrier : CommonStarEdge) :
    C(unitInterval × stdSimplex ℝ (Fin 2), TetraBoundary) where
  toFun pair :=
    ⟨carrier.affineLinePoint pair.1 pair.2,
      carrier.affineLinePoint_has_zero pair.1 pair.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_pi fun vertex => by
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have timeContinuous :
          Continuous (fun pair : unitInterval × stdSimplex ℝ (Fin 2) => pair.1.1) :=
        continuous_subtype_val.comp continuous_fst
      have sourceContinuous : Continuous
          (fun pair : unitInterval × stdSimplex ℝ (Fin 2) =>
            (carrier.sourceBoundaryMap pair.2).1.1 vertex) :=
        (continuous_apply vertex).comp
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp
              (carrier.sourceBoundaryMap.continuous.comp continuous_snd)))
      have targetContinuous : Continuous
          (fun pair : unitInterval × stdSimplex ℝ (Fin 2) =>
            lowLabelAffineMap 1 carrier.labels pair.2 vertex) :=
        ((continuous_apply vertex).comp continuous_subtype_val).comp
          ((lowLabelAffineMap 1 carrier.labels).continuous.comp continuous_snd)
      exact ((continuous_const.sub timeContinuous).mul sourceContinuous).add
        (timeContinuous.mul targetContinuous)

/-- [definition] Radial return of the degree-one affine passage to the sphere. -/
def affineSphereHomotopy (carrier : CommonStarEdge) :
    C(unitInterval × stdSimplex ℝ (Fin 2), TwoSphere) :=
  boundaryRadial.comp carrier.affineBoundaryHomotopy

/-- [proved-derived; formal-checked] The edge passage starts at the exact source edge. -/
theorem affineSphereHomotopy_zero (carrier : CommonStarEdge)
    (point : stdSimplex ℝ (Fin 2)) :
    carrier.affineSphereHomotopy (0, point) = carrier.source point := by
  rw [affineSphereHomotopy, ContinuousMap.comp_apply]
  change boundaryRadial
      ⟨carrier.affineLinePoint 0 point, carrier.affineLinePoint_has_zero 0 point⟩ = _
  have boundaryZero :
      (⟨carrier.affineLinePoint 0 point,
          carrier.affineLinePoint_has_zero 0 point⟩ : TetraBoundary) =
        carrier.sourceBoundaryMap point := by
    apply Subtype.ext
    apply stdSimplex.ext
    funext vertex
    rw [affineLinePoint_apply]
    norm_num
  rw [boundaryZero, sourceBoundaryMap, ContinuousMap.comp_apply,
    boundaryRadial_sphereBoundaryMap]

/-- [proved-derived; formal-checked] The edge passage ends at the face-natural ordered-label
realization. -/
theorem affineSphereHomotopy_one (carrier : CommonStarEdge)
    (point : stdSimplex ℝ (Fin 2)) :
    carrier.affineSphereHomotopy (1, point) =
      lowLabelSphereMap 1 (by omega) carrier.labels point := by
  rw [affineSphereHomotopy, ContinuousMap.comp_apply]
  apply congrArg boundaryRadial
  change
    (⟨carrier.affineLinePoint 1 point,
        carrier.affineLinePoint_has_zero 1 point⟩ : TetraBoundary) =
      lowLabelBoundaryMap 1 (by omega) carrier.labels point
  apply Subtype.ext
  apply stdSimplex.ext
  funext vertex
  rw [affineLinePoint_apply]
  norm_num
  rfl

/-- [proved-derived; formal-checked] The value of the affine passage at an endpoint depends only
on the actual source point and the selected endpoint label.  This is the exact incidence law
which later cancels vertical prism paths. -/
theorem affineSphereHomotopy_vertex_congr
    (first second : CommonStarEdge) (firstVertex secondVertex : Fin 2)
    (sourceLaw : first.source (stdSimplex.vertex firstVertex) =
      second.source (stdSimplex.vertex secondVertex))
    (labelLaw : first.labels firstVertex = second.labels secondVertex)
    (time : unitInterval) :
    first.affineSphereHomotopy (time, stdSimplex.vertex firstVertex) =
      second.affineSphereHomotopy (time, stdSimplex.vertex secondVertex) := by
  rw [affineSphereHomotopy, affineSphereHomotopy]
  apply congrArg boundaryRadial
  apply Subtype.ext
  apply stdSimplex.ext
  funext vertex
  change first.affineLinePoint time (stdSimplex.vertex firstVertex) vertex =
    second.affineLinePoint time (stdSimplex.vertex secondVertex) vertex
  rw [affineLinePoint_apply, affineLinePoint_apply]
  have sourceBoundaryLaw :
      first.sourceBoundaryMap (stdSimplex.vertex firstVertex) =
        second.sourceBoundaryMap (stdSimplex.vertex secondVertex) := by
    rw [sourceBoundaryMap, sourceBoundaryMap, ContinuousMap.comp_apply,
      ContinuousMap.comp_apply, sourceLaw]
  have sourceCoordinateLaw := congrArg
    (fun point : TetraBoundary => point.1 vertex) sourceBoundaryLaw
  rw [sourceCoordinateLaw]
  have targetLaw :
      lowLabelAffineMap 1 first.labels (stdSimplex.vertex firstVertex) =
        lowLabelAffineMap 1 second.labels (stdSimplex.vertex secondVertex) := by
    change stdSimplex.map first.labels (stdSimplex.vertex firstVertex) =
      stdSimplex.map second.labels (stdSimplex.vertex secondVertex)
    rw [stdSimplex.map_vertex, stdSimplex.map_vertex, labelLaw]
  rw [congrArg (fun point : Tetrahedron => point vertex) targetLaw]

end CommonStarEdge

section Audit

#print axioms exists_omitted_label
#print axioms omittedLabel
#print axioms label_ne_omittedLabel
#print axioms labelApex
#print axioms labelApex_ne_omittedLabel
#print axioms lowLabelAffineMap_has_zero
#print axioms lowLabelSphereMap_succAbove_eq_radialFace
#print axioms lowLabelSphereSimplex_succAbove_eq_radialSingularSimplex
#print axioms lowLabelSphereMap_face
#print axioms DegreeThreeAffineLabel.affineMap_omitted_zero
#print axioms DegreeThreeAffineLabel.sphereMap_face
#print axioms DegreeThreeAffineLabel.sphereSimplex_face
#print axioms DegreeThreeAffineLabel.prefix_labels_zero
#print axioms DegreeThreeAffineLabel.prefix_labels_succ
#print axioms DegreeThreeAffineLabel.prefixSphereSimplex_face
#print axioms DegreeThreeAffineLabel.prefixSphereSimplex_face_zero
#print axioms DegreeThreeAffineLabel.boundary_prefixSphereSimplex
#print axioms CommonStarTriangle.affineLinePoint_has_zero
#print axioms CommonStarTriangle.affineBoundaryHomotopy
#print axioms CommonStarTriangle.affineSphereHomotopy_zero
#print axioms CommonStarTriangle.affineSphereHomotopy_one
#print axioms CommonStarTriangle.affineSphereHomotopy_face_congr
#print axioms CommonStarEdge.affineLinePoint_has_zero
#print axioms CommonStarEdge.affineSphereHomotopy_zero
#print axioms CommonStarEdge.affineSphereHomotopy_one
#print axioms CommonStarEdge.affineSphereHomotopy_vertex_congr

end Audit

end Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier
