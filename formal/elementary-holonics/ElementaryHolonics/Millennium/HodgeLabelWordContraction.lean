import ElementaryHolonics.Foundation.OrderedWordChain
import ElementaryHolonics.Millennium.HodgeTriangleHomotopyPrism
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Geometric receiver for the ordered-label contraction

The free ordered-word calculus is owned by `Foundation.OrderedWordChain`.  This file is the
geometric receiver for its supported tetrahedral words.  Repetitions and folds are retained as
word occurrences; support only records that the fixed apex has an available omitted coordinate.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Soma.Holonics.Millennium.HodgeLabelWordContraction

open Soma.Holonics.OrderedWordChain
open Soma.Holonics.Millennium.HodgeCommonStarAffineCarrier
open Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry

abbrev Label := TetraVertex
abbrev TriangleWord := Word Label 3
abbrev FreeTriangle := Chain ℚ Label 3
abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

abbrev WordTriangleChain := TriangleWord →₀ ℚ
abbrev WordEdgeChain := Word Label 2 →₀ ℚ

/-- A word lies in one fixed tetrahedral boundary chart when every addressed entry avoids the
chart's omitted coordinate. -/
def WordAvoids (omitted : Label) (word : TriangleWord) : Prop :=
  ∀ index : Fin 3, word index ≠ omitted

def fixedSupportSet (omitted : Label) : Set TriangleWord :=
  {word | WordAvoids omitted word}

abbrev FixedSupportedWord (omitted : Label) := fixedSupportSet omitted
abbrev FixedSupportedChain (omitted : Label) := FixedSupportedWord omitted →₀ ℚ

/-- Forgetting the fixed chart witness is the inverse of restricting a supported free current. -/
def fixedForgetSupport (omitted : Label) :
    FixedSupportedChain omitted →ₗ[ℚ] FreeTriangle :=
  (Submodule.subtype (Finsupp.supported ℚ ℚ (fixedSupportSet omitted))).comp
    (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
      (fixedSupportSet omitted)).symm.toLinearMap

/-- Restrict a free current whose complete Finsupp support lies in one fixed chart. -/
def fixedSupportLift (omitted : Label) (chain : FreeTriangle)
    (supported : chain ∈ Finsupp.supported ℚ ℚ (fixedSupportSet omitted)) :
    FixedSupportedChain omitted :=
  Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    (fixedSupportSet omitted) ⟨chain, supported⟩

@[simp]
theorem fixedForgetSupport_lift (omitted : Label) (chain : FreeTriangle)
    (supported : chain ∈ Finsupp.supported ℚ ℚ (fixedSupportSet omitted)) :
    fixedForgetSupport omitted (fixedSupportLift omitted chain supported) = chain := by
  change ((Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    (fixedSupportSet omitted)).symm
      ((Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
        (fixedSupportSet omitted)) ⟨chain, supported⟩)).1 = chain
  rw [LinearEquiv.symm_apply_apply]

/-- Raw radial realization of every free ordered triangle word. -/
def rawWordRealization : FreeTriangle →ₗ[ℚ] SphereChain 2 :=
  Finsupp.linearCombination ℚ (fun word =>
    simplexGenerator (rawAffineLabelSimplex word))

def fixedRawTriangleReceiver (omitted : Label) :
    FixedSupportedChain omitted →ₗ[ℚ] SphereChain 2 :=
  rawWordRealization.comp (fixedForgetSupport omitted)

def fixedGeometricPrefixReceiver (apex omitted : Label)
    (apex_absent : apex ≠ omitted) :
    FixedSupportedChain omitted →ₗ[ℚ] SphereChain 3 :=
  Finsupp.linearCombination ℚ (fun word =>
    simplexGenerator
      (DegreeThreeAffineLabel.prefixCarrier apex omitted word.1
        apex_absent word.2).sphereSimplex)

theorem fixedGeometricPrefixReceiver_boundary_atom
    (apex omitted : Label) (apex_absent : apex ≠ omitted)
    (word : FixedSupportedWord omitted) :
    SphereSingularChainComplex.d 3 2
        (fixedGeometricPrefixReceiver apex omitted apex_absent
          (Finsupp.single word 1)) =
      fixedRawTriangleReceiver omitted (Finsupp.single word 1) -
        (simplexGenerator (rawAffineLabelSimplex ![apex, word.1 1, word.1 2]) -
          simplexGenerator (rawAffineLabelSimplex ![apex, word.1 0, word.1 2]) +
          simplexGenerator (rawAffineLabelSimplex ![apex, word.1 0, word.1 1])) := by
  simp only [fixedGeometricPrefixReceiver, Finsupp.linearCombination_single, one_smul]
  change SphereSingularChainComplex.d 3 2
      (simplexGenerator
        (DegreeThreeAffineLabel.prefixCarrier apex omitted word.1
          apex_absent word.2).sphereSimplex) = _
  rw [DegreeThreeAffineLabel.boundary_prefixSphereSimplex_eq_rawAffineLabelSimplex
    apex omitted word.1 apex_absent word.2]
  simp [fixedRawTriangleReceiver, rawWordRealization, fixedForgetSupport,
    Finsupp.supportedEquivFinsupp_symm_single]
  abel

/-- The complete geometric side-face current produced by prefixing the fixed apex to the free
ordered boundary of a current in one fixed chart. -/
def fixedPrefixSideReceiver (apex omitted : Label) :
    FixedSupportedChain omitted →ₗ[ℚ] SphereChain 2 :=
  rawWordRealization.comp
    ((prefixEdge (R := ℚ) apex).comp
      ((triangleBoundary (R := ℚ)).comp (fixedForgetSupport omitted)))

/-- One fixed-chart word realizes its prefixed free boundary as the three geometric side faces of
the prefix tetrahedron. -/
theorem fixedPrefixSideReceiver_atom (apex omitted : Label)
    (word : FixedSupportedWord omitted) :
    fixedPrefixSideReceiver apex omitted (Finsupp.single word 1) =
      simplexGenerator (rawAffineLabelSimplex ![apex, word.1 1, word.1 2]) -
        simplexGenerator (rawAffineLabelSimplex ![apex, word.1 0, word.1 2]) +
          simplexGenerator (rawAffineLabelSimplex ![apex, word.1 0, word.1 1]) := by
  have faceZero : face word.1 (0 : Fin 3) = ![word.1 1, word.1 2] := by
    funext index
    fin_cases index <;> rfl
  have faceOne : face word.1 (1 : Fin 3) = ![word.1 0, word.1 2] := by
    funext index
    fin_cases index <;> rfl
  have faceTwo : face word.1 (2 : Fin 3) = ![word.1 0, word.1 1] := by
    funext index
    fin_cases index <;> rfl
  have prefixZero : prefixWord apex ![word.1 1, word.1 2] =
      ![apex, word.1 1, word.1 2] := by
    funext index
    fin_cases index <;> rfl
  have prefixOne : prefixWord apex ![word.1 0, word.1 2] =
      ![apex, word.1 0, word.1 2] := by
    funext index
    fin_cases index <;> rfl
  have prefixTwo : prefixWord apex ![word.1 0, word.1 1] =
      ![apex, word.1 0, word.1 1] := by
    funext index
    fin_cases index <;> rfl
  simp only [fixedPrefixSideReceiver, LinearMap.comp_apply]
  rw [show fixedForgetSupport omitted (Finsupp.single word 1) =
      generator (R := ℚ) word.1 by
    simp [fixedForgetSupport, generator, Finsupp.supportedEquivFinsupp_symm_single]]
  rw [show triangleBoundary (R := ℚ) (generator (R := ℚ) word.1) =
      triangleBoundaryAtom (R := ℚ) word.1 by
    change triangleBoundary (R := ℚ) (Finsupp.single word.1 1) = _
    rw [triangleBoundary_single, one_smul]]
  simp only [triangleBoundaryAtom, Fin.sum_univ_three, map_add, map_smul,
    prefixEdge_single, prefixEdgeAtom, rawWordRealization, generator,
    Finsupp.linearCombination_single]
  rw [faceZero, faceOne, faceTwo]
  rw [prefixZero, prefixOne, prefixTwo]
  norm_num
  abel

/-- [proved-derived; formal-checked] Prefixing every occurrence in one fixed chart returns the raw
geometric current minus the complete geometrically realized prefixed boundary current.  This is
the chain-level receiver square joining the free ordered contraction to singular chains. -/
theorem fixedGeometricPrefixReceiver_boundary (apex omitted : Label)
    (apex_absent : apex ≠ omitted) (chain : FixedSupportedChain omitted) :
    SphereSingularChainComplex.d 3 2
        (fixedGeometricPrefixReceiver apex omitted apex_absent chain) =
      fixedRawTriangleReceiver omitted chain - fixedPrefixSideReceiver apex omitted chain := by
  let left : FixedSupportedChain omitted →ₗ[ℚ] SphereChain 2 :=
    (SphereSingularChainComplex.d 3 2).hom.comp
      (fixedGeometricPrefixReceiver apex omitted apex_absent)
  let right : FixedSupportedChain omitted →ₗ[ℚ] SphereChain 2 :=
    fixedRawTriangleReceiver omitted - fixedPrefixSideReceiver apex omitted
  have equalMaps : left = right := by
    apply Finsupp.lhom_ext
    intro word coefficient
    have singleAsSmul :
        (Finsupp.single word coefficient : FixedSupportedChain omitted) =
          coefficient • Finsupp.single word 1 := by
      simp
    rw [singleAsSmul]
    simp only [left, right, LinearMap.comp_apply, LinearMap.sub_apply, map_smul]
    rw [fixedGeometricPrefixReceiver_boundary_atom apex omitted apex_absent word,
      fixedPrefixSideReceiver_atom apex omitted word]
  change left chain = right chain
  exact LinearMap.congr_fun equalMaps chain

/-- A closed fixed-chart ordered current has no prefixed side current. -/
theorem fixedPrefixSideReceiver_of_closed (apex omitted : Label)
    (chain : FixedSupportedChain omitted)
    (closed : triangleBoundary (R := ℚ) (fixedForgetSupport omitted chain) = 0) :
    fixedPrefixSideReceiver apex omitted chain = 0 := by
  rw [fixedPrefixSideReceiver]
  simp only [LinearMap.comp_apply, closed, map_zero]

/-- [proved-derived; formal-checked] A closed current in one fixed chart is filled exactly by its
geometric prefix receiver. -/
theorem fixedGeometricPrefixReceiver_boundary_of_closed (apex omitted : Label)
    (apex_absent : apex ≠ omitted) (chain : FixedSupportedChain omitted)
    (closed : triangleBoundary (R := ℚ) (fixedForgetSupport omitted chain) = 0) :
    SphereSingularChainComplex.d 3 2
        (fixedGeometricPrefixReceiver apex omitted apex_absent chain) =
      fixedRawTriangleReceiver omitted chain := by
  rw [fixedGeometricPrefixReceiver_boundary,
    fixedPrefixSideReceiver_of_closed apex omitted chain closed, sub_zero]

/-- The finite tetrahedral face current written in the free ordered-word receiver. -/
def faceWordRealization : FaceChain →ₗ[ℚ] WordTriangleChain where
  toFun chain :=
    chain 0 • generator (R := ℚ) ![(1 : Label), 2, 3] +
    chain 1 • generator (R := ℚ) ![(0 : Label), 2, 3] +
    chain 2 • generator (R := ℚ) ![(0 : Label), 1, 3] +
    chain 3 • generator (R := ℚ) ![(0 : Label), 1, 2]
  map_add' left right := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' coefficient chain := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
      smul_add]

/-- The finite tetrahedral edge current written in the free ordered-word receiver. -/
def edgeWordRealization : EdgeChain →ₗ[ℚ] WordEdgeChain where
  toFun chain :=
    chain .e01 • generator (R := ℚ) ![(0 : Label), 1] +
    chain .e02 • generator (R := ℚ) ![(0 : Label), 2] +
    chain .e03 • generator (R := ℚ) ![(0 : Label), 3] +
    chain .e12 • generator (R := ℚ) ![(1 : Label), 2] +
    chain .e13 • generator (R := ℚ) ![(1 : Label), 3] +
    chain .e23 • generator (R := ℚ) ![(2 : Label), 3]
  map_add' left right := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' coefficient chain := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
      smul_add]

/-- The finite carried face of a three-label word in the free ordered-word receiver. -/
def faceWordCurrent (labels : TriangleWord) : WordTriangleChain :=
  faceWordRealization (orientedFaceCarry (labels 0) (labels 1) (labels 2))

/-- The canonical ordered label word of one tetrahedral face. -/
def canonicalFaceWord : Fin 4 → TriangleWord
  | 0 => ![1, 2, 3]
  | 1 => ![0, 2, 3]
  | 2 => ![0, 1, 3]
  | 3 => ![0, 1, 2]

/-- A nonzero carried-face coefficient can occur only on the one canonical face word which avoids
the same omitted coordinate as all three source labels. -/
theorem orientedFaceCarry_nonzero_avoids
    (a b c omitted : Label)
    (a_absent : a ≠ omitted) (b_absent : b ≠ omitted) (c_absent : c ≠ omitted)
    (face : Fin 4) (nonzero : orientedFaceCarry a b c face ≠ 0) :
    WordAvoids omitted (canonicalFaceWord face) := by
  intro index
  fin_cases omitted <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases face <;> fin_cases index <;>
    simp_all [canonicalFaceWord, orientedFaceCarry, triangleOrientation, Fin.ext_iff]

/-- A scalar-weighted generator is supported whenever each nonzero occurrence avoids the fixed
omitted coordinate. -/
theorem smul_generator_mem_fixedSupport (omitted : Label) (coefficient : ℚ)
    (word : TriangleWord) (supported : coefficient ≠ 0 → WordAvoids omitted word) :
    coefficient • generator (R := ℚ) word ∈
      Finsupp.supported ℚ ℚ (fixedSupportSet omitted) := by
  by_cases zeroCoefficient : coefficient = 0
  · simp [zeroCoefficient]
  · exact Submodule.smul_mem _ coefficient <| by
      simpa [generator, fixedSupportSet] using
        (Finsupp.single_mem_supported ℚ (1 : ℚ) (supported zeroCoefficient))

/-- The finite carried face current retains the fixed omitted-coordinate chart of its labels. -/
theorem faceWordCurrent_supported (labels : TriangleWord) (omitted : Label)
    (labels_absent : ∀ index, labels index ≠ omitted) :
    faceWordCurrent labels ∈ Finsupp.supported ℚ ℚ (fixedSupportSet omitted) := by
  unfold faceWordCurrent faceWordRealization
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply smul_generator_mem_fixedSupport
        intro nonzero
        exact orientedFaceCarry_nonzero_avoids
          (labels 0) (labels 1) (labels 2) omitted
          (labels_absent 0) (labels_absent 1) (labels_absent 2) 0 nonzero
      · apply smul_generator_mem_fixedSupport
        intro nonzero
        exact orientedFaceCarry_nonzero_avoids
          (labels 0) (labels 1) (labels 2) omitted
          (labels_absent 0) (labels_absent 1) (labels_absent 2) 1 nonzero
    · apply smul_generator_mem_fixedSupport
      intro nonzero
      exact orientedFaceCarry_nonzero_avoids
        (labels 0) (labels 1) (labels 2) omitted
        (labels_absent 0) (labels_absent 1) (labels_absent 2) 2 nonzero
  · apply smul_generator_mem_fixedSupport
    intro nonzero
    exact orientedFaceCarry_nonzero_avoids
      (labels 0) (labels 1) (labels 2) omitted
      (labels_absent 0) (labels_absent 1) (labels_absent 2) 3 nonzero

/-- One raw ordered triangle has the complete alternating ordered-edge boundary. -/
theorem triangleBoundary_generator (labels : TriangleWord) :
    triangleBoundary (R := ℚ) (generator (R := ℚ) labels) =
      generator (R := ℚ) (labels ∘ (0 : Fin 3).succAbove) -
        generator (R := ℚ) (labels ∘ (1 : Fin 3).succAbove) +
          generator (R := ℚ) (labels ∘ (2 : Fin 3).succAbove) := by
  rw [show generator (R := ℚ) labels = Finsupp.single labels 1 by rfl,
    triangleBoundary_single, one_smul]
  rw [triangleBoundaryAtom, Fin.sum_univ_three]
  norm_num
  abel

@[simp]
theorem word3_face_zero (a b c : Label) :
    (![a, b, c] : TriangleWord) ∘ (0 : Fin 3).succAbove = ![b, c] := by
  funext index
  fin_cases index <;> rfl

@[simp]
theorem word3_tail (a b c : Label) :
    (![a, b, c] : TriangleWord) ∘ Fin.succ = ![b, c] := by
  funext index
  fin_cases index <;> rfl

@[simp]
theorem word3_face_one (a b c : Label) :
    (![a, b, c] : TriangleWord) ∘ (1 : Fin 3).succAbove = ![a, c] := by
  funext index
  fin_cases index <;> rfl

@[simp]
theorem word3_face_two (a b c : Label) :
    (![a, b, c] : TriangleWord) ∘ (2 : Fin 3).succAbove = ![a, b] := by
  funext index
  fin_cases index <;> rfl

/-- [proved-derived; formal-checked] The canonical free-word receiver is a chain map from the
finite tetrahedral face incidence into ordered word incidence. -/
theorem triangleBoundary_faceWordRealization (chain : FaceChain) :
    triangleBoundary (R := ℚ) (faceWordRealization chain) =
      edgeWordRealization (faceBoundary chain) := by
  change triangleBoundary (R := ℚ)
      (chain 0 • generator (R := ℚ) ![(1 : Label), 2, 3] +
        chain 1 • generator (R := ℚ) ![(0 : Label), 2, 3] +
        chain 2 • generator (R := ℚ) ![(0 : Label), 1, 3] +
        chain 3 • generator (R := ℚ) ![(0 : Label), 1, 2]) =
    (faceBoundary chain) .e01 • generator (R := ℚ) ![(0 : Label), 1] +
      (faceBoundary chain) .e02 • generator (R := ℚ) ![(0 : Label), 2] +
      (faceBoundary chain) .e03 • generator (R := ℚ) ![(0 : Label), 3] +
      (faceBoundary chain) .e12 • generator (R := ℚ) ![(1 : Label), 2] +
      (faceBoundary chain) .e13 • generator (R := ℚ) ![(1 : Label), 3] +
      (faceBoundary chain) .e23 • generator (R := ℚ) ![(2 : Label), 3]
  simp only [map_add, map_smul, triangleBoundary_generator,
    word3_face_zero, word3_face_one, word3_face_two]
  simp [faceBoundary, boundaryColumn, Fin.sum_univ_four]
  module

/-- The free word boundary of a finite carried face is the carried alternating edge current. -/
theorem triangleBoundary_faceWordCurrent (labels : TriangleWord) :
    triangleBoundary (R := ℚ) (faceWordCurrent labels) =
      edgeWordRealization (orientedEdgeCarry (labels 1) (labels 2)) -
        edgeWordRealization (orientedEdgeCarry (labels 0) (labels 2)) +
          edgeWordRealization (orientedEdgeCarry (labels 0) (labels 1)) := by
  rw [faceWordCurrent, triangleBoundary_faceWordRealization,
    faceBoundary_orientedFaceCarry]
  simp only [map_sub, map_add]

/-- The edge correction written before geometric realization.  Equal and reversed words retain
their constant/fold occurrences exactly as in the singular receiver. -/
def edgeCorrectionWord (first second : Label) : WordTriangleChain :=
  if first = second then
    generator (R := ℚ) ![first, first, first]
  else if first < second then
    0
  else
      generator (R := ℚ) ![first, second, first] +
      generator (R := ℚ) ![first, first, first]

/-- Every retained fold/constant occurrence in an edge correction remains in the fixed chart of
its endpoint labels. -/
theorem edgeCorrectionWord_supported (omitted first second : Label)
    (first_absent : first ≠ omitted) (second_absent : second ≠ omitted) :
    edgeCorrectionWord first second ∈
      Finsupp.supported ℚ ℚ (fixedSupportSet omitted) := by
  have constantSupported : WordAvoids omitted ![first, first, first] := by
    intro index
    fin_cases index <;> exact first_absent
  have foldSupported : WordAvoids omitted ![first, second, first] := by
    intro index
    fin_cases index <;> assumption
  by_cases same : first = second
  · rw [edgeCorrectionWord, if_pos same]
    simpa [generator, fixedSupportSet] using
      (Finsupp.single_mem_supported ℚ (1 : ℚ) constantSupported)
  · by_cases increasing : first < second
    · rw [edgeCorrectionWord, if_neg same, if_pos increasing]
      exact Submodule.zero_mem _
    · rw [edgeCorrectionWord, if_neg same, if_neg increasing]
      exact Submodule.add_mem _
        (by simpa [generator, fixedSupportSet] using
          (Finsupp.single_mem_supported ℚ (1 : ℚ) foldSupported))
        (by simpa [generator, fixedSupportSet] using
          (Finsupp.single_mem_supported ℚ (1 : ℚ) constantSupported))

/-- [proved-derived; formal-checked] The ordered edge correction returns raw word minus finite
oriented-edge realization before any geometric receiver is applied. -/
theorem edgeCorrectionWord_boundary (first second : Label) :
    triangleBoundary (R := ℚ) (edgeCorrectionWord first second) =
      generator (R := ℚ) ![first, second] -
        edgeWordRealization (orientedEdgeCarry first second) := by
  fin_cases first <;> fin_cases second <;>
    simp [edgeCorrectionWord, edgeWordRealization, triangleBoundary_generator,
      orientedEdgeCarry, edgeInitial, edgeTerminal] <;>
    module

/-- A canonical tetrahedral face word realizes as the already-owned radial singular face. -/
theorem rawWordRealization_canonicalFace (faceIndex : Fin 4) :
    rawWordRealization (generator (R := ℚ) (canonicalFaceWord faceIndex)) =
      simplexGenerator (radialSingularSimplex faceIndex) := by
  have wordEq : canonicalFaceWord faceIndex = faceIndex.succAbove := by
    fin_cases faceIndex <;> funext index <;> fin_cases index <;> rfl
  simp only [rawWordRealization, generator, Finsupp.linearCombination_single, one_smul]
  rw [wordEq, rawAffineLabelSimplex,
    lowLabelSphereSimplex_succAbove_eq_radialSingularSimplex]

/-- [proved-derived; formal-checked] Free canonical face-word realization commutes with the finite
tetrahedral face realization. -/
theorem rawWordRealization_faceWordRealization (chain : FaceChain) :
    rawWordRealization (faceWordRealization chain) = faceRealization chain := by
  change rawWordRealization
      (chain 0 • generator (R := ℚ) ![(1 : Label), 2, 3] +
        chain 1 • generator (R := ℚ) ![(0 : Label), 2, 3] +
        chain 2 • generator (R := ℚ) ![(0 : Label), 1, 3] +
        chain 3 • generator (R := ℚ) ![(0 : Label), 1, 2]) =
    ∑ faceIndex, chain faceIndex • simplexGenerator (radialSingularSimplex faceIndex)
  simp only [map_add, map_smul]
  rw [show (![(1 : Label), 2, 3] : TriangleWord) = canonicalFaceWord 0 by rfl,
    show (![(0 : Label), 2, 3] : TriangleWord) = canonicalFaceWord 1 by rfl,
    show (![(0 : Label), 1, 3] : TriangleWord) = canonicalFaceWord 2 by rfl,
    show (![(0 : Label), 1, 2] : TriangleWord) = canonicalFaceWord 3 by rfl,
    rawWordRealization_canonicalFace, rawWordRealization_canonicalFace,
    rawWordRealization_canonicalFace, rawWordRealization_canonicalFace,
    Fin.sum_univ_four]

/-- The raw geometric receiver of the carried face word is the finite tetrahedral face receiver. -/
theorem rawWordRealization_faceWordCurrent (labels : TriangleWord) :
    rawWordRealization (faceWordCurrent labels) =
      faceRealization (labelledSimplexCarry 2 labels) := by
  rw [faceWordCurrent, rawWordRealization_faceWordRealization,
    labelledSimplexCarry_two]

/-- The word-level fold/constant correction realizes as the existing geometric correction. -/
theorem rawWordRealization_edgeCorrectionWord (first second : Label) :
    rawWordRealization (edgeCorrectionWord first second) =
      rawAffineLabelEdgeCorrection first second := by
  by_cases same : first = second
  · rw [edgeCorrectionWord, rawAffineLabelEdgeCorrection, if_pos same, if_pos same]
    simp [rawWordRealization, generator]
  · by_cases increasing : first < second
    · rw [edgeCorrectionWord, rawAffineLabelEdgeCorrection,
        if_neg same, if_pos increasing, if_neg same, if_pos increasing]
      exact map_zero rawWordRealization
    · rw [edgeCorrectionWord, rawAffineLabelEdgeCorrection,
        if_neg same, if_neg increasing, if_neg same, if_neg increasing,
        map_add]
      simp [rawWordRealization, generator]

/-- The free ordered-word normalization defect corresponding exactly to the existing radial
singular defect. -/
def normalizationDefectWord (labels : TriangleWord) : WordTriangleChain :=
  generator (R := ℚ) labels - faceWordCurrent labels -
    (edgeCorrectionWord ((labels ∘ (0 : Fin 3).succAbove) 0)
        ((labels ∘ (0 : Fin 3).succAbove) 1) -
      edgeCorrectionWord ((labels ∘ (1 : Fin 3).succAbove) 0)
        ((labels ∘ (1 : Fin 3).succAbove) 1) +
      edgeCorrectionWord ((labels ∘ (2 : Fin 3).succAbove) 0)
        ((labels ∘ (2 : Fin 3).succAbove) 1))

/-- [proved-derived; formal-checked] The free ordered-word normalization defect realizes as the
existing singular normalization defect, including every fold and constant reconstruction
occurrence. -/
theorem rawWordRealization_normalizationDefectWord (labels : TriangleWord) :
    rawWordRealization (normalizationDefectWord labels) =
      rawAffineLabelSimplexNormalizationDefect labels := by
  unfold normalizationDefectWord rawAffineLabelSimplexNormalizationDefect
  simp only [map_sub, map_add]
  rw [show rawWordRealization (generator (R := ℚ) labels) =
      simplexGenerator (rawAffineLabelSimplex labels) by
    simp [rawWordRealization, generator],
    rawWordRealization_faceWordCurrent,
    rawWordRealization_edgeCorrectionWord,
    rawWordRealization_edgeCorrectionWord,
    rawWordRealization_edgeCorrectionWord]

/-- [proved-derived; formal-checked] The complete free ordered-word normalization defect is
closed.  Closure is inherited from the finite face-incidence square and the three retained edge
corrections, not from an exhaustive enumeration of word coefficients. -/
theorem normalizationDefectWord_boundary_zero (labels : TriangleWord) :
    triangleBoundary (R := ℚ) (normalizationDefectWord labels) = 0 := by
  unfold normalizationDefectWord
  simp only [map_sub, map_add]
  rw [triangleBoundary_generator, triangleBoundary_faceWordCurrent,
    edgeCorrectionWord_boundary, edgeCorrectionWord_boundary,
    edgeCorrectionWord_boundary]
  have pair0 : (![ (labels ∘ (0 : Fin 3).succAbove) 0,
      (labels ∘ (0 : Fin 3).succAbove) 1] : Fin 2 → Label) =
      labels ∘ (0 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  have pair1 : (![ (labels ∘ (1 : Fin 3).succAbove) 0,
      (labels ∘ (1 : Fin 3).succAbove) 1] : Fin 2 → Label) =
      labels ∘ (1 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  have pair2 : (![ (labels ∘ (2 : Fin 3).succAbove) 0,
      (labels ∘ (2 : Fin 3).succAbove) 1] : Fin 2 → Label) =
      labels ∘ (2 : Fin 3).succAbove := by
    funext index
    fin_cases index <;> rfl
  rw [pair0, pair1, pair2]
  have carry0 : orientedEdgeCarry ((labels ∘ (0 : Fin 3).succAbove) 0)
      ((labels ∘ (0 : Fin 3).succAbove) 1) =
      orientedEdgeCarry (labels 1) (labels 2) := by
    congr 1 <;> rfl
  have carry1 : orientedEdgeCarry ((labels ∘ (1 : Fin 3).succAbove) 0)
      ((labels ∘ (1 : Fin 3).succAbove) 1) =
      orientedEdgeCarry (labels 0) (labels 2) := by
    congr 1 <;> rfl
  have carry2 : orientedEdgeCarry ((labels ∘ (2 : Fin 3).succAbove) 0)
      ((labels ∘ (2 : Fin 3).succAbove) 1) =
      orientedEdgeCarry (labels 0) (labels 1) := by
    congr 1 <;> rfl
  rw [carry0, carry1, carry2]
  abel

/-- The complete normalization defect occupies one fixed tetrahedral boundary chart. -/
theorem normalizationDefectWord_supported (labels : TriangleWord) :
    normalizationDefectWord labels ∈
      Finsupp.supported ℚ ℚ (fixedSupportSet (omittedLabel labels)) := by
  have labelsAbsent : ∀ index, labels index ≠ omittedLabel labels :=
    label_ne_omittedLabel labels
  have labelsInSupport : labels ∈ fixedSupportSet (omittedLabel labels) :=
    labelsAbsent
  have rawSupported : generator (R := ℚ) labels ∈
      Finsupp.supported ℚ ℚ (fixedSupportSet (omittedLabel labels)) := by
    simpa [generator, fixedSupportSet] using
      (Finsupp.single_mem_supported ℚ (1 : ℚ) labelsInSupport)
  have faceSupported := faceWordCurrent_supported labels (omittedLabel labels) labelsAbsent
  have edge0 := edgeCorrectionWord_supported (omittedLabel labels)
    ((labels ∘ (0 : Fin 3).succAbove) 0)
    ((labels ∘ (0 : Fin 3).succAbove) 1)
    (labelsAbsent 1) (labelsAbsent 2)
  have edge1 := edgeCorrectionWord_supported (omittedLabel labels)
    ((labels ∘ (1 : Fin 3).succAbove) 0)
    ((labels ∘ (1 : Fin 3).succAbove) 1)
    (labelsAbsent 0) (labelsAbsent 2)
  have edge2 := edgeCorrectionWord_supported (omittedLabel labels)
    ((labels ∘ (2 : Fin 3).succAbove) 0)
    ((labels ∘ (2 : Fin 3).succAbove) 1)
    (labelsAbsent 0) (labelsAbsent 1)
  unfold normalizationDefectWord
  exact Submodule.sub_mem _ (Submodule.sub_mem _ rawSupported faceSupported)
    (Submodule.add_mem _ (Submodule.sub_mem _ edge0 edge1) edge2)

/-- The closed normalization current with its complete fixed-chart occurrence population. -/
def fixedNormalizationDefect (labels : TriangleWord) :
    FixedSupportedChain (omittedLabel labels) :=
  fixedSupportLift (omittedLabel labels) (normalizationDefectWord labels)
    (normalizationDefectWord_supported labels)

@[simp]
theorem fixedForgetSupport_normalizationDefect (labels : TriangleWord) :
    fixedForgetSupport (omittedLabel labels) (fixedNormalizationDefect labels) =
      normalizationDefectWord labels := by
  exact fixedForgetSupport_lift _ _ _

theorem fixedNormalizationDefect_closed (labels : TriangleWord) :
    triangleBoundary (R := ℚ)
      (fixedForgetSupport (omittedLabel labels) (fixedNormalizationDefect labels)) = 0 := by
  rw [fixedForgetSupport_normalizationDefect,
    normalizationDefectWord_boundary_zero]

@[simp]
theorem fixedRawTriangleReceiver_normalizationDefect (labels : TriangleWord) :
    fixedRawTriangleReceiver (omittedLabel labels) (fixedNormalizationDefect labels) =
      rawAffineLabelSimplexNormalizationDefect labels := by
  rw [fixedRawTriangleReceiver, LinearMap.comp_apply,
    fixedForgetSupport_normalizationDefect,
    rawWordRealization_normalizationDefectWord]

/-- The degree-three geometric current which fills the complete normalization defect.  Its fixed
omitted-coordinate chart is retained by `fixedNormalizationDefect`; no per-occurrence choice is
made after currents have been summed. -/
def rawAffineLabelSimplexNormalizationFiller (labels : TriangleWord) : SphereChain 3 :=
  fixedGeometricPrefixReceiver (labelApex labels) (omittedLabel labels)
    (labelApex_ne_omittedLabel labels) (fixedNormalizationDefect labels)

/-- [proved-derived; formal-checked] The raw affine normalization defect is an exact singular
boundary.  This removes the formerly admitted local filler hypothesis. -/
theorem rawAffineLabelSimplexNormalizationFiller_boundary (labels : TriangleWord) :
    SphereSingularChainComplex.d 3 2
        (rawAffineLabelSimplexNormalizationFiller labels) =
      rawAffineLabelSimplexNormalizationDefect labels := by
  rw [rawAffineLabelSimplexNormalizationFiller,
    fixedGeometricPrefixReceiver_boundary_of_closed]
  · exact fixedRawTriangleReceiver_normalizationDefect labels
  · exact fixedNormalizationDefect_closed labels

/-- The complete geometric degree-two source of one label normalization passage. -/
def rawAffineLabelSimplexNormalizationSource (labels : TriangleWord) : SphereChain 2 :=
  faceRealization (labelledSimplexCarry 2 labels) +
    (rawAffineLabelEdgeCorrection ((labels ∘ (0 : Fin 3).succAbove) 0)
        ((labels ∘ (0 : Fin 3).succAbove) 1) -
      rawAffineLabelEdgeCorrection ((labels ∘ (1 : Fin 3).succAbove) 0)
        ((labels ∘ (1 : Fin 3).succAbove) 1) +
      rawAffineLabelEdgeCorrection ((labels ∘ (2 : Fin 3).succAbove) 0)
        ((labels ∘ (2 : Fin 3).succAbove) 1))

/-- [proved-derived; formal-checked] Label normalization is an actual elementary boundary holon:
the occurrence retains its ordered word and every fold/constant correction; the receiver is the
fixed-chart prefix filler. -/
def affineLabelSimplexNormalizationHolon :
    Soma.Holonics.BoundaryHolon (SphereChain 2) (SphereChain 3) where
  Occurrence := TriangleWord
  source labels := rawAffineLabelSimplexNormalizationSource labels
  target labels := simplexGenerator (rawAffineLabelSimplex labels)
  receive labels := rawAffineLabelSimplexNormalizationFiller labels
  boundary := (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom
  returnsBoundary := by
    intro labels
    change SphereSingularChainComplex.d 3 2
        (rawAffineLabelSimplexNormalizationFiller labels) =
      simplexGenerator (rawAffineLabelSimplex labels) -
        rawAffineLabelSimplexNormalizationSource labels
    rw [rawAffineLabelSimplexNormalizationFiller_boundary]
    unfold rawAffineLabelSimplexNormalizationDefect
      rawAffineLabelSimplexNormalizationSource
    abel

end Soma.Holonics.Millennium.HodgeLabelWordContraction
