import ElementaryHolonics.Millennium.HodgeTetrahedralCarrierAssembly

/-!
# Oriented tetrahedral labels carry finite simplicial currents

This file isolates the finite algebra needed by the normalized sphere carrier.  A tuple of
tetrahedral vertex labels carries its oriented vertex, edge, or face chain.  Repeated labels cancel
automatically.  In every degree the finite boundary is the complete alternating population of the
carried faces; in degree three this is the exact cancellation of the four oriented triangles around
a labelled tetrahedron.

The construction is deliberately independent of a geometric cover.  A later owner must produce
labels from actual sphere occurrences and prove compatibility under source faces.  This file proves
that once those labels exist, their induced finite current already has the required chain law.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry

set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

open CategoryTheory
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly

/-- The oriented edge from `initial` to `terminal`, expressed in the globally increasing edge
basis.  Equal endpoints return zero, so degeneracy is retained as exact cancellation. -/
def orientedEdgeCarry (initial terminal : TetraVertex) : EdgeChain :=
  fun edge =>
    if edgeInitial edge = initial ∧ edgeTerminal edge = terminal then 1
    else if edgeInitial edge = terminal ∧ edgeTerminal edge = initial then -1
    else 0

/-- Terminal minus initial is the exact vertex boundary of an oriented labelled edge. -/
theorem vertexBoundary_orientedEdgeCarry (initial terminal : TetraVertex) :
    vertexBoundary (orientedEdgeCarry initial terminal) =
      vertexUnit terminal - vertexUnit initial := by
  funext vertex
  fin_cases initial <;> fin_cases terminal <;> fin_cases vertex <;>
    simp [vertexBoundary, orientedEdgeCarry, edgeInitial, edgeTerminal, vertexUnit,
      Fin.ext_iff]

/-- The alternating determinant coefficient of the ordered triple `(a,b,c)` in the ordered
coordinate plane `(i,j,k)`. -/
def triangleOrientation (a b c i j k : TetraVertex) : ℚ :=
  (if a = i then 1 else 0) *
      ((if b = j then 1 else 0) * (if c = k then 1 else 0) -
        (if b = k then 1 else 0) * (if c = j then 1 else 0)) -
    (if a = j then 1 else 0) *
      ((if b = i then 1 else 0) * (if c = k then 1 else 0) -
        (if b = k then 1 else 0) * (if c = i then 1 else 0)) +
    (if a = k then 1 else 0) *
      ((if b = i then 1 else 0) * (if c = j then 1 else 0) -
        (if b = j then 1 else 0) * (if c = i then 1 else 0))

/-- The oriented triangle on three tetrahedral labels.  Its single possible nonzero coordinate is
the face opposite the omitted vertex. -/
def orientedFaceCarry (a b c : TetraVertex) : FaceChain
  | 0 => triangleOrientation a b c 1 2 3
  | 1 => triangleOrientation a b c 0 2 3
  | 2 => triangleOrientation a b c 0 1 3
  | 3 => triangleOrientation a b c 0 1 2

/-- The boundary of an oriented labelled triangle is its three ordered edge occurrences. -/
theorem faceBoundary_orientedFaceCarry (a b c : TetraVertex) :
    faceBoundary (orientedFaceCarry a b c) =
      orientedEdgeCarry b c - orientedEdgeCarry a c + orientedEdgeCarry a b := by
  funext edge
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases edge <;>
    simp [faceBoundary, boundaryColumn, orientedFaceCarry, triangleOrientation,
      orientedEdgeCarry, edgeInitial, edgeTerminal, Fin.sum_univ_four, Fin.ext_iff]

/-- Repetition makes an oriented labelled face vanish. -/
theorem orientedFaceCarry_repeat_first (a c : TetraVertex) :
    orientedFaceCarry a a c = 0 := by
  funext face
  fin_cases a <;> fin_cases c <;> fin_cases face <;>
    simp [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

theorem orientedFaceCarry_repeat_last (a b : TetraVertex) :
    orientedFaceCarry a b b = 0 := by
  funext face
  fin_cases a <;> fin_cases b <;> fin_cases face <;>
    simp [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

theorem orientedFaceCarry_repeat_ends (a b : TetraVertex) :
    orientedFaceCarry a b a = 0 := by
  funext face
  fin_cases a <;> fin_cases b <;> fin_cases face <;>
    simp [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

/-- Exchanging two adjacent labels reverses the oriented face current. -/
theorem orientedFaceCarry_swap_first (a b c : TetraVertex) :
    orientedFaceCarry b a c = -orientedFaceCarry a b c := by
  funext face
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases face <;>
    simp [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

theorem orientedFaceCarry_swap_last (a b c : TetraVertex) :
    orientedFaceCarry a c b = -orientedFaceCarry a b c := by
  funext face
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases face <;>
    simp [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

theorem orientedFaceCarry_cycle (a b c : TetraVertex) :
    orientedFaceCarry c a b = orientedFaceCarry a b c := by
  rw [orientedFaceCarry_swap_first, orientedFaceCarry_swap_last]
  simp

/-- The admissibility condition which the geometric star cover must return for every source
three-simplex: at least two of its four vertex labels agree. -/
def FourLabelsAdmissible (a b c d : TetraVertex) : Prop :=
  a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d

/-- Four admissible labelled vertices have zero alternating triangle boundary.  The theorem is
false without `FourLabelsAdmissible`: four distinct labels carry the tetrahedral fundamental
cycle. -/
theorem alternating_orientedFaceCarry_zero_of_admissible (a b c d : TetraVertex)
    (admissible : FourLabelsAdmissible a b c d) :
    orientedFaceCarry b c d - orientedFaceCarry a c d +
        orientedFaceCarry a b d - orientedFaceCarry a b c = 0 := by
  rcases admissible with hab | hac | had | hbc | hbd | hcd
  · subst b
    rw [orientedFaceCarry_repeat_first, orientedFaceCarry_repeat_first]
    abel
  · subst c
    rw [orientedFaceCarry_repeat_first, orientedFaceCarry_repeat_ends,
      orientedFaceCarry_swap_first]
    abel
  · subst d
    rw [orientedFaceCarry_repeat_ends, orientedFaceCarry_repeat_ends]
    rw [show orientedFaceCarry b c a = orientedFaceCarry a b c by
      exact (orientedFaceCarry_cycle b c a).symm]
    abel
  · subst c
    rw [orientedFaceCarry_repeat_first, orientedFaceCarry_repeat_last]
    abel
  · subst d
    rw [orientedFaceCarry_repeat_ends, orientedFaceCarry_repeat_last,
      orientedFaceCarry_swap_last]
    abel
  · subst d
    rw [orientedFaceCarry_repeat_last, orientedFaceCarry_repeat_last]
    abel

/-- The finite chain carried by an ordered tuple of tetrahedral vertex labels. -/
def labelledSimplexCarry : (degree : ℕ) →
    (Fin (degree + 1) → TetraVertex) → tetrahedralChainComplex.X degree
  | 0, labels => vertexUnit (labels 0)
  | 1, labels => orientedEdgeCarry (labels 0) (labels 1)
  | 2, labels => orientedFaceCarry (labels 0) (labels 1) (labels 2)
  | _ + 3, _ => 0

@[simp]
theorem labelledSimplexCarry_zero (labels : Fin 1 → TetraVertex) :
    labelledSimplexCarry 0 labels = vertexUnit (labels 0) := rfl

@[simp]
theorem labelledSimplexCarry_one (labels : Fin 2 → TetraVertex) :
    labelledSimplexCarry 1 labels = orientedEdgeCarry (labels 0) (labels 1) := rfl

@[simp]
theorem labelledSimplexCarry_two (labels : Fin 3 → TetraVertex) :
    labelledSimplexCarry 2 labels = orientedFaceCarry (labels 0) (labels 1) (labels 2) := rfl

@[simp]
theorem labelledSimplexCarry_add_three (degree : ℕ)
    (labels : Fin (degree + 4) → TetraVertex) :
    labelledSimplexCarry (degree + 3) labels = 0 := by
  rfl

/-- Restrict an ordered label tuple along the `i`th simplicial face. -/
def faceLabels {degree : ℕ} (labels : Fin (degree + 2) → TetraVertex)
    (i : Fin (degree + 2)) : Fin (degree + 1) → TetraVertex :=
  labels ∘ i.succAbove

/-- The complete finite simplicial boundary law for labelled tetrahedral currents. -/
theorem labelledSimplexCarry_boundary (degree : ℕ)
    (labels : Fin (degree + 2) → TetraVertex)
    (degreeThreeAdmissible : degree = 2 →
      FourLabelsAdmissible (labels 0) (labels 1) (labels 2) (labels 3)) :
    tetrahedralChainComplex.d (degree + 1) degree
        (labelledSimplexCarry (degree + 1) labels) =
      ∑ i : Fin (degree + 2), (-1 : ℚ) ^ (i : ℕ) •
        labelledSimplexCarry degree (faceLabels labels i) := by
  cases degree with
  | zero =>
      rw [tetrahedralChainComplex_d_zero]
      change vertexBoundary (orientedEdgeCarry (labels 0) (labels 1)) =
        ∑ i : Fin 2, (-1 : ℚ) ^ (i : ℕ) •
          vertexUnit (labels (i.succAbove 0))
      rw [vertexBoundary_orientedEdgeCarry, Fin.sum_univ_two]
      simp [faceLabels, Fin.succAbove, Fin.ext_iff]
      rw [sub_eq_add_neg]
  | succ degree =>
      cases degree with
      | zero =>
          rw [tetrahedralChainComplex_d_one]
          change faceBoundary (orientedFaceCarry (labels 0) (labels 1) (labels 2)) =
            ∑ i : Fin 3, (-1 : ℚ) ^ (i : ℕ) •
              orientedEdgeCarry (labels (i.succAbove 0)) (labels (i.succAbove 1))
          rw [faceBoundary_orientedFaceCarry, Fin.sum_univ_three]
          simp [faceLabels, Fin.succAbove, Fin.ext_iff]
          rw [sub_eq_add_neg]
      | succ degree =>
          cases degree with
          | zero =>
              rw [tetrahedralChainComplex_d_three_two]
              change (0 : FaceChain) =
                ∑ i : Fin 4, (-1 : ℚ) ^ (i : ℕ) •
                  orientedFaceCarry (labels (i.succAbove 0))
                    (labels (i.succAbove 1)) (labels (i.succAbove 2))
              rw [Fin.sum_univ_four]
              simp [faceLabels, Fin.succAbove, Fin.ext_iff]
              rw [show (-1 : ℚ) ^ 3 = -1 by norm_num]
              simpa [sub_eq_add_neg] using
                (alternating_orientedFaceCarry_zero_of_admissible
                (labels 0) (labels 1) (labels 2) (labels 3)
                (degreeThreeAdmissible rfl)).symm
          | succ degree =>
              have hd : tetrahedralChainComplex.d
                    (degree + 1 + 1 + 1 + 1) (degree + 1 + 1 + 1) = 0 := by
                change ChainComplex.of.d tetrahedralChainModule tetrahedralDifferential
                    (degree + 1 + 1 + 1 + 1) (degree + 1 + 1 + 1) = 0
                rw [ChainComplex.of_d tetrahedralChainModule tetrahedralDifferential
                  (degree + 1 + 1 + 1)]
                rfl
              rw [hd]
              simp [labelledSimplexCarry]

/-- A tetrahedral vertex label on every singular simplex, compatible with every source face.  The
degree-three field records the exact nerve condition exposed by the finite falsifier: no admitted
source tetrahedron may carry four distinct target labels. -/
structure CompatibleTetrahedralLabeling where
  vertexLabel : (degree : ℕ) → SphereSingularSimplex degree →
    Fin (degree + 1) → TetraVertex
  face_compat : ∀ (degree : ℕ) (simplex : SphereSingularSimplex (degree + 1))
      (face : Fin (degree + 2)),
    vertexLabel degree (simplexFace face simplex) =
      vertexLabel (degree + 1) simplex ∘ face.succAbove
  degreeThree_admissible : ∀ simplex : SphereSingularSimplex 3,
    FourLabelsAdmissible
      (vertexLabel 3 simplex 0) (vertexLabel 3 simplex 1)
      (vertexLabel 3 simplex 2) (vertexLabel 3 simplex 3)

namespace CompatibleTetrahedralLabeling

/-- A compatible label field carries each singular occurrence into the finite tetrahedral body. -/
def carry (labeling : CompatibleTetrahedralLabeling) (degree : ℕ)
    (simplex : SphereSingularSimplex degree) : tetrahedralChainComplex.X degree :=
  labelledSimplexCarry degree (labeling.vertexLabel degree simplex)

/-- The label face law and fourfold-intersection obstruction assemble directly into the abstract
face-natural carrier required by the Hodge detector. -/
def faceNaturalCarrier (labeling : CompatibleTetrahedralLabeling) : FaceNaturalCarrier where
  carry := labeling.carry
  boundary degree simplex := by
    change tetrahedralChainComplex.d (degree + 1) degree
        (labelledSimplexCarry (degree + 1)
          (labeling.vertexLabel (degree + 1) simplex)) = _
    rw [labelledSimplexCarry_boundary degree
      (labeling.vertexLabel (degree + 1) simplex)]
    · apply Finset.sum_congr rfl
      intro face _
      change (-1 : ℚ) ^ (face : ℕ) •
          labelledSimplexCarry degree
            (faceLabels (labeling.vertexLabel (degree + 1) simplex) face) =
        (-1 : ℚ) ^ (face : ℕ) •
          labelledSimplexCarry degree
            (labeling.vertexLabel degree (simplexFace face simplex))
      rw [show faceLabels (labeling.vertexLabel (degree + 1) simplex) face =
          labeling.vertexLabel degree (simplexFace face simplex) by
        simpa [faceLabels] using (labeling.face_compat degree simplex face).symm]
    · intro hdegree
      subst degree
      exact labeling.degreeThree_admissible simplex

/-- Canonical labels on a radial face are the three tetrahedral vertices other than that face. -/
def RadialNormalized (labeling : CompatibleTetrahedralLabeling) : Prop :=
  ∀ face : Fin 4,
    labeling.vertexLabel 2 (radialSingularSimplex face) = face.succAbove

/-- The canonical ordered complement of a vertex carries its addressed tetrahedral face atom. -/
theorem orientedFaceCarry_succAbove (face : Fin 4) :
    orientedFaceCarry (face.succAbove 0) (face.succAbove 1) (face.succAbove 2) =
      faceUnit face := by
  funext observed
  fin_cases face <;> fin_cases observed <;>
    simp [orientedFaceCarry, triangleOrientation, faceUnit, Fin.succAbove, Fin.ext_iff]

/-- Canonical radial labels are exactly the four normalization equations required by the existing
reduction assembly. -/
theorem faceNaturalCarrier_normalized (labeling : CompatibleTetrahedralLabeling)
    (normalized : labeling.RadialNormalized) :
    labeling.faceNaturalCarrier.NormalizedOnRadialFaces := by
  intro face
  change labelledSimplexCarry 2
      (labeling.vertexLabel 2 (radialSingularSimplex face)) = faceUnit face
  rw [normalized face]
  exact orientedFaceCarry_succAbove face

/-- A compatible, admissible, radially normalized label field returns the actual degree-two
tetrahedral receiver. -/
def degreeTwoReceiver (labeling : CompatibleTetrahedralLabeling)
    (normalized : labeling.RadialNormalized) :
    HodgeSphereFundamentalDetector.TetrahedralDegreeTwoReceiver :=
  labeling.faceNaturalCarrier.degreeTwoReceiver
    (labeling.faceNaturalCarrier_normalized normalized)

end CompatibleTetrahedralLabeling

section Audit

#print axioms vertexBoundary_orientedEdgeCarry
#print axioms faceBoundary_orientedFaceCarry
#print axioms alternating_orientedFaceCarry_zero_of_admissible
#print axioms labelledSimplexCarry_boundary
#print axioms CompatibleTetrahedralLabeling.faceNaturalCarrier
#print axioms CompatibleTetrahedralLabeling.faceNaturalCarrier_normalized
#print axioms CompatibleTetrahedralLabeling.degreeTwoReceiver

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
