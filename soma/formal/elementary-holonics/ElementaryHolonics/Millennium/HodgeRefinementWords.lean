import ElementaryHolonics.Millennium.HodgeBarycentricTetrahedron
import ElementaryHolonics.Millennium.HodgeBarycentricTriangleSubdivision
import ElementaryHolonics.Millennium.HodgeBarycentricEdgeSubdivision

/-!
# Fixed-depth refinement words

This file makes the finite address population of a repeated barycentric refinement explicit.  A
word is a function on `Fin scale`; its zero coordinate is the newest local address.  Thus
`List.ofFn word` is already in the order required by the serial composition law: the tail is the
older carrier and the head is the newly selected child.  The construction is finite, exact, and
retains every signed occurrence; no list-length subtype or numerical approximation is introduced.

Truth status: definitions are `[definition]`; the expansion laws below are
`[proved-derived; formal-checked]` relative to the exact one-step subdivision laws imported above.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinementWords

set_option maxHeartbeats 2000000

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron

abbrev TetraWord (scale : ℕ) := Fin scale → BarycentricTetrahedronAddress
abbrev TriangleWord (scale : ℕ) := Fin scale → BarycentricTriangleAddress
abbrev EdgeWord (scale : ℕ) := Fin scale → Fin 2

def tetraWordList {scale : ℕ} (word : TetraWord scale) :
    List BarycentricTetrahedronAddress := List.ofFn word

def triangleWordList {scale : ℕ} (word : TriangleWord scale) :
    List BarycentricTriangleAddress := List.ofFn word

def edgeWordList {scale : ℕ} (word : EdgeWord scale) : List (Fin 2) := List.ofFn word

def finSuccEquiv {α : Type} (scale : ℕ) :
    (Fin (scale + 1) → α) ≃ α × (Fin scale → α) where
  toFun word := (word 0, fun index => word index.succ)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv word := by
    funext index
    exact Fin.cases rfl (fun tail => rfl) index
  right_inv pair := by
    cases pair with
    | mk head tail =>
        rfl

def prodFinSuccEquiv {α : Type} (scale : ℕ) :
    (Fin scale → α) × α ≃ (Fin (scale + 1) → α) where
  toFun pair := Fin.cons pair.2 pair.1
  invFun word := (fun index => word index.succ, word 0)
  left_inv pair := by
    cases pair with
    | mk tail head => rfl
  right_inv word := by
    funext index
    exact Fin.cases rfl (fun tail => rfl) index

def tetraWordSubsimplex {scale : ℕ} (word : TetraWord scale)
    (simplex : SphereSingularSimplex 3) : SphereSingularSimplex 3 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 3)) simplex).comp
          (barycentricTetrahedronWordMap (tetraWordList word)))

def triangleWordSubsimplex {scale : ℕ} (word : TriangleWord scale)
    (simplex : SphereSingularSimplex 2) : SphereSingularSimplex 2 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 2)) simplex).comp
          (barycentricTriangleWordMap (triangleWordList word)))

def edgeWordMap : List (Fin 2) → C(Segment, Segment)
  | [] => ContinuousMap.id Segment
  | address :: tail => (edgeWordMap tail).comp (edgeConeMap address)

def edgeWordSubsimplex {scale : ℕ} (word : EdgeWord scale)
    (simplex : SphereSingularSimplex 1) : SphereSingularSimplex 1 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).symm
      ((TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1)) simplex).comp
          (edgeWordMap (edgeWordList word)))

def tetraAddressSign (address : BarycentricTetrahedronAddress) : ℚ :=
  (-1 : ℚ) ^ ((address.1 : ℕ) + (address.2.1 : ℕ) + (address.2.2 : ℕ))

def triangleAddressSign (address : BarycentricTriangleAddress) : ℚ :=
  (-1 : ℚ) ^ ((address.1 : ℕ) + (address.2 : ℕ))

def edgeAddressSign (address : Fin 2) : ℚ := (-1 : ℚ) ^ (address : ℕ)

def tetraWordSign {scale : ℕ} (word : TetraWord scale) : ℚ :=
  ∏ index : Fin scale, tetraAddressSign (word index)

def triangleWordSign {scale : ℕ} (word : TriangleWord scale) : ℚ :=
  ∏ index : Fin scale, triangleAddressSign (word index)

def edgeWordSign {scale : ℕ} (word : EdgeWord scale) : ℚ :=
  ∏ index : Fin scale, edgeAddressSign (word index)

theorem edgeSubdivision_as_address_sum (simplex : SphereSingularSimplex 1) :
    barycentricEdgeSubdivision simplex =
      ∑ address : Fin 2, edgeAddressSign address •
        simplexGenerator (barycentricEdgeSubsimplex address simplex) := by
  rfl

theorem triangleSubdivision_as_address_sum (simplex : SphereSingularSimplex 2) :
    barycentricTriangleSubdivision simplex =
      ∑ address : BarycentricTriangleAddress, triangleAddressSign address •
        simplexGenerator (barycentricTriangleSubsimplex address.1 address.2 simplex) := by
  rw [barycentricTriangleSubdivision]
  symm
  rw [Fintype.sum_prod_type]
  simp [triangleAddressSign]

theorem tetraSubdivision_as_address_sum (simplex : SphereSingularSimplex 3) :
    barycentricTetrahedronSubdivision simplex =
      ∑ address : BarycentricTetrahedronAddress, tetraAddressSign address •
        simplexGenerator
          (barycentricTetrahedronSubsimplex address.1 address.2.1 address.2.2 simplex) := by
  rw [barycentricTetrahedronSubdivision]
  symm
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [tetraAddressSign]

@[simp] theorem tetraWordList_length {scale : ℕ} (word : TetraWord scale) :
    (tetraWordList word).length = scale := by simp [tetraWordList]

@[simp] theorem triangleWordList_length {scale : ℕ} (word : TriangleWord scale) :
    (triangleWordList word).length = scale := by simp [triangleWordList]

@[simp] theorem edgeWordList_length {scale : ℕ} (word : EdgeWord scale) :
    (edgeWordList word).length = scale := by simp [edgeWordList]

@[simp] theorem tetraWordSign_cons {scale : ℕ}
    (head : BarycentricTetrahedronAddress) (tail : TetraWord scale) :
    tetraWordSign (Fin.cons head tail) =
      tetraAddressSign head * tetraWordSign tail := by
  simp [tetraWordSign, Fin.prod_univ_succ]

@[simp] theorem triangleWordSign_cons {scale : ℕ}
    (head : BarycentricTriangleAddress) (tail : TriangleWord scale) :
    triangleWordSign (Fin.cons head tail) =
      triangleAddressSign head * triangleWordSign tail := by
  simp [triangleWordSign, Fin.prod_univ_succ]

@[simp] theorem edgeWordSign_cons {scale : ℕ}
    (head : Fin 2) (tail : EdgeWord scale) :
    edgeWordSign (Fin.cons head tail) =
      edgeAddressSign head * edgeWordSign tail := by
  simp [edgeWordSign, Fin.prod_univ_succ]

theorem tetraWordSubsimplex_cons {scale : ℕ}
    (head : BarycentricTetrahedronAddress) (tail : TetraWord scale)
    (simplex : SphereSingularSimplex 3) :
    tetraWordSubsimplex (Fin.cons head tail) simplex =
      barycentricTetrahedronSubsimplex head.1 head.2.1 head.2.2
        (tetraWordSubsimplex tail simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 3))).injective
  simp only [tetraWordSubsimplex, tetraWordList, List.ofFn_cons,
    barycentricTetrahedronWordMap, barycentricTetrahedronSubsimplex,
    Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

theorem triangleWordSubsimplex_cons {scale : ℕ}
    (head : BarycentricTriangleAddress) (tail : TriangleWord scale)
    (simplex : SphereSingularSimplex 2) :
    triangleWordSubsimplex (Fin.cons head tail) simplex =
      barycentricTriangleSubsimplex head.1 head.2
        (triangleWordSubsimplex tail simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 2))).injective
  simp only [triangleWordSubsimplex, triangleWordList, List.ofFn_cons,
    barycentricTriangleWordMap, barycentricTriangleSubsimplex,
    Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

theorem edgeWordSubsimplex_cons {scale : ℕ}
    (head : Fin 2) (tail : EdgeWord scale) (simplex : SphereSingularSimplex 1) :
    edgeWordSubsimplex (Fin.cons head tail) simplex =
      barycentricEdgeSubsimplex head (edgeWordSubsimplex tail simplex) := by
  apply (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 1))).injective
  simp only [edgeWordSubsimplex, edgeWordList, List.ofFn_cons,
    edgeWordMap, barycentricEdgeSubsimplex, Equiv.apply_symm_apply]
  rw [ContinuousMap.comp_assoc]

def iteratedBarycentricEdgeSubdivision : ℕ → SphereChain 1 → SphereChain 1
  | 0 => id
  | scale + 1 => fun chain =>
      barycentricEdgeSubdivisionMorphism
        (iteratedBarycentricEdgeSubdivision scale chain)

/-- [proved-derived; formal-checked] One edge refinement preserves its exact endpoint boundary. -/
theorem boundary_barycentricEdgeSubdivisionMorphism (chain : SphereChain 1) :
    SphereSingularChainComplex.d 1 0
        (barycentricEdgeSubdivisionMorphism chain) =
      SphereSingularChainComplex.d 1 0 chain := by
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun morphism : SphereSingularChainComplex.X 1 ⟶
      SphereSingularChainComplex.X 0 => morphism chain)
      barycentricEdgeSubdivisionMorphism_comp_boundary

/-- [proved-derived; formal-checked] Every iterated edge refinement preserves its original
terminal-minus-initial boundary. -/
theorem boundary_iteratedBarycentricEdgeSubdivision
    (scale : ℕ) (chain : SphereChain 1) :
    SphereSingularChainComplex.d 1 0
        (iteratedBarycentricEdgeSubdivision scale chain) =
      SphereSingularChainComplex.d 1 0 chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedBarycentricEdgeSubdivision,
        boundary_barycentricEdgeSubdivisionMorphism, inductionHypothesis]

/-- [proved-derived; formal-checked] Repeated triangle refinement returns exactly the matching
repeated edge refinement of its boundary. -/
theorem boundary_iteratedBarycentricTriangleSubdivision
    (scale : ℕ) (chain : SphereChain 2) :
    SphereSingularChainComplex.d 2 1
        (iteratedBarycentricTriangleSubdivision scale chain) =
      iteratedBarycentricEdgeSubdivision scale
        (SphereSingularChainComplex.d 2 1 chain) := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      rw [iteratedBarycentricTriangleSubdivision,
        boundary_barycentricTriangleSubdivisionMorphism,
        inductionHypothesis, iteratedBarycentricEdgeSubdivision]

theorem edgeWordExpansion (scale : ℕ) (simplex : SphereSingularSimplex 1) :
    iteratedBarycentricEdgeSubdivision scale (simplexGenerator simplex) =
      ∑ word : EdgeWord scale,
        edgeWordSign word • simplexGenerator (edgeWordSubsimplex word simplex) := by
  induction scale with
  | zero =>
      simp [iteratedBarycentricEdgeSubdivision, edgeWordSign, edgeWordSubsimplex,
        edgeWordList, edgeWordMap]
  | succ scale inductionHypothesis =>
      simp only [iteratedBarycentricEdgeSubdivision]
      rw [inductionHypothesis, map_sum]
      simp only [map_smul, barycentricEdgeSubdivisionMorphism_simplexGenerator]
      simp_rw [edgeSubdivision_as_address_sum, Finset.smul_sum]
      calc
        (∑ old : EdgeWord scale, ∑ head : Fin 2,
          edgeWordSign old • ((-1 : ℚ) ^ (head : ℕ) •
            simplexGenerator (barycentricEdgeSubsimplex head
              (edgeWordSubsimplex old simplex)))) =
          ∑ pair : (EdgeWord scale) × Fin 2,
            edgeWordSign pair.1 • ((-1 : ℚ) ^ (pair.2 : ℕ) •
              simplexGenerator (barycentricEdgeSubsimplex pair.2
                (edgeWordSubsimplex pair.1 simplex))) := by
          symm
          rw [Fintype.sum_prod_type]
        _ = ∑ word : EdgeWord (scale + 1),
            edgeWordSign word • simplexGenerator (edgeWordSubsimplex word simplex) := by
          apply Fintype.sum_equiv (prodFinSuccEquiv (α := Fin 2) scale)
          intro pair
          cases pair with
          | mk tail head =>
              change edgeWordSign tail • ((-1 : ℚ) ^ (head : ℕ) •
                simplexGenerator (barycentricEdgeSubsimplex head
                  (edgeWordSubsimplex tail simplex))) =
                edgeWordSign (Fin.cons head tail) •
                  simplexGenerator (edgeWordSubsimplex (Fin.cons head tail) simplex)
              rw [edgeWordSign_cons, edgeWordSubsimplex_cons, ← mul_smul]
              simp [edgeAddressSign, mul_comm]

theorem triangleWordExpansion (scale : ℕ) (simplex : SphereSingularSimplex 2) :
    iteratedBarycentricTriangleSubdivision scale (simplexGenerator simplex) =
      ∑ word : TriangleWord scale,
        triangleWordSign word • simplexGenerator (triangleWordSubsimplex word simplex) := by
  induction scale with
  | zero =>
      simp [iteratedBarycentricTriangleSubdivision, triangleWordSign,
        triangleWordSubsimplex, triangleWordList, barycentricTriangleWordMap]
  | succ scale inductionHypothesis =>
      simp only [iteratedBarycentricTriangleSubdivision]
      rw [inductionHypothesis, map_sum]
      simp only [map_smul, barycentricTriangleSubdivisionMorphism_simplexGenerator]
      simp_rw [triangleSubdivision_as_address_sum, Finset.smul_sum]
      calc
        (∑ old : TriangleWord scale, ∑ head : BarycentricTriangleAddress,
          triangleWordSign old •
            (triangleAddressSign head •
              simplexGenerator (barycentricTriangleSubsimplex head.1 head.2
                (triangleWordSubsimplex old simplex)))) =
          ∑ pair : (TriangleWord scale) × BarycentricTriangleAddress,
            triangleWordSign pair.1 •
              (triangleAddressSign pair.2 •
                simplexGenerator (barycentricTriangleSubsimplex pair.2.1 pair.2.2
                  (triangleWordSubsimplex pair.1 simplex))) := by
          symm
          rw [Fintype.sum_prod_type]
        _ = ∑ word : TriangleWord (scale + 1),
            triangleWordSign word • simplexGenerator (triangleWordSubsimplex word simplex) := by
          apply Fintype.sum_equiv
            (prodFinSuccEquiv (α := BarycentricTriangleAddress) scale)
          intro pair
          cases pair with
          | mk tail head =>
              change triangleWordSign tail • (triangleAddressSign head •
                simplexGenerator (barycentricTriangleSubsimplex head.1 head.2
                  (triangleWordSubsimplex tail simplex))) =
                triangleWordSign (Fin.cons head tail) •
                  simplexGenerator (triangleWordSubsimplex (Fin.cons head tail) simplex)
              rw [triangleWordSign_cons, triangleWordSubsimplex_cons, ← mul_smul]
              simp [mul_comm]

theorem tetraWordExpansion (scale : ℕ) (simplex : SphereSingularSimplex 3) :
    iteratedBarycentricTetrahedronSubdivision scale (simplexGenerator simplex) =
      ∑ word : TetraWord scale,
        tetraWordSign word • simplexGenerator (tetraWordSubsimplex word simplex) := by
  induction scale with
  | zero =>
      simp [iteratedBarycentricTetrahedronSubdivision, tetraWordSign,
        tetraWordSubsimplex, tetraWordList, barycentricTetrahedronWordMap]
  | succ scale inductionHypothesis =>
      simp only [iteratedBarycentricTetrahedronSubdivision]
      rw [inductionHypothesis, map_sum]
      simp only [map_smul, barycentricTetrahedronSubdivisionMorphism_simplexGenerator]
      simp_rw [tetraSubdivision_as_address_sum, Finset.smul_sum]
      calc
        (∑ old : TetraWord scale, ∑ head : BarycentricTetrahedronAddress,
          tetraWordSign old •
            (tetraAddressSign head •
              simplexGenerator (barycentricTetrahedronSubsimplex head.1 head.2.1 head.2.2
                (tetraWordSubsimplex old simplex)))) =
          ∑ pair : (TetraWord scale) × BarycentricTetrahedronAddress,
            tetraWordSign pair.1 •
              (tetraAddressSign pair.2 •
                simplexGenerator (barycentricTetrahedronSubsimplex pair.2.1 pair.2.2.1 pair.2.2.2
                  (tetraWordSubsimplex pair.1 simplex))) := by
          symm
          rw [Fintype.sum_prod_type]
        _ = ∑ word : TetraWord (scale + 1),
            tetraWordSign word • simplexGenerator (tetraWordSubsimplex word simplex) := by
          apply Fintype.sum_equiv
            (prodFinSuccEquiv (α := BarycentricTetrahedronAddress) scale)
          intro pair
          cases pair with
          | mk tail head =>
              change tetraWordSign tail • (tetraAddressSign head •
                simplexGenerator
                  (barycentricTetrahedronSubsimplex head.1 head.2.1 head.2.2
                    (tetraWordSubsimplex tail simplex))) =
                tetraWordSign (Fin.cons head tail) •
                  simplexGenerator (tetraWordSubsimplex (Fin.cons head tail) simplex)
              rw [tetraWordSign_cons, tetraWordSubsimplex_cons, ← mul_smul]
              simp [mul_comm]

section Audit

#print axioms edgeWordExpansion
#print axioms boundary_iteratedBarycentricEdgeSubdivision
#print axioms boundary_iteratedBarycentricTriangleSubdivision
#print axioms triangleWordExpansion
#print axioms tetraWordExpansion

end Audit

end Soma.Holonics.Millennium.HodgeRefinementWords
