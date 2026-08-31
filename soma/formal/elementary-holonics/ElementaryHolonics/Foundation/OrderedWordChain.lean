import ElementaryHolonics.Foundation.Holon

/-!
# Ordered word chains

An ordered word is an occurrence, not a set of vertices.  Deleting one addressed entry gives its
boundary face; prefixing one addressed apex gives its elementary cone.  Repetitions, reversals,
and diagonal words remain distinct generators throughout.

This file records the degree-two contraction needed by several local-to-global passages without
attaching it to any one classical subject.  The realization of a word into geometry is deliberately
left to the receiving construction.
-/

noncomputable section

namespace Soma.Holonics.OrderedWordChain

/-- [definition] An addressed word of a fixed positive length. -/
abbrev Word (α : Type*) (length : ℕ) := Fin length → α

/-- [definition] The free `R`-current of addressed words. -/
abbrev Chain (R α : Type*) [Zero R] (length : ℕ) := Word α length →₀ R

/-- [definition] One retained word occurrence. -/
def generator {R α : Type*} [CommRing R] {length : ℕ} (word : Word α length) :
    Chain R α length :=
  Finsupp.single word 1

/-- [definition] Delete one addressed entry of a word. -/
def face {α : Type*} {length : ℕ} (word : Word α (length + 1))
    (omitted : Fin (length + 1)) : Word α length :=
  word ∘ omitted.succAbove

/-- [definition] The complete alternating edge-word boundary of one triangle word. -/
def triangleBoundaryAtom {R α : Type*} [CommRing R] (word : Word α 3) :
    Chain R α 2 :=
  ∑ omitted : Fin 3, (-1 : R) ^ (omitted : ℕ) •
    generator (R := R) (face word omitted)

/-- [definition] Linear extension of the triangle-word boundary. -/
def triangleBoundary {R α : Type*} [CommRing R] : Chain R α 3 →ₗ[R]
    Chain R α 2 :=
  Finsupp.linearCombination R (triangleBoundaryAtom (R := R))

/-- [definition] The complete alternating triangle-word boundary of one tetrahedron word. -/
def tetrahedronBoundaryAtom {R α : Type*} [CommRing R] (word : Word α 4) :
    Chain R α 3 :=
  ∑ omitted : Fin 4, (-1 : R) ^ (omitted : ℕ) •
    generator (R := R) (face word omitted)

/-- [definition] Linear extension of the tetrahedron-word boundary. -/
def tetrahedronBoundary {R α : Type*} [CommRing R] : Chain R α 4 →ₗ[R]
    Chain R α 3 :=
  Finsupp.linearCombination R (tetrahedronBoundaryAtom (R := R))

/-- [definition] Prefix one apex while retaining the complete ordered tail. -/
def prefixWord {α : Type*} {length : ℕ} (apex : α) (word : Word α length) :
    Word α (length + 1) :=
  Fin.cases apex word

/-- [definition] Prefix an apex to one edge word, producing one triangle word. -/
def prefixEdgeAtom {R α : Type*} [CommRing R] (apex : α) (word : Word α 2) :
    Chain R α 3 :=
  generator (R := R) (prefixWord apex word)

/-- [definition] Linear prefixing of edge-word currents. -/
def prefixEdge {R α : Type*} [CommRing R] (apex : α) : Chain R α 2 →ₗ[R]
    Chain R α 3 :=
  Finsupp.linearCombination R (prefixEdgeAtom (R := R) apex)

/-- [definition] Prefix an apex to one triangle word, producing one tetrahedron word. -/
def prefixTriangleAtom {R α : Type*} [CommRing R] (apex : α) (word : Word α 3) :
    Chain R α 4 :=
  generator (R := R) (prefixWord apex word)

/-- [definition] Linear prefixing of triangle-word currents. -/
def prefixTriangle {R α : Type*} [CommRing R] (apex : α) : Chain R α 3 →ₗ[R]
    Chain R α 4 :=
  Finsupp.linearCombination R (prefixTriangleAtom (R := R) apex)

@[simp]
theorem triangleBoundary_single {R α : Type*} [CommRing R] (word : Word α 3)
    (coefficient : R) :
    triangleBoundary (R := R) (Finsupp.single word coefficient) =
      coefficient • triangleBoundaryAtom (R := R) word := by
  simp [triangleBoundary]

@[simp]
theorem tetrahedronBoundary_single {R α : Type*} [CommRing R] (word : Word α 4)
    (coefficient : R) :
    tetrahedronBoundary (R := R) (Finsupp.single word coefficient) =
      coefficient • tetrahedronBoundaryAtom (R := R) word := by
  simp [tetrahedronBoundary]

@[simp]
theorem prefixEdge_single {R α : Type*} [CommRing R] (apex : α) (word : Word α 2)
    (coefficient : R) :
    prefixEdge (R := R) apex (Finsupp.single word coefficient) =
      coefficient • prefixEdgeAtom (R := R) apex word := by
  simp [prefixEdge]

@[simp]
theorem prefixTriangle_single {R α : Type*} [CommRing R] (apex : α) (word : Word α 3)
    (coefficient : R) :
    prefixTriangle (R := R) apex (Finsupp.single word coefficient) =
      coefficient • prefixTriangleAtom (R := R) apex word := by
  simp [prefixTriangle]

/-- [proved-derived; formal-checked] Prefixing one triangle occurrence is the exact degree-two
chain contraction: its boundary is the original word minus the prefixed boundary word. -/
theorem tetrahedronBoundary_prefixTriangleAtom {R α : Type*} [CommRing R] (apex : α)
    (word : Word α 3) :
    tetrahedronBoundary (R := R) (prefixTriangleAtom (R := R) apex word) =
      generator (R := R) word -
        prefixEdge (R := R) apex (triangleBoundaryAtom (R := R) word) := by
  classical
  change tetrahedronBoundary (R := R)
      (Finsupp.single (prefixWord apex word) 1) =
    Finsupp.single word 1 -
      prefixEdge (R := R) apex (triangleBoundaryAtom (R := R) word)
  rw [tetrahedronBoundary_single]
  simp only [one_smul, tetrahedronBoundaryAtom, triangleBoundaryAtom,
    map_sum, map_smul, generator]
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp_rw [prefixEdge_single]
  simp only [prefixEdgeAtom, generator, one_smul]
  have faceZero : face (prefixWord apex word) (0 : Fin 4) = word := by
    funext index
    fin_cases index <;> rfl
  have faceOne : face (prefixWord apex word) (1 : Fin 4) =
      prefixWord apex (face word (0 : Fin 3)) := by
    funext index
    fin_cases index <;> rfl
  have faceTwo : face (prefixWord apex word) (2 : Fin 4) =
      prefixWord apex (face word (1 : Fin 3)) := by
    funext index
    fin_cases index <;> rfl
  have faceThree : face (prefixWord apex word) (3 : Fin 4) =
      prefixWord apex (face word (2 : Fin 3)) := by
    funext index
    fin_cases index <;> rfl
  rw [faceZero, faceOne, faceTwo, faceThree]
  norm_num
  module

/-- [proved-derived; formal-checked] The contraction acts on an arbitrary finite word current;
closedness removes its complete side-face population before any geometric receiver is applied. -/
theorem tetrahedronBoundary_prefixTriangle {R α : Type*} [CommRing R] (apex : α)
    (chain : Chain R α 3) :
    tetrahedronBoundary (R := R) (prefixTriangle (R := R) apex chain) =
      chain - prefixEdge (R := R) apex (triangleBoundary (R := R) chain) := by
  let left : Chain R α 3 →ₗ[R] Chain R α 3 :=
    (tetrahedronBoundary (R := R)).comp (prefixTriangle (R := R) apex)
  let right : Chain R α 3 →ₗ[R] Chain R α 3 :=
    LinearMap.id - (prefixEdge (R := R) apex).comp (triangleBoundary (R := R))
  have equalMaps : left = right := by
    apply Finsupp.lhom_ext
    intro word coefficient
    have singleAsSmul : (Finsupp.single word coefficient : Chain R α 3) =
        coefficient • generator (R := R) word := by
      simp [generator]
    rw [singleAsSmul]
    simp only [left, right, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_smul]
    rw [show prefixTriangle (R := R) apex (generator (R := R) word) =
        prefixTriangleAtom (R := R) apex word by
      change prefixTriangle (R := R) apex (Finsupp.single word 1) = _
      rw [prefixTriangle_single, one_smul]]
    rw [tetrahedronBoundary_prefixTriangleAtom]
    rw [show triangleBoundary (R := R) (generator (R := R) word) =
        triangleBoundaryAtom (R := R) word by
      change triangleBoundary (R := R) (Finsupp.single word 1) = _
      rw [triangleBoundary_single, one_smul]]
  exact LinearMap.congr_fun equalMaps chain

/-- [proved-derived; formal-checked] A closed ordered triangle current is filled exactly by
prefixing any addressed apex.  Diagonal and repeated words remain present in both sides. -/
theorem tetrahedronBoundary_prefixTriangle_of_closed {R α : Type*} [CommRing R] (apex : α)
    (chain : Chain R α 3)
    (closed : triangleBoundary (R := R) chain = 0) :
    tetrahedronBoundary (R := R) (prefixTriangle (R := R) apex chain) = chain := by
  rw [tetrahedronBoundary_prefixTriangle, closed, map_zero, sub_zero]

/-- [definition] The complete population of closed ordered triangle currents. -/
abbrev ClosedTriangleCurrent (R α : Type*) [CommRing R] :=
  LinearMap.ker (triangleBoundary (R := R) (α := α))

/-- [proved-derived; formal-checked] Prefix contraction is itself an elementary boundary holon.
Its occurrences are closed ordered currents, its source is zero, its target is the complete current,
and its receiver retains every prefixed word as the reconstruction fibre. -/
def closedPrefixHolon {R α : Type*} [CommRing R] (apex : α) :
    Soma.Holonics.BoundaryHolon (Chain R α 3) (Chain R α 4) where
  Occurrence := ClosedTriangleCurrent R α
  source _ := 0
  target occurrence := occurrence.1
  receive occurrence := prefixTriangle (R := R) apex occurrence.1
  boundary := (tetrahedronBoundary (R := R) (α := α)).toAddMonoidHom
  returnsBoundary := by
    intro occurrence
    change tetrahedronBoundary (R := R)
        (prefixTriangle (R := R) apex occurrence.1) = occurrence.1 - 0
    rw [tetrahedronBoundary_prefixTriangle_of_closed apex occurrence.1 occurrence.2,
      sub_zero]

section Audit

#print axioms tetrahedronBoundary_prefixTriangleAtom
#print axioms tetrahedronBoundary_prefixTriangle
#print axioms tetrahedronBoundary_prefixTriangle_of_closed
#print axioms closedPrefixHolon

end Audit

end Soma.Holonics.OrderedWordChain
