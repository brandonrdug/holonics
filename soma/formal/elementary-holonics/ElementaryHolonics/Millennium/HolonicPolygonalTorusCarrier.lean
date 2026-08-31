import ElementaryHolonics.Millennium.HolonicTorusKnots
import ElementaryHolonics.Millennium.Turn
import ElementaryHolonics.Foundation.BoundaryReceiver

/-!
# A finite polygonal solid-torus carrier

This file constructs the first combinatorial carrier required by Gate L1 of the Millennium Lean
roadmap.  The carrier is the product of a finite major cycle with a polygonal cross-section: one
core vertex and one boundary polygon at every major address.  Its edge and face incidences are
given over `ℤ`, so signs are orientations of addressed cells rather than untyped scalar labels.

The construction returns four exact receipts:

* every declared face has zero vertex boundary;
* the longitudinal and meridional boundary chains close;
* every cross-section triangle closes, while their sum has exactly the boundary meridian;
* a dual cross-section cut pairs to one with every unit longitudinal winding.

This is a finite cellular carrier.  It does not yet assert a geometric realization, a homology
classification, or a continuum limit.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicPolygonalTorusCarrier

open scoped BigOperators
open Soma.Holonics.Foundation

/-- Major addresses.  `major + 1` keeps the cyclic carrier nonempty. -/
abbrev MajorIndex (major : ℕ) := Fin (major + 1)

/-- Boundary addresses in the polygonal cross-section.  `minor + 3` supplies at least a triangle. -/
abbrev MinorIndex (minor : ℕ) := Fin (minor + 3)

/-- The next address on the cyclic major axis. -/
def majorNext {major : ℕ} : MajorIndex major ≃ MajorIndex major :=
  Equiv.addRight 1

/-- The next address on the polygonal boundary cycle. -/
def minorNext {minor : ℕ} : MinorIndex minor ≃ MinorIndex minor :=
  Equiv.addRight 1

/-- Vertices of `S¹ ×` a coned polygon: one core and one polygon boundary per major address. -/
inductive Vertex (major minor : ℕ)
  | core : MajorIndex major → Vertex major minor
  | boundary : MajorIndex major → MinorIndex minor → Vertex major minor
  deriving DecidableEq, Fintype

/-- Oriented one-cells of the product cellulation. -/
inductive Edge (major minor : ℕ)
  | coreLongitude : MajorIndex major → Edge major minor
  | longitude : MajorIndex major → MinorIndex minor → Edge major minor
  | meridian : MajorIndex major → MinorIndex minor → Edge major minor
  | radial : MajorIndex major → MinorIndex minor → Edge major minor
  deriving DecidableEq, Fintype

/-- Oriented two-cells: cross-section triangles, boundary torus squares, and radial-longitude
squares. -/
inductive Face (major minor : ℕ)
  | crossSection : MajorIndex major → MinorIndex minor → Face major minor
  | boundarySquare : MajorIndex major → MinorIndex minor → Face major minor
  | radialLongitude : MajorIndex major → MinorIndex minor → Face major minor
  deriving DecidableEq, Fintype

/-- Oriented prism cells obtained by transporting one cross-section triangle through one major
step. -/
inductive Cell3 (major minor : ℕ)
  | wedge : MajorIndex major → MinorIndex minor → Cell3 major minor
  deriving DecidableEq, Fintype

/-- Integer cellular chains retain each addressed occurrence and its orientation coefficient. -/
abbrev Chain (α : Type*) := α →₀ ℤ

/-- The terminal minus initial incidence of one oriented edge. -/
def edgeBoundary : Edge major minor → Chain (Vertex major minor)
  | .coreLongitude i =>
      Finsupp.single (.core (majorNext i)) 1 - Finsupp.single (.core i) 1
  | .longitude i j =>
      Finsupp.single (.boundary (majorNext i) j) 1 -
        Finsupp.single (.boundary i j) 1
  | .meridian i j =>
      Finsupp.single (.boundary i (minorNext j)) 1 -
        Finsupp.single (.boundary i j) 1
  | .radial i j =>
      Finsupp.single (.boundary i j) 1 - Finsupp.single (.core i) 1

/-- Linear extension of edge incidence to every integer one-chain. -/
def boundaryOne : Chain (Edge major minor) →ₗ[ℤ] Chain (Vertex major minor) :=
  Finsupp.linearCombination ℤ edgeBoundary

@[simp]
theorem boundaryOne_single (edge : Edge major minor) (coefficient : ℤ) :
    boundaryOne (Finsupp.single edge coefficient) = coefficient • edgeBoundary edge := by
  simp [boundaryOne]

/-- The oriented edge boundary of each two-cell. -/
def faceBoundary : Face major minor → Chain (Edge major minor)
  | .crossSection i j =>
      Finsupp.single (.radial i j) 1 + Finsupp.single (.meridian i j) 1 -
        Finsupp.single (.radial i (minorNext j)) 1
  | .boundarySquare i j =>
      Finsupp.single (.longitude i j) 1 +
        Finsupp.single (.meridian (majorNext i) j) 1 -
        Finsupp.single (.longitude i (minorNext j)) 1 -
        Finsupp.single (.meridian i j) 1
  | .radialLongitude i j =>
      Finsupp.single (.radial i j) 1 + Finsupp.single (.longitude i j) 1 -
        Finsupp.single (.radial (majorNext i) j) 1 -
        Finsupp.single (.coreLongitude i) 1

/-- Every two-cell returns zero after its edge incidence is followed to vertices: `∂₁∂₂ = 0`. -/
theorem boundaryOne_faceBoundary_eq_zero (face : Face major minor) :
    boundaryOne (faceBoundary face) = 0 := by
  cases face <;>
    simp [faceBoundary, edgeBoundary]

/-- The longitudinal boundary chain at one minor address. -/
def longitudeWindingChain (j : MinorIndex minor) : Chain (Edge major minor) :=
  ∑ i : MajorIndex major, Finsupp.single (.longitude i j) 1

/-- The meridional boundary chain at one major address. -/
def meridianWindingChain (i : MajorIndex major) : Chain (Edge major minor) :=
  ∑ j : MinorIndex minor, Finsupp.single (.meridian i j) 1

/-- A longitudinal winding has no vertex boundary. -/
theorem boundaryOne_longitudeWindingChain_eq_zero (j : MinorIndex minor) :
    boundaryOne (longitudeWindingChain (major := major) j) = 0 := by
  rw [longitudeWindingChain, map_sum]
  simp only [boundaryOne_single, one_smul, edgeBoundary]
  rw [Finset.sum_sub_distrib]
  have hshift := Equiv.sum_comp (majorNext (major := major))
    (fun i : MajorIndex major => Finsupp.single (Vertex.boundary i j) (1 : ℤ))
  rw [hshift]
  exact sub_self _

/-- A meridional winding has no vertex boundary. -/
theorem boundaryOne_meridianWindingChain_eq_zero (i : MajorIndex major) :
    boundaryOne (meridianWindingChain (minor := minor) i) = 0 := by
  rw [meridianWindingChain, map_sum]
  simp only [boundaryOne_single, one_smul, edgeBoundary]
  rw [Finset.sum_sub_distrib]
  have hshift := Equiv.sum_comp (minorNext (minor := minor))
    (fun j : MinorIndex minor => Finsupp.single (Vertex.boundary i j) (1 : ℤ))
  rw [hshift]
  exact sub_self _

/-- The filled polygonal cross-section at one major address. -/
def crossSectionDisk (i : MajorIndex major) : Chain (Face major minor) :=
  ∑ j : MinorIndex minor, Finsupp.single (.crossSection i j) 1

/-- Linear extension of face incidence to every integer two-chain. -/
def boundaryTwo : Chain (Face major minor) →ₗ[ℤ] Chain (Edge major minor) :=
  Finsupp.linearCombination ℤ faceBoundary

@[simp]
theorem boundaryTwo_single (face : Face major minor) (coefficient : ℤ) :
    boundaryTwo (Finsupp.single face coefficient) = coefficient • faceBoundary face := by
  simp [boundaryTwo]

/-- The radial incidences of the filled polygon cancel pairwise, leaving exactly its meridian. -/
theorem boundaryTwo_crossSectionDisk_eq_meridian (i : MajorIndex major) :
    boundaryTwo (crossSectionDisk (minor := minor) i) = meridianWindingChain i := by
  rw [crossSectionDisk, map_sum, meridianWindingChain]
  simp only [boundaryTwo_single, one_smul, faceBoundary]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hshift := Equiv.sum_comp (minorNext (minor := minor))
    (fun j : MinorIndex minor => Finsupp.single (Edge.radial i j) (1 : ℤ))
  rw [hshift]
  abel

/-- The oriented face boundary of one triangular prism in the product cellulation. -/
def cellBoundary : Cell3 major minor → Chain (Face major minor)
  | .wedge i j =>
      Finsupp.single (.crossSection i j) 1 +
        Finsupp.single (.boundarySquare i j) 1 -
        Finsupp.single (.crossSection (majorNext i) j) 1 -
        Finsupp.single (.radialLongitude i j) 1 +
        Finsupp.single (.radialLongitude i (minorNext j)) 1

/-- Every prism boundary closes at the edge level: `∂₂∂₃ = 0`. -/
theorem boundaryTwo_cellBoundary_eq_zero (cell : Cell3 major minor) :
    boundaryTwo (cellBoundary cell) = 0 := by
  cases cell
  simp [cellBoundary, faceBoundary]
  abel

/-- A cross-section cut is the integer cochain supported on one major layer of longitudinal
edges.  It is dual to the longitudinal winding direction. -/
def dualCrossSectionCut (cut : MajorIndex major) : Edge major minor → ℤ
  | .coreLongitude i => if i = cut then 1 else 0
  | .longitude i _ => if i = cut then 1 else 0
  | .meridian _ _ => 0
  | .radial _ _ => 0

/-- Exact evaluation of an integer cochain on an addressed one-chain. -/
def evaluateCochain (cochain : Edge major minor → ℤ) :
    Chain (Edge major minor) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ cochain

@[simp]
theorem evaluateCochain_single (cochain : Edge major minor → ℤ)
    (edge : Edge major minor) (coefficient : ℤ) :
    evaluateCochain cochain (Finsupp.single edge coefficient) = coefficient * cochain edge := by
  simp [evaluateCochain]

/-- Every declared cross-section cut meets a unit longitudinal boundary winding exactly once. -/
theorem dualCrossSectionCut_pairs_longitudeWindingChain
    (cut : MajorIndex major) (j : MinorIndex minor) :
    evaluateCochain (dualCrossSectionCut cut) (longitudeWindingChain j) = 1 := by
  rw [longitudeWindingChain, map_sum]
  simp [dualCrossSectionCut]

/-- The same cross-section cut is blind to a meridional winding. -/
theorem dualCrossSectionCut_pairs_meridianWindingChain
    (cut i : MajorIndex major) :
    evaluateCochain (dualCrossSectionCut cut) (meridianWindingChain (minor := minor) i) = 0 := by
  rw [meridianWindingChain, map_sum]
  simp [dualCrossSectionCut]

/-- The dual cross-section cut vanishes on the boundary of every two-cell. -/
theorem dualCrossSectionCut_pairs_faceBoundary_eq_zero
    (cut : MajorIndex major) (face : Face major minor) :
    evaluateCochain (dualCrossSectionCut cut) (faceBoundary face) = 0 := by
  cases face <;> simp [faceBoundary, dualCrossSectionCut]

/-- Therefore the cross-section cochain vanishes on every cellular two-boundary. -/
theorem dualCrossSectionCut_pairs_boundaryTwo_eq_zero
    (cut : MajorIndex major) (chain : Chain (Face major minor)) :
    evaluateCochain (dualCrossSectionCut cut) (boundaryTwo chain) = 0 := by
  let composite : Chain (Face major minor) →ₗ[ℤ] ℤ :=
    (evaluateCochain (dualCrossSectionCut cut)).comp boundaryTwo
  have hzero : composite = 0 := by
    apply Finsupp.lhom_ext
    intro face coefficient
    simp [composite, dualCrossSectionCut_pairs_faceBoundary_eq_zero]
  exact LinearMap.congr_fun hzero chain

/-- The meridian bounds the filled cross-section disk, while a unit longitude cannot be any
cellular two-boundary because the dual cut reads one on it and zero on every boundary. -/
theorem longitudeWindingChain_isNot_boundaryTwo
    (cut : MajorIndex major) (j : MinorIndex minor) :
    ¬ ∃ chain : Chain (Face major minor), boundaryTwo chain = longitudeWindingChain j := by
  change longitudeWindingChain j ∉ Set.range boundaryTwo.toAddMonoidHom
  exact not_mem_range_of_receiver_boundary_eq_zero
    boundaryTwo.toAddMonoidHom
    (evaluateCochain (dualCrossSectionCut cut)).toAddMonoidHom
    (dualCrossSectionCut_pairs_boundaryTwo_eq_zero cut)
    (by
      change evaluateCochain (dualCrossSectionCut cut) (longitudeWindingChain j) ≠ 0
      rw [dualCrossSectionCut_pairs_longitudeWindingChain]
      norm_num)

/-! ## Typed zero is a transported fibre, not a shared glyph -/

/-- Two differently typed coordinate charts over the same occurrence population, together with
the exact rebase that identifies their readings. -/
structure AddressedChartTransition (X A B : Type*) [Zero A] [Zero B] where
  sourceChart : X → A
  targetChart : X → B
  rebase : A ≃ B
  natural : ∀ x, rebase (sourceChart x) = targetChart x
  rebase_zero : rebase 0 = 0

namespace AddressedChartTransition

/-- A zero in the target chart is the same addressed fibre as a zero in the source chart only
through the declared transition. -/
theorem target_eq_zero_iff_source_eq_zero
    {X A B : Type*} [Zero A] [Zero B] (transition : AddressedChartTransition X A B) (x : X) :
    transition.targetChart x = 0 ↔ transition.sourceChart x = 0 := by
  constructor
  · intro htarget
    apply transition.rebase.injective
    rw [transition.natural, htarget, transition.rebase_zero]
  · intro hsource
    rw [← transition.natural, hsource, transition.rebase_zero]

/-- Hence the two typed zero fibres agree as subsets of their common occurrence carrier. -/
theorem zeroFibres_eq
    {X A B : Type*} [Zero A] [Zero B] (transition : AddressedChartTransition X A B) :
    {x | transition.sourceChart x = 0} = {x | transition.targetChart x = 0} := by
  ext x
  exact (transition.target_eq_zero_iff_source_eq_zero x).symm

end AddressedChartTransition

/-- A zero receiver can still collapse distinct carrier occurrences. -/
def boolZeroReceiver : Bool → Unit := fun _ => ()

/-- Equal zero-like readings do not reconstruct the occurrence without an injective chart or a
retained reconstruction fibre. -/
theorem equalZeroReading_doesNotIdentifyCarrierOccurrence :
    boolZeroReceiver false = boolZeroReceiver true ∧ false ≠ true := by
  decide

end Soma.Holonics.Millennium.HolonicPolygonalTorusCarrier

end

section Audit
open Soma.Holonics.Millennium.HolonicPolygonalTorusCarrier
#print axioms boundaryOne_faceBoundary_eq_zero
#print axioms boundaryOne_longitudeWindingChain_eq_zero
#print axioms boundaryOne_meridianWindingChain_eq_zero
#print axioms boundaryTwo_crossSectionDisk_eq_meridian
#print axioms boundaryTwo_cellBoundary_eq_zero
#print axioms dualCrossSectionCut_pairs_longitudeWindingChain
#print axioms dualCrossSectionCut_pairs_meridianWindingChain
#print axioms dualCrossSectionCut_pairs_faceBoundary_eq_zero
#print axioms dualCrossSectionCut_pairs_boundaryTwo_eq_zero
#print axioms longitudeWindingChain_isNot_boundaryTwo
#print axioms AddressedChartTransition.target_eq_zero_iff_source_eq_zero
#print axioms AddressedChartTransition.zeroFibres_eq
#print axioms equalZeroReading_doesNotIdentifyCarrierOccurrence
end Audit
