import ElementaryHolonics.Millennium.HodgeBarycentricChainSupport
import ElementaryHolonics.Millennium.HodgeTetrahedralStarCover

/-!
# Finite boundary-witness carrier for the tetrahedral sphere cycle

The global `CompatibleTetrahedralLabeling` interface is stronger than the present Hodge gate.
To prove that the explicit radial sphere cycle is not a singular boundary, begin instead with one
hypothetical degree-three boundary witness.  Its actual chain support is finite.  This file retains
only that occurrence population, its coefficients, one tetrahedral vertex tuple on each occurrence,
and the complete carried boundary.

The source-specific contradiction is exact.  Empty fourfold star intersection makes every local
four-label tuple admissible, hence its alternating face current is zero.  A seam-compatible,
radially normalized refinement of a boundary witness would make the sum of those same local
currents return the nonzero tetrahedral fundamental face current.  Those two returns cannot agree.

This file proves the finite algebra and packages the remaining geometric deed as a function from a
hypothetical boundary equality to this finite return.  It does not assume a global label field, a
global subdivision scale, or a singular-homology comparison.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` relative to the imported exact singular-chain support and
tetrahedral incidence laws.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFiniteCarrier

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricCoverSmallness
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover

/-- [definition] The genuine nonzero occurrence population of one rational singular
three-chain. -/
abbrev BoundaryOccurrence (boundaryWitness : SphereChain 3) :=
  ↑(sphereChainSupport 3 boundaryWitness)

/-- [definition] The finite degree-two face population needed by one boundary contradiction: all
four source faces of every supported three-simplex together with the four radial normalization
faces.  Equal face maps are identified only as equal addressed singular simplices. -/
def boundaryFaceClosure (boundaryWitness : SphereChain 3) :
    Finset (SphereSingularSimplex 2) := by
  classical
  exact
    (sphereChainSupport 3 boundaryWitness).biUnion (fun simplex =>
      Finset.univ.image (fun face : Fin 4 => simplexFace face simplex)) ∪
    Finset.univ.image radialSingularSimplex

/-- [proved-derived; formal-checked] Every face of every genuinely supported boundary occurrence
is retained in the finite face closure. -/
theorem simplexFace_mem_boundaryFaceClosure
    (boundaryWitness : SphereChain 3)
    (occurrence : BoundaryOccurrence boundaryWitness) (face : Fin 4) :
    simplexFace face occurrence.1 ∈ boundaryFaceClosure boundaryWitness := by
  classical
  apply Finset.mem_union_left
  rw [Finset.mem_biUnion]
  exact ⟨occurrence.1, occurrence.2,
    Finset.mem_image.2 ⟨face, Finset.mem_univ face, rfl⟩⟩

/-- [proved-derived; formal-checked] Every radial normalization face is retained in the same finite
closure. -/
theorem radialSingularSimplex_mem_boundaryFaceClosure
    (boundaryWitness : SphereChain 3) (face : Fin 4) :
    radialSingularSimplex face ∈ boundaryFaceClosure boundaryWitness := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.2 ⟨face, Finset.mem_univ face, rfl⟩

/-- [proved-derived; formal-checked] The actual finite face closure of any alleged boundary admits
one exact barycentric depth at which every deeper descendant lies in a tetrahedral open star.  This
is the lawful uniform-scale theorem: it is quantified over the witness-relative finite population,
not over all singular simplices. -/
theorem exists_scale_boundaryFaceClosure_vertexStar_subordinate
    (boundaryWitness : SphereChain 3) :
    ∃ scale : ℕ, ∀ occurrence : ↑(boundaryFaceClosure boundaryWitness),
      ∀ word : List BarycentricTriangleAddress,
        scale ≤ word.length → ∃ vertex : TetraVertex,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 2)) occurrence.1).comp
                (barycentricTriangleWordMap word)) ⊆ vertexStar vertex := by
  classical
  exact exists_scale_finite_sphereSimplex_family_barycentric_descendants_subordinate
    (fun occurrence : ↑(boundaryFaceClosure boundaryWitness) => occurrence.1)
    vertexStar isOpen_vertexStar vertexStar_cover

/-- [definition] The complete alternating finite-face current returned by labels on every
occurrence in one actual degree-three support.  Coefficients and occurrence addresses are retained;
no equal geometric faces are quotient-cancelled here. -/
def carriedBoundary (boundaryWitness : SphereChain 3)
    (labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex) : FaceChain :=
  ∑ occurrence : BoundaryOccurrence boundaryWitness,
    sphereChainCoefficient 3 boundaryWitness occurrence.1 •
      ∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
        orientedFaceCarry
          ((labels occurrence ∘ face.succAbove) 0)
          ((labels occurrence ∘ face.succAbove) 1)
          ((labels occurrence ∘ face.succAbove) 2)

/-- [definition] Each supported three-simplex obeys the exact tetrahedral nerve obstruction: its
four vertex labels cannot all be distinct. -/
def LocallyAdmissible (boundaryWitness : SphereChain 3)
    (labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex) : Prop :=
  ∀ occurrence,
    FourLabelsAdmissible
      (labels occurrence 0) (labels occurrence 1)
      (labels occurrence 2) (labels occurrence 3)

/-- [definition] The cover-side constitutive datum: the four label stars of every retained local
three-occurrence share one actual sphere occurrence.  This is stronger than fourfold admissibility
in exactly the geometric way supplied by a star-of-vertex subdivision. -/
def CommonStarWitness (boundaryWitness : SphereChain 3)
    (labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex) : Prop :=
  ∀ occurrence, ∃ point : HodgeTwoSphereFundamentalCycle.TwoSphere,
    ∀ index : Fin 4, point ∈ vertexStar (labels occurrence index)

/-- [proved-derived; formal-checked] Common star incidence supplies the local admissibility law;
this is the exact nerve passage from sphere geometry to the finite alternating current. -/
theorem locallyAdmissible_of_commonStarWitness
    (boundaryWitness : SphereChain 3)
    (labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex)
    (common : CommonStarWitness boundaryWitness labels) :
    LocallyAdmissible boundaryWitness labels := by
  intro occurrence
  obtain ⟨point, point_mem⟩ := common occurrence
  exact HodgeTetrahedralStarCover.fourLabelsAdmissible_of_commonStarPoint
    (labels occurrence) point point_mem

/-- [proved-derived; formal-checked] Every locally admissible supported occurrence returns zero
alternating face current, so their exact coefficient-weighted population also returns zero. -/
theorem carriedBoundary_eq_zero_of_locallyAdmissible
    (boundaryWitness : SphereChain 3)
    (labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex)
    (admissible : LocallyAdmissible boundaryWitness labels) :
    carriedBoundary boundaryWitness labels = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro occurrence _
  rw [show
      (∑ face : Fin 4, (-1 : ℚ) ^ (face : ℕ) •
        orientedFaceCarry
          ((labels occurrence ∘ face.succAbove) 0)
          ((labels occurrence ∘ face.succAbove) 1)
          ((labels occurrence ∘ face.succAbove) 2)) = 0 by
    rw [Fin.sum_univ_four]
    simp [Function.comp_apply, Fin.succAbove, Fin.ext_iff]
    rw [show (-1 : ℚ) ^ 3 = -1 by norm_num]
    simp only [neg_one_smul]
    simpa [Function.comp_apply, Fin.succAbove, Fin.ext_iff, sub_eq_add_neg] using
      alternating_orientedFaceCarry_zero_of_admissible
        (labels occurrence 0) (labels occurrence 1)
        (labels occurrence 2) (labels occurrence 3)
        (admissible occurrence)]
  exact smul_zero _

/-- [proved-derived; formal-checked] The finite tetrahedral fundamental face current is genuinely
nonzero; coordinate zero is the exact separating receiver. -/
theorem fundamentalFaceChain_ne_zero : fundamentalFaceChain ≠ 0 := by
  intro hzero
  have coordinateZero := congrFun hzero (0 : Fin 4)
  norm_num [fundamentalFaceChain] at coordinateZero

/-- [definition] The exact finite artifact the remaining geometric passage must construct from a
hypothetical boundary witness.  `returnsRadial` is where face-seam cancellation, subdivision
chain-naturality, the source boundary equality, and radial normalization must be composed; none is
inferred from local membership alone. -/
structure BoundaryReturn (boundaryWitness : SphereChain 3) where
  labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex
  locallyAdmissible : LocallyAdmissible boundaryWitness labels
  returnsRadial : carriedBoundary boundaryWitness labels = fundamentalFaceChain

/-- [definition] The geometric finite return before passage through the empty-fourfold nerve law.
It retains the common sphere occurrence witnessing each local star interaction rather than storing
admissibility as an unexplained Boolean face.  This is an output certificate, not the construction
interface: a lawful construction must first produce one global-vertex closed-star labeling on the
refined occurrence complex and derive `returnsRadial` by the relative Sperner carry. -/
structure GeometricBoundaryReturn (boundaryWitness : SphereChain 3) where
  labels : BoundaryOccurrence boundaryWitness → Fin 4 → TetraVertex
  commonStar : CommonStarWitness boundaryWitness labels
  returnsRadial : carriedBoundary boundaryWitness labels = fundamentalFaceChain

/-- [proved-derived; formal-checked] Empty fourfold star intersection transports every geometric
finite return into the exact algebraic return. -/
def GeometricBoundaryReturn.toBoundaryReturn
    {boundaryWitness : SphereChain 3}
    (returned : GeometricBoundaryReturn boundaryWitness) :
    BoundaryReturn boundaryWitness where
  labels := returned.labels
  locallyAdmissible := locallyAdmissible_of_commonStarWitness
    boundaryWitness returned.labels returned.commonStar
  returnsRadial := returned.returnsRadial

/-- [receiver-insufficiency-counterexample; formal-checked] No finite boundary-support population
can simultaneously satisfy the local empty-fourfold law and return the nonzero radial current.
Thus a hypothetical singular boundary becomes impossible as soon as the geometric refinement
constructs `BoundaryReturn`. -/
theorem boundaryReturn_isEmpty (boundaryWitness : SphereChain 3) :
    IsEmpty (BoundaryReturn boundaryWitness) := by
  constructor
  intro returned
  apply fundamentalFaceChain_ne_zero
  rw [← returned.returnsRadial]
  exact carriedBoundary_eq_zero_of_locallyAdmissible
    boundaryWitness returned.labels returned.locallyAdmissible

/-- [receiver-insufficiency-counterexample; formal-checked] A common-star finite return is empty
for every alleged boundary population. -/
theorem geometricBoundaryReturn_isEmpty (boundaryWitness : SphereChain 3) :
    IsEmpty (GeometricBoundaryReturn boundaryWitness) := by
  constructor
  intro returned
  letI := boundaryReturn_isEmpty boundaryWitness
  exact isEmptyElim returned.toBoundaryReturn

/-- [proved-derived; formal-checked] **FINITE HODGE NONBOUNDARY REDUCTION.**  It is enough to
construct the finite return above from each alleged singular three-boundary of the radial cycle.
The construction is allowed to depend on the actual witness and therefore needs only its finite
support; no global carrier or global scale is required. -/
theorem sphereFundamentalCandidate_not_mem_boundary_range_of_finite_return
    (construct : ∀ boundaryWitness : SphereChain 3,
      SphereSingularChainComplex.d 3 2 boundaryWitness = sphereFundamentalCandidate →
        Nonempty (BoundaryReturn boundaryWitness)) :
    sphereFundamentalCandidate ∉
      Set.range (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom := by
  rintro ⟨boundaryWitness, boundaryLaw⟩
  letI := boundaryReturn_isEmpty boundaryWitness
  exact isEmptyElim (construct boundaryWitness boundaryLaw).some

/-- [proved-derived; formal-checked] The same finite Hodge reduction stated entirely in geometric
star-cover terms.  The remaining construction now owes only common-star incidence and the exact
radial current return on the supplied finite boundary witness. -/
theorem sphereFundamentalCandidate_not_mem_boundary_range_of_geometric_return
    (construct : ∀ boundaryWitness : SphereChain 3,
      SphereSingularChainComplex.d 3 2 boundaryWitness = sphereFundamentalCandidate →
        Nonempty (GeometricBoundaryReturn boundaryWitness)) :
    sphereFundamentalCandidate ∉
      Set.range (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom := by
  apply sphereFundamentalCandidate_not_mem_boundary_range_of_finite_return
  intro boundaryWitness boundaryLaw
  exact (construct boundaryWitness boundaryLaw).map
    GeometricBoundaryReturn.toBoundaryReturn

section Audit

#print axioms carriedBoundary_eq_zero_of_locallyAdmissible
#print axioms locallyAdmissible_of_commonStarWitness
#print axioms simplexFace_mem_boundaryFaceClosure
#print axioms radialSingularSimplex_mem_boundaryFaceClosure
#print axioms exists_scale_boundaryFaceClosure_vertexStar_subordinate
#print axioms fundamentalFaceChain_ne_zero
#print axioms boundaryReturn_isEmpty
#print axioms geometricBoundaryReturn_isEmpty
#print axioms sphereFundamentalCandidate_not_mem_boundary_range_of_finite_return
#print axioms sphereFundamentalCandidate_not_mem_boundary_range_of_geometric_return

end Audit

end Soma.Holonics.Millennium.HodgeFiniteCarrier
