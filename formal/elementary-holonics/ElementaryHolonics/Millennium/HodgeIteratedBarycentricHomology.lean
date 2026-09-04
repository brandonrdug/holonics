import ElementaryHolonics.Millennium.HodgeBarycentricAffineSourceComplex
import ElementaryHolonics.Millennium.HodgeRefinementWords

/-!
# Exact homology return through every finite barycentric scale

The source-faithful affine cone already fills the complete one-step degree-two subdivision
defect.  This file composes that local filling through an arbitrary fixed refinement depth.
For a genuine singular two-cycle, the returned three-current has boundary exactly the refined
cycle minus the original cycle.  Thus refinement changes occurrence population and scale while
preserving the represented singular-homology class by an explicit retained lineage current.

Truth status: introduced currents are `[definition]`; the homotopy returns and their linear zero
lemma are `[proved-derived; formal-checked]`, from the affine source cone and the exact barycentric
boundary squares.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeBarycentricSubdivisionHomotopy
open Soma.Holonics.Millennium.HodgeBarycentricAffineSourceComplex

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [proved-derived; formal-checked] The explicit affine degree-two cone returns
the complete one-step refinement defect on every two-chain. -/
theorem boundary_barycentricDegreeTwoHomotopyMorphism (chain : SphereChain 2) :
    SphereSingularChainComplex.d 3 2
        (barycentricDegreeTwoHomotopyMorphism chain) =
      barycentricTriangleSubdivisionMorphism chain - chain -
        barycentricEdgeSubdivisionHomotopyMorphism
          (SphereSingularChainComplex.d 2 1 chain) := by
  have law := congrArg
    (fun morphism : SphereSingularChainComplex.X 2 ⟶
        SphereSingularChainComplex.X 2 => morphism chain)
    barycentricDegreeTwoHomotopyMorphism_comp_boundary
  change SphereSingularChainComplex.d 3 2
      (barycentricDegreeTwoHomotopyMorphism chain) =
    barycentricTriangleSubdivisionMorphism chain - chain -
      barycentricEdgeSubdivisionHomotopyMorphism
        (SphereSingularChainComplex.d 2 1 chain) at law
  exact law

/-- [definition] The accumulated three-current carrying all one-step affine cones from scale zero
through the declared fixed refinement depth. -/
def iteratedBarycentricDegreeTwoHomotopy : ℕ → SphereChain 2 → SphereChain 3
  | 0 => fun _ => 0
  | scale + 1 => fun chain =>
      iteratedBarycentricDegreeTwoHomotopy scale chain +
        barycentricDegreeTwoHomotopyMorphism
          (iteratedBarycentricTriangleSubdivision scale chain)

/-- [proved-derived; formal-checked] Refining the zero edge current at any fixed
depth retains zero. -/
theorem iteratedBarycentricEdgeSubdivision_zero (scale : ℕ) :
    iteratedBarycentricEdgeSubdivision scale (0 : SphereChain 1) = 0 := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricEdgeSubdivisionMorphism
          (iteratedBarycentricEdgeSubdivision scale 0) = 0
      rw [inductionHypothesis, map_zero]

/-- [proved-derived; formal-checked] Every fixed-depth refinement of a singular
two-cycle differs from its source by the exact boundary of the accumulated addressed affine-cone
current. -/
theorem boundary_iteratedBarycentricDegreeTwoHomotopy
    (scale : ℕ) (chain : SphereChain 2)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    SphereSingularChainComplex.d 3 2
        (iteratedBarycentricDegreeTwoHomotopy scale chain) =
      iteratedBarycentricTriangleSubdivision scale chain - chain := by
  induction scale with
  | zero =>
      simp [iteratedBarycentricDegreeTwoHomotopy,
        iteratedBarycentricTriangleSubdivision]
  | succ scale inductionHypothesis =>
      have refinedCycle :
          SphereSingularChainComplex.d 2 1
              (iteratedBarycentricTriangleSubdivision scale chain) = 0 := by
        rw [boundary_iteratedBarycentricTriangleSubdivision, cycle]
        exact iteratedBarycentricEdgeSubdivision_zero scale
      rw [iteratedBarycentricDegreeTwoHomotopy, map_add,
        inductionHypothesis,
        boundary_barycentricDegreeTwoHomotopyMorphism,
        refinedCycle, map_zero]
      simp only [iteratedBarycentricTriangleSubdivision]
      abel

section Audit

#print axioms boundary_barycentricDegreeTwoHomotopyMorphism
#print axioms iteratedBarycentricEdgeSubdivision_zero
#print axioms boundary_iteratedBarycentricDegreeTwoHomotopy

end Audit

end Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology
