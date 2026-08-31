import ElementaryHolonics.Millennium.HodgeIteratedBarycentricHomology
import ElementaryHolonics.Millennium.HodgeRadialCurrent

/-!
# Finite tetrahedral carrier of every refined sphere cycle

Point-natural carry is already a chain map through degrees two, one, and zero.  Consequently the
point current of every fixed-depth refinement of a genuine singular two-cycle is an actual cycle
in the finite tetrahedral face complex.  The computed finite kernel then forces that current to be
one rational multiple of the fundamental face population.

This is the finite half of the sphere-surjectivity passage.  It does not identify the source cycle
with its carried realization in singular homology; that remaining equality is the common-star
carrier homotopy recorded in the roadmap.

Truth status: introduced carriers are `[definition]`; every theorem is
`[proved-derived; formal-checked]` from point-current naturality, exact
barycentric boundary transport, and the computed tetrahedral cycle coordinates.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedCycleCarrier

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [definition] The finite face current returned by one point-natural receiver after the declared
fixed refinement depth. -/
def refinedCyclePointCurrent (labeling : StarPointLabeling) (scale : ℕ)
    (chain : SphereChain 2) : FaceChain :=
  pointCarryMorphism labeling 2
    (iteratedBarycentricTriangleSubdivision scale chain)

/-- [proved-derived; formal-checked] The finite point current of every refined
singular two-cycle has zero complete six-edge boundary. -/
theorem refinedCyclePointCurrent_boundary_zero
    (labeling : StarPointLabeling) (scale : ℕ) (chain : SphereChain 2)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    faceBoundary (refinedCyclePointCurrent labeling scale chain) = 0 := by
  rw [refinedCyclePointCurrent, ← pointCarryMorphism_boundary_two]
  rw [boundary_iteratedBarycentricTriangleSubdivision, cycle,
    iteratedBarycentricEdgeSubdivision_zero, map_zero]

/-- [proved-derived; formal-checked] The complete finite carrier of every refined
sphere cycle is forced by its face-zero coordinate and the one-dimensional tetrahedral top
kernel. -/
theorem refinedCyclePointCurrent_coordinates
    (labeling : StarPointLabeling) (scale : ℕ) (chain : SphereChain 2)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    refinedCyclePointCurrent labeling scale chain =
      refinedCyclePointCurrent labeling scale chain 0 • fundamentalFaceChain :=
  cycle_coordinates _ (refinedCyclePointCurrent_boundary_zero labeling scale chain cycle)

/-- [proved-derived; formal-checked] Realizing the finite current of a refined
sphere cycle returns exactly one rational multiple of the explicit radial sphere cycle. -/
theorem faceRealization_refinedCyclePointCurrent
    (labeling : StarPointLabeling) (scale : ℕ) (chain : SphereChain 2)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    faceRealization (refinedCyclePointCurrent labeling scale chain) =
      refinedCyclePointCurrent labeling scale chain 0 • sphereFundamentalCandidate := by
  let coefficient := refinedCyclePointCurrent labeling scale chain 0
  calc
    faceRealization (refinedCyclePointCurrent labeling scale chain) =
        faceRealization (coefficient • fundamentalFaceChain) := by
      apply congrArg faceRealization
      exact refinedCyclePointCurrent_coordinates labeling scale chain cycle
    _ = coefficient • faceRealization fundamentalFaceChain := map_smul _ _ _
    _ = coefficient • sphereFundamentalCandidate := by
      rw [faceRealization_fundamental]

section Audit

#print axioms refinedCyclePointCurrent_boundary_zero
#print axioms refinedCyclePointCurrent_coordinates
#print axioms faceRealization_refinedCyclePointCurrent

end Audit

end Soma.Holonics.Millennium.HodgeRefinedCycleCarrier
