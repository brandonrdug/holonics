import ElementaryHolonics.Foundation.BoundaryScalePassage

/-!
# Cycle compression returns its retained reflection seam

`HolonicGranularBoundaryRadiation` already owns receiver-founded granulation, scale-natural
boundary transport, reconstruction fibres, and integration by reflection.  This file does not
found another compression object.  It composes two adjacent `BoundaryScalePassage`s so that a
current, its boundary, and the boundary of that boundary travel through one declared scale cut.

The central theorem is exact.  If a transported cycle has a coarse filler and that filler has a
chosen fine predecessor, the predecessor need not fill the original cycle: their difference is a
retained seam in the kernel of the middle transport.  The original cycle is a boundary exactly
when this seam vanishes.  Faithful middle transport is one sufficient reconstruction law; without
it a coarse filling may erase a nonzero source obstruction.

This is the chain-level form of the project's compression doctrine.  In a material realization,
the retained seam is where a changed lattice phase, shock front, crystal interface, or unresolved
fine circulation must live.  Those constitutive identifications require their own realization
passages; the theorem here is the common algebra they must satisfy.
-/

namespace Soma.Holonics.Millennium.HolonicBoundaryCycleReflection

open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

universe u

/--
Two consecutive scale-natural boundary passages with a shared middle transport.

`upper` transports fillers and their cycle boundaries.  `lower` transports those cycles and their
outer boundaries.  The two `boundary_boundary` laws retain the source and target chain conditions
rather than inferring conservation from a single boundary form.
-/
structure BoundaryCyclePassage
    (Scalar FineFiller FineCycle FineOuter CoarseFiller CoarseCycle CoarseOuter : Type u)
    [Semiring Scalar]
    [AddCommMonoid FineFiller] [Module Scalar FineFiller]
    [AddCommMonoid FineCycle] [Module Scalar FineCycle]
    [AddCommMonoid FineOuter] [Module Scalar FineOuter]
    [AddCommMonoid CoarseFiller] [Module Scalar CoarseFiller]
    [AddCommMonoid CoarseCycle] [Module Scalar CoarseCycle]
    [AddCommMonoid CoarseOuter] [Module Scalar CoarseOuter] where
  upper : BoundaryScalePassage Scalar FineFiller FineCycle CoarseFiller CoarseCycle
  lower : BoundaryScalePassage Scalar FineCycle FineOuter CoarseCycle CoarseOuter
  middleTransport : lower.interiorTransport = upper.boundaryTransport
  fine_boundary_boundary : lower.fineBoundary.comp upper.fineBoundary = 0
  coarse_boundary_boundary : lower.coarseBoundary.comp upper.coarseBoundary = 0

namespace BoundaryCyclePassage

variable
    {Scalar FineFiller FineCycle FineOuter CoarseFiller CoarseCycle CoarseOuter : Type u}
    [Semiring Scalar]
    [AddCommMonoid FineFiller] [Module Scalar FineFiller]
    [AddCommMonoid FineCycle] [Module Scalar FineCycle]
    [AddCommMonoid FineOuter] [Module Scalar FineOuter]
    [AddCommMonoid CoarseFiller] [Module Scalar CoarseFiller]
    [AddCommMonoid CoarseCycle] [Module Scalar CoarseCycle]
    [AddCommMonoid CoarseOuter] [Module Scalar CoarseOuter]

variable (passage : BoundaryCyclePassage Scalar FineFiller FineCycle FineOuter
  CoarseFiller CoarseCycle CoarseOuter)

/-- Every fine filler has a closed fine boundary. -/
theorem fine_boundary_boundary_apply (filler : FineFiller) :
    passage.lower.fineBoundary (passage.upper.fineBoundary filler) = 0 := by
  exact LinearMap.congr_fun passage.fine_boundary_boundary filler

/-- Every coarse filler has a closed coarse boundary. -/
theorem coarse_boundary_boundary_apply (filler : CoarseFiller) :
    passage.lower.coarseBoundary (passage.upper.coarseBoundary filler) = 0 := by
  exact LinearMap.congr_fun passage.coarse_boundary_boundary filler

/-- A closed fine current remains closed after the declared scale passage. -/
theorem transport_closed (cycle : FineCycle)
    (closed : passage.lower.fineBoundary cycle = 0) :
    passage.lower.coarseBoundary (passage.upper.boundaryTransport cycle) = 0 := by
  rw [← passage.middleTransport, passage.lower.transport_boundary, closed, map_zero]

/-- A fine boundary remains a coarse boundary with its filler transported explicitly. -/
theorem transport_boundary (filler : FineFiller) :
    passage.upper.coarseBoundary (passage.upper.interiorTransport filler) =
      passage.upper.boundaryTransport (passage.upper.fineBoundary filler) :=
  passage.upper.transport_boundary filler

end BoundaryCyclePassage

section RetainedSeam

variable
    {Scalar FineFiller FineCycle FineOuter CoarseFiller CoarseCycle CoarseOuter : Type u}
    [CommRing Scalar]
    [AddCommGroup FineFiller] [Module Scalar FineFiller]
    [AddCommGroup FineCycle] [Module Scalar FineCycle]
    [AddCommGroup FineOuter] [Module Scalar FineOuter]
    [AddCommGroup CoarseFiller] [Module Scalar CoarseFiller]
    [AddCommGroup CoarseCycle] [Module Scalar CoarseCycle]
    [AddCommGroup CoarseOuter] [Module Scalar CoarseOuter]

variable {passage : BoundaryCyclePassage Scalar FineFiller FineCycle FineOuter
  CoarseFiller CoarseCycle CoarseOuter}

/--
The complete data behind a coarse boundary claim for one transported fine cycle.

The coarse filler alone is insufficient.  A reconstruction occurrence also carries a fine filler
which maps to it; the remaining mismatch is retained below rather than silently decoded.
-/
structure CompressedBoundaryLift (cycle : FineCycle) where
  coarseFiller : CoarseFiller
  fillsTransport : passage.upper.coarseBoundary coarseFiller =
    passage.upper.boundaryTransport cycle
  fineFiller : FineFiller
  reconstructsFiller : passage.upper.interiorTransport fineFiller = coarseFiller

namespace CompressedBoundaryLift

variable {cycle : FineCycle}
    (lift : CompressedBoundaryLift (passage := passage) cycle)

/-- The exact fine mismatch retained behind the coarse filling face. -/
def retainedSeam : FineCycle := passage.upper.fineBoundary lift.fineFiller - cycle

/--
The retained seam is invisible to the coarse middle receiver.

This is the exact information loss caused by the scale passage, not an estimated truncation error.
-/
theorem retainedSeam_transport_eq_zero :
    passage.upper.boundaryTransport lift.retainedSeam = 0 := by
  unfold retainedSeam
  rw [map_sub, ← passage.upper.transport_boundary,
    lift.reconstructsFiller, lift.fillsTransport, sub_self]

/-- The selected fine predecessor fills the source cycle exactly iff its retained seam vanishes. -/
theorem sourceBoundary_iff_retainedSeam_eq_zero :
    passage.upper.fineBoundary lift.fineFiller = cycle ↔ lift.retainedSeam = 0 := by
  exact sub_eq_zero.symm

/--
If the middle transport is faithful, a reconstructed coarse filling reflects to an exact source
filling.  Faithfulness is an explicit hypothesis; it is never inferred from matching counts,
dimensions, or one receiver value.
-/
theorem sourceBoundary_of_boundaryTransport_injective
    (faithful : Function.Injective passage.upper.boundaryTransport) :
    passage.upper.fineBoundary lift.fineFiller = cycle := by
  apply lift.sourceBoundary_iff_retainedSeam_eq_zero.mpr
  apply faithful
  simpa using lift.retainedSeam_transport_eq_zero

/-- A nonzero retained seam is a direct certificate that this reconstructed predecessor is not a
source filler even though its coarse image is one. -/
theorem not_sourceBoundary_of_retainedSeam_ne_zero
    (nonzero : lift.retainedSeam ≠ 0) :
    passage.upper.fineBoundary lift.fineFiller ≠ cycle := by
  exact fun fills ↦ nonzero (lift.sourceBoundary_iff_retainedSeam_eq_zero.mp fills)

end CompressedBoundaryLift

end RetainedSeam

section Control

/-! ## An exact receiver-insufficiency control -/

/-- Both boundaries and every scale transport collapse to zero.  This is a lawful chain passage,
but its middle transport is deliberately unfaithful. -/
def collapsedRationalCyclePassage :
    BoundaryCyclePassage ℚ ℚ ℚ ℚ ℚ ℚ ℚ where
  upper := {
    fineBoundary := 0
    coarseBoundary := 0
    interiorTransport := 0
    boundaryTransport := 0
    boundary_natural := by ext; simp
  }
  lower := {
    fineBoundary := 0
    coarseBoundary := 0
    interiorTransport := 0
    boundaryTransport := 0
    boundary_natural := by ext; simp
  }
  middleTransport := rfl
  fine_boundary_boundary := by ext; simp
  coarse_boundary_boundary := by ext; simp

/-- The transported nonzero source cycle has a coarse filler and a fine predecessor of that filler. -/
def collapsedNonzeroCycleLift :
    CompressedBoundaryLift (passage := collapsedRationalCyclePassage) (1 : ℚ) where
  coarseFiller := 0
  fillsTransport := by simp [collapsedRationalCyclePassage]
  fineFiller := 0
  reconstructsFiller := by simp [collapsedRationalCyclePassage]

/-- The coarse filling face has erased the complete nonzero source obstruction. -/
theorem coarseBoundaryCanEraseANonzeroSourceSeam :
    collapsedNonzeroCycleLift.retainedSeam = (-1 : ℚ) ∧
      collapsedNonzeroCycleLift.retainedSeam ≠ 0 ∧
      collapsedRationalCyclePassage.upper.coarseBoundary
          collapsedNonzeroCycleLift.coarseFiller =
        collapsedRationalCyclePassage.upper.boundaryTransport (1 : ℚ) := by
  refine ⟨?_, ?_, collapsedNonzeroCycleLift.fillsTransport⟩
  · norm_num [CompressedBoundaryLift.retainedSeam, collapsedNonzeroCycleLift,
      collapsedRationalCyclePassage]
  · norm_num [CompressedBoundaryLift.retainedSeam, collapsedNonzeroCycleLift,
      collapsedRationalCyclePassage]

end Control

section Audit

#print axioms BoundaryCyclePassage.transport_closed
#print axioms CompressedBoundaryLift.retainedSeam_transport_eq_zero
#print axioms CompressedBoundaryLift.sourceBoundary_of_boundaryTransport_injective
#print axioms coarseBoundaryCanEraseANonzeroSourceSeam

end Audit

end Soma.Holonics.Millennium.HolonicBoundaryCycleReflection
