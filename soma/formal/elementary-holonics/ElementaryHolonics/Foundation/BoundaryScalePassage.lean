import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Scale-natural boundary transport

This file is the small dependency owner of `BoundaryScalePassage`.  The definition and theorems
were previously embedded in `HolonicGranularBoundaryRadiation`; extracting them changes no name or
statement.  It lets chain, topology, and physical realizations share the same boundary-naturality
law without importing any one constitutive realization.
-/

namespace Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

/-- One scale passage transports both interior and boundary sections and makes boundary formation
commute.  It does not prescribe how either grain was founded. -/
structure BoundaryScalePassage
    (Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary : Type*)
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary] where
  fineBoundary : FineInterior →ₗ[Scalar] FineBoundary
  coarseBoundary : CoarseInterior →ₗ[Scalar] CoarseBoundary
  interiorTransport : FineInterior →ₗ[Scalar] CoarseInterior
  boundaryTransport : FineBoundary →ₗ[Scalar] CoarseBoundary
  boundary_natural :
    coarseBoundary.comp interiorTransport = boundaryTransport.comp fineBoundary

namespace BoundaryScalePassage

variable
    {Scalar FineInterior FineBoundary MiddleInterior MiddleBoundary
      CoarseInterior CoarseBoundary : Type*}
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid MiddleInterior] [Module Scalar MiddleInterior]
    [AddCommMonoid MiddleBoundary] [Module Scalar MiddleBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]

/-- Boundary current may be formed before or after one lawful grain transport. -/
theorem transport_boundary
    (passage : BoundaryScalePassage Scalar FineInterior FineBoundary
      CoarseInterior CoarseBoundary)
    (current : FineInterior) :
    passage.coarseBoundary (passage.interiorTransport current) =
      passage.boundaryTransport (passage.fineBoundary current) := by
  exact LinearMap.congr_fun passage.boundary_natural current

/-- Scale-natural boundary passages compose without introducing a privileged level. -/
def comp
    (fineToMiddle : BoundaryScalePassage Scalar FineInterior FineBoundary
      MiddleInterior MiddleBoundary)
    (middleToCoarse : BoundaryScalePassage Scalar MiddleInterior MiddleBoundary
      CoarseInterior CoarseBoundary)
    (middleBoundary_agrees :
      middleToCoarse.fineBoundary = fineToMiddle.coarseBoundary) :
    BoundaryScalePassage Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary where
  fineBoundary := fineToMiddle.fineBoundary
  coarseBoundary := middleToCoarse.coarseBoundary
  interiorTransport := middleToCoarse.interiorTransport.comp fineToMiddle.interiorTransport
  boundaryTransport := middleToCoarse.boundaryTransport.comp fineToMiddle.boundaryTransport
  boundary_natural := by
    ext current
    simp only [LinearMap.comp_apply]
    calc
      middleToCoarse.coarseBoundary
          (middleToCoarse.interiorTransport (fineToMiddle.interiorTransport current)) =
        middleToCoarse.boundaryTransport
          (middleToCoarse.fineBoundary (fineToMiddle.interiorTransport current)) :=
            middleToCoarse.transport_boundary (fineToMiddle.interiorTransport current)
      _ = middleToCoarse.boundaryTransport
          (fineToMiddle.boundaryTransport (fineToMiddle.fineBoundary current)) :=
            congrArg middleToCoarse.boundaryTransport
              (by
                rw [middleBoundary_agrees]
                exact fineToMiddle.transport_boundary current)

/-- The composed scale passage carries the fine boundary to the coarse boundary in one step. -/
theorem comp_transport_boundary
    (fineToMiddle : BoundaryScalePassage Scalar FineInterior FineBoundary
      MiddleInterior MiddleBoundary)
    (middleToCoarse : BoundaryScalePassage Scalar MiddleInterior MiddleBoundary
      CoarseInterior CoarseBoundary)
    (middleBoundary_agrees :
      middleToCoarse.fineBoundary = fineToMiddle.coarseBoundary)
    (current : FineInterior) :
    (fineToMiddle.comp middleToCoarse middleBoundary_agrees).coarseBoundary
        ((fineToMiddle.comp middleToCoarse middleBoundary_agrees).interiorTransport current) =
      (fineToMiddle.comp middleToCoarse middleBoundary_agrees).boundaryTransport
        ((fineToMiddle.comp middleToCoarse middleBoundary_agrees).fineBoundary current) := by
  exact (fineToMiddle.comp middleToCoarse middleBoundary_agrees).transport_boundary current

end BoundaryScalePassage

section Audit

#print axioms BoundaryScalePassage.transport_boundary
#print axioms BoundaryScalePassage.comp_transport_boundary

end Audit

end Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation
