import ElementaryHolonics.Millennium.HodgeSphereFundamentalDetector
import ElementaryHolonics.Millennium.HodgeTetrahedralRealizationChainMap

/-!
# A genuine singular-to-tetrahedral reduction returns the Hodge detector

The finite tetrahedral target is now a chain complex rather than an isolated degree-two module.
Consequently, a chain map from the rational singular chains of `S²` automatically annihilates
singular three-boundaries in degree two: the target has no degree-three differential.  If its
degree-two component is also a left inverse to the four-face geometric realization, it supplies
the exact `TetrahedralDegreeTwoReceiver` already used by the sphere-product Hodge passage.

This removes `boundary_zero` from the geometric construction target.  The remaining source-specific
object is one chain map with one normalized retraction square.  Constructing it still owes all
subdivision, seam, and chart-independence data; no arbitrary assignment of a singular simplex to a
tetrahedral face is admitted here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralReduction

open CategoryTheory
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereFundamentalDetector
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap

/-- Every genuine chain map into the two-dimensional tetrahedral complex kills singular
three-boundaries at degree two. -/
theorem boundary_zero_of_chain_map
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex) :
    SphereSingularChainComplex.d 3 2 ≫ reduction.f 2 = 0 := by
  rw [← reduction.comm 3 2, tetrahedralChainComplex_d_three_two]
  simp

/-- A singular-to-finite chain map with an exact degree-two retraction supplies the previously
isolated tetrahedral receiver, and hence the normalized scalar detector. -/
def degreeTwoReceiverOfReduction
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex)
    (realization_retract :
      faceRealizationMorphism ≫ reduction.f 2 = 𝟙 TetrahedralFaceModule) :
    TetrahedralDegreeTwoReceiver where
  receive := reduction.f 2
  boundary_zero := boundary_zero_of_chain_map reduction
  realization_retract := realization_retract

/-- A retraction of the complete geometric chain map supplies the normalized degree-two receiver
without a separate component hypothesis. -/
def degreeTwoReceiverOfChainRetraction
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex)
    (chain_retract :
      tetrahedralRealizationChainMap ≫ reduction = 𝟙 tetrahedralChainComplex) :
    TetrahedralDegreeTwoReceiver := by
  apply degreeTwoReceiverOfReduction reduction
  have component_retract := congrArg
    (fun chainMap : tetrahedralChainComplex ⟶ tetrahedralChainComplex => chainMap.f 2)
    chain_retract
  change (ModuleCat.ofHom HodgeTetrahedralSphereComplex.faceRealization :
      ModuleCat.of ℚ HodgeTetrahedralSphereComplex.FaceChain ⟶
        SphereSingularChainComplex.X 2) ≫ reduction.f 2 =
      𝟙 (ModuleCat.of ℚ HodgeTetrahedralSphereComplex.FaceChain) at component_retract
  exact component_retract

theorem sphereFundamentalHomologyClass_ne_zero_of_reduction
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex)
    (realization_retract :
      faceRealizationMorphism ≫ reduction.f 2 = 𝟙 TetrahedralFaceModule) :
    HodgeSphereProductRulingProjections.sphereFundamentalHomologyClass ≠ 0 :=
  TetrahedralDegreeTwoReceiver.sphereFundamentalHomologyClass_ne_zero
    (degreeTwoReceiverOfReduction reduction realization_retract)

theorem tetrahedralHomologyRealization_injective_of_reduction
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex)
    (realization_retract :
      faceRealizationMorphism ≫ reduction.f 2 = 𝟙 TetrahedralFaceModule) :
    Function.Injective HodgeTetrahedralSphereComplex.tetrahedralHomologyRealization :=
  TetrahedralDegreeTwoReceiver.tetrahedralHomologyRealization_injective
    (degreeTwoReceiverOfReduction reduction realization_retract)

theorem rulingHomologyMap_injective_of_reduction
    (reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex)
    (realization_retract :
      faceRealizationMorphism ≫ reduction.f 2 = 𝟙 TetrahedralFaceModule) :
    Function.Injective rulingHomologyMap :=
  TetrahedralDegreeTwoReceiver.rulingHomologyMap_injective
    (degreeTwoReceiverOfReduction reduction realization_retract)

section Audit

#print axioms boundary_zero_of_chain_map
#print axioms degreeTwoReceiverOfReduction
#print axioms degreeTwoReceiverOfChainRetraction
#print axioms sphereFundamentalHomologyClass_ne_zero_of_reduction
#print axioms tetrahedralHomologyRealization_injective_of_reduction
#print axioms rulingHomologyMap_injective_of_reduction

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralReduction
