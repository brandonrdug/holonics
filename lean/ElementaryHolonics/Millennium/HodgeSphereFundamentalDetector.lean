import ElementaryHolonics.Millennium.HodgeSphereProductRulingProjections
import ElementaryHolonics.Foundation.BoundaryReceiver

/-!
# The exact degree-two detector needed by the tetrahedral sphere realization

The missing nonvanishing theorem does not require a computation of every singular-homology
group.  It is enough to construct one exact receiver on singular two-chains which

* annihilates every singular three-boundary; and
* evaluates the explicit tetrahedral sphere cycle to `1`.

Such a receiver descends through the genuine categorical singular-homology quotient.  This file
proves that descent and the resulting nonvanishing and ruling-injectivity theorems.  It also gives
the stronger finite reconstruction form: a degree-two receiver back to the four tetrahedral faces
which annihilates three-boundaries and is a left inverse to geometric realization automatically
supplies the scalar detector.

The remaining geometric construction is therefore sharply bounded.  Barycentric subdivision and
a tetrahedral star-carrier need only return `TetrahedralDegreeTwoReceiver`; a full chain-homotopy
equivalence in every degree is unnecessary for this gate.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereFundamentalDetector

open CategoryTheory CategoryTheory.Limits
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections
open Soma.Holonics.Foundation

abbrev RationalLine : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- A degree-two singular cocycle normalized on the explicit tetrahedral sphere cycle. -/
structure SphereDegreeTwoDetector where
  receive : SphereSingularChainComplex.X 2 ⟶ RationalLine
  boundary_zero : SphereSingularChainComplex.d 3 2 ≫ receive = 0
  fundamental_value : receive sphereFundamentalCandidate = 1

namespace SphereDegreeTwoDetector

/-- Restrict a chain detector to genuine singular cycles. -/
def onCycles (detector : SphereDegreeTwoDetector) :
    SphereSingularChainComplex.cycles 2 ⟶ RationalLine :=
  SphereSingularChainComplex.iCycles 2 ≫ detector.receive

theorem boundaries_zero (detector : SphereDegreeTwoDetector) :
    SphereSingularChainComplex.toCycles 3 2 ≫ detector.onCycles = 0 := by
  unfold onCycles
  rw [← Category.assoc, HomologicalComplex.toCycles_i, detector.boundary_zero]

/-- Before taking the homology quotient, the shared receiver law already separates the explicit
tetrahedral sphere cycle from the image of the singular three-boundary. -/
theorem sphereFundamentalCandidate_not_mem_boundary_range
    (detector : SphereDegreeTwoDetector) :
    sphereFundamentalCandidate ∉
      Set.range (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom := by
  exact not_mem_range_of_receiver_boundary_eq_zero
    (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom
    detector.receive.hom.toAddMonoidHom
    (fun source ↦ by
      change (SphereSingularChainComplex.d 3 2 ≫ detector.receive) source = 0
      rw [detector.boundary_zero]
      rfl)
    (by
      change detector.receive sphereFundamentalCandidate ≠ 0
      rw [detector.fundamental_value]
      norm_num)

/-- The detector after exact descent through rational singular homology. -/
def onHomology (detector : SphereDegreeTwoDetector) :
    RationalSingularHomology 2 sphereTopCat ⟶ RationalLine :=
  (SphereSingularChainComplex.homologyIsCokernel 3 2 (by simp)).desc
    (CokernelCofork.ofπ detector.onCycles detector.boundaries_zero)

@[reassoc]
theorem homologyπ_onHomology (detector : SphereDegreeTwoDetector) :
    SphereSingularChainComplex.homologyπ 2 ≫ detector.onHomology =
      detector.onCycles := by
  simpa [onHomology] using
    (Cofork.IsColimit.π_desc
      (SphereSingularChainComplex.homologyIsCokernel 3 2 (by simp))
      (t := CokernelCofork.ofπ detector.onCycles detector.boundaries_zero))

theorem homology_class_value (detector : SphereDegreeTwoDetector) :
    detector.onHomology sphereFundamentalHomologyClass = 1 := by
  change
    (sphereCycleLift ≫ SphereSingularChainComplex.homologyπ 2 ≫ detector.onHomology) 1 = 1
  rw [detector.homologyπ_onHomology]
  change (sphereCycleLift ≫ SphereSingularChainComplex.iCycles 2 ≫ detector.receive) 1 = 1
  rw [← Category.assoc, sphereCycleLift_i]
  change detector.receive ((1 : ℚ) • sphereFundamentalCandidate) = 1
  simpa using detector.fundamental_value

/-- A normalized degree-two detector certifies that the explicit sphere class is nonzero. -/
theorem sphereFundamentalHomologyClass_ne_zero (detector : SphereDegreeTwoDetector) :
    sphereFundamentalHomologyClass ≠ 0 := by
  intro hzero
  have hreceived := congrArg (fun homologyElement => detector.onHomology homologyElement) hzero
  change detector.onHomology sphereFundamentalHomologyClass =
    detector.onHomology 0 at hreceived
  rw [detector.homology_class_value, map_zero] at hreceived
  exact one_ne_zero hreceived

/-- The same detector closes the finite tetrahedral realization gate. -/
theorem tetrahedralHomologyRealization_injective (detector : SphereDegreeTwoDetector) :
    Function.Injective tetrahedralHomologyRealization :=
  tetrahedralHomologyRealization_injective_iff.mpr
    detector.sphereFundamentalHomologyClass_ne_zero

/-- The same detector proves independence of the two geometric ruling classes. -/
theorem rulingHomologyMap_injective (detector : SphereDegreeTwoDetector) :
    Function.Injective rulingHomologyMap :=
  rulingHomologyMap_injective_of_fundamentalClass_ne_zero
    detector.sphereFundamentalHomologyClass_ne_zero

end SphereDegreeTwoDetector

abbrev TetrahedralFaceModule : ModuleCat ℚ := ModuleCat.of ℚ FaceChain

def faceRealizationMorphism :
    TetrahedralFaceModule ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom faceRealization

def faceZeroCoordinate : TetrahedralFaceModule ⟶ RationalLine :=
  ModuleCat.ofHom
    { toFun := fun chain => chain 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/--
The smallest finite reconstruction object sufficient for nonvanishing.  It is only a receiver in
degrees two and three: no global singular/cellular comparison is assumed.
-/
structure TetrahedralDegreeTwoReceiver where
  receive : SphereSingularChainComplex.X 2 ⟶ TetrahedralFaceModule
  boundary_zero : SphereSingularChainComplex.d 3 2 ≫ receive = 0
  realization_retract : faceRealizationMorphism ≫ receive = 𝟙 TetrahedralFaceModule

namespace TetrahedralDegreeTwoReceiver

/-- Reading the coefficient of face zero turns finite reconstruction into orientation detection. -/
def detector (receiver : TetrahedralDegreeTwoReceiver) : SphereDegreeTwoDetector where
  receive := receiver.receive ≫ faceZeroCoordinate
  boundary_zero := by
    rw [← Category.assoc, receiver.boundary_zero]
    simp
  fundamental_value := by
    change faceZeroCoordinate (receiver.receive sphereFundamentalCandidate) = 1
    rw [← faceRealization_fundamental]
    change (faceRealizationMorphism ≫ receiver.receive ≫ faceZeroCoordinate)
      fundamentalFaceChain = 1
    rw [← Category.assoc, receiver.realization_retract, Category.id_comp]
    rfl

theorem sphereFundamentalHomologyClass_ne_zero
    (receiver : TetrahedralDegreeTwoReceiver) :
    sphereFundamentalHomologyClass ≠ 0 :=
  receiver.detector.sphereFundamentalHomologyClass_ne_zero

theorem tetrahedralHomologyRealization_injective
    (receiver : TetrahedralDegreeTwoReceiver) :
    Function.Injective tetrahedralHomologyRealization :=
  receiver.detector.tetrahedralHomologyRealization_injective

theorem rulingHomologyMap_injective (receiver : TetrahedralDegreeTwoReceiver) :
    Function.Injective rulingHomologyMap :=
  receiver.detector.rulingHomologyMap_injective

end TetrahedralDegreeTwoReceiver

section Audit

#print axioms SphereDegreeTwoDetector.sphereFundamentalHomologyClass_ne_zero
#print axioms SphereDegreeTwoDetector.sphereFundamentalCandidate_not_mem_boundary_range
#print axioms SphereDegreeTwoDetector.tetrahedralHomologyRealization_injective
#print axioms SphereDegreeTwoDetector.rulingHomologyMap_injective
#print axioms TetrahedralDegreeTwoReceiver.detector
#print axioms TetrahedralDegreeTwoReceiver.rulingHomologyMap_injective

end Audit

end Soma.Holonics.Millennium.HodgeSphereFundamentalDetector
