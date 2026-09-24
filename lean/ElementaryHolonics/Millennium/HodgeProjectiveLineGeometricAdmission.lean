import ElementaryHolonics.Millennium.HodgeProjectiveLineSingularReduction

/-!
# A constructed geometric admission for the projective-line product Hodge carrier

This file collects the independently proved source returns into one admission object.  The object
contains no Hodge-conclusion or cycle-class-surjectivity field.  It retains:

* the quotient-level holomorphic atlas;
* the `S² × S²` topological realization;
* the injective homogeneous Segre map and its nonsingular quadric Jacobian;
* the two actual projection-fibre divisors and their one-point transverse intersection; and
* the cellular Hodge datum constructed from those same divisor and two-cell populations.

The conclusion for the admitted family is then derived from the finite-basis reconstruction
already proved for the cellular datum.  This is a genuine geometric/cellular Hodge instance.  The
upgrade to the classical singular-cohomology statement remains the explicit sphere-product
comparison isolated in `HodgeProjectiveLineSingularReduction`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineGeometricAdmission

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology
open Soma.Holonics.Millennium.HodgeProjectiveLineSegre

/-- [definition] A source-complete geometric/cellular realization.  Notice that no conclusion is
stored in the certificate. -/
structure Certificate where
  datum : Datum
  datum_eq : datum = cellularDatum
  atlas : HolomorphicSurfaceAtlasCertificate
  topologyModel :
    Surface ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  projectiveMap : Surface → ComplexProjectiveThreeSpace
  projectiveMap_eq : projectiveMap = segre
  projectiveMap_injective : Function.Injective projectiveMap
  projectiveMap_smoothQuadric : ∀ point, OnSmoothSegreQuadric (projectiveMap point)
  firstDivisor : Set Surface
  secondDivisor : Set Surface
  firstDivisor_eq : firstDivisor = rulingSupport .first
  secondDivisor_eq : secondDivisor = rulingSupport .second
  transverseIntersection :
    firstDivisor ∩ secondDivisor = ({(coordinatePoint, coordinatePoint)} : Set Surface)

/-- [proved-derived; formal-checked] Every field of the certificate is constructed on the actual
carrier. -/
def projectiveLineProductCertificate : Certificate where
  datum := cellularDatum
  datum_eq := rfl
  atlas := projectiveLineProductHolomorphicAtlas
  topologyModel := surfaceHomeomorphSphereProduct
  projectiveMap := segre
  projectiveMap_eq := rfl
  projectiveMap_injective := segre_injective
  projectiveMap_smoothQuadric := segre_mem_smooth_quadric
  firstDivisor := rulingSupport .first
  secondDivisor := rulingSupport .second
  firstDivisor_eq := rfl
  secondDivisor_eq := rfl
  transverseIntersection := rulingSupports_intersection

/-- [definition] The admitted family consists exactly of data carried by a constructed
geometric/cellular certificate. -/
def GeometricallyAdmitted (D : Datum) : Prop :=
  ∃ certificate : Certificate, certificate.datum = D

/-- [proved-derived; formal-checked] The actual projective-line product datum is admitted. -/
theorem cellularDatum_geometricallyAdmitted : GeometricallyAdmitted cellularDatum :=
  ⟨projectiveLineProductCertificate, rfl⟩

/-- [proved-derived; formal-checked] Every datum admitted by the constructed geometric certificate
has its Hodge conclusion, derived rather than stored in the certificate. -/
theorem conclusion_of_geometricallyAdmitted {D : Datum}
    (hadmitted : GeometricallyAdmitted D) : D.Conclusion := by
  obtain ⟨certificate, hcertificate⟩ := hadmitted
  rw [← hcertificate, certificate.datum_eq]
  exact cellularHodgeConclusion

/-- [proved-derived; formal-checked] The official Hodge receiver is inhabited on the complete
constructed geometric/cellular projective-line-product family. -/
theorem theHodgeConjectureIn_geometricallyAdmitted :
    TheHodgeConjectureIn GeometricallyAdmitted := by
  intro D hadmitted
  exact conclusion_of_geometricallyAdmitted hadmitted

/-- [proved-derived; formal-checked] Every rational Hodge occurrence in the actual admitted datum
has a returned rational combination of the two geometric projection-fibre divisors. -/
noncomputable def admittedCycleLift
    (hodgeClass : cellularDatum.rationalHodgeClasses) :
    Soma.Holonics.Millennium.HodgeConstructivePassage.CycleLiftFibre
      cellularDatum hodgeClass :=
  cellularCycleLift hodgeClass

section Audit

#print axioms projectiveLineProductCertificate
#print axioms cellularDatum_geometricallyAdmitted
#print axioms conclusion_of_geometricallyAdmitted
#print axioms theHodgeConjectureIn_geometricallyAdmitted
#print axioms admittedCycleLift

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineGeometricAdmission
