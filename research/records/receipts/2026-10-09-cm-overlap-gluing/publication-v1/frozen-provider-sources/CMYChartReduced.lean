import CMYChartSheaf
import CMYEisenstein
import Mathlib.RingTheory.AdjoinRoot

/-!
The reduced induced cubic's actual Y-chart ideal is principal. Its section
ring and scheme chart are constructed from the Eisenstein quotient.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev YChartCubicRing := AdjoinRoot yMonicCubic
def yChartBivariateEquiv : YChartAway ≃+* ℂ[X][X] :=
  yAwayEquivPlane.trans yPlaneBivariateEquiv.toRingEquiv
theorem yChartBivariateEquiv_cubic : yChartBivariateEquiv yNormalizedCubic = -yMonicCubic := by
  rw [yChartBivariateEquiv, RingEquiv.trans_apply, yNormalizedCubic_image]
  exact yPlaneBivariateEquiv_cubic
theorem yChartBivariateIdeal_map :
    yCubicChartIdeal.map yChartBivariateEquiv.toRingHom = Ideal.span {yMonicCubic} := by
  rw [yCubicChartIdeal, Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span {yChartBivariateEquiv yNormalizedCubic} = _
  rw [yChartBivariateEquiv_cubic, Ideal.span_singleton_neg]
def yChartCubicEquiv : (YChartAway ⧸ yCubicChartIdeal) ≃+* YChartCubicRing :=
  Ideal.quotientEquiv yCubicChartIdeal (Ideal.span {yMonicCubic})
    yChartBivariateEquiv yChartBivariateIdeal_map.symm

theorem yCubicChartIdeal_prime : yCubicChartIdeal.IsPrime := by
  let : IsDomain YChartCubicRing := AdjoinRoot.isDomain_of_prime yMonicCubic_irreducible.prime
  have hk : yCubicChartIdeal = RingHom.ker
      (yChartCubicEquiv.toRingHom.comp (Ideal.Quotient.mk yCubicChartIdeal)) := by
    rw [RingHom.ker_equiv_comp, Ideal.mk_ker]
  rw [hk]
  exact RingHom.ker_isPrime _

theorem yReducedChartIdeal :
    (cubicIdealSheaf.ideal yAmbientAffineOpen).comap yAmbientChartRingIso.hom.hom =
      yCubicChartIdeal := by
  rw [yReducedChartIdeal_radical, yCubicChartIdeal_prime.radical]

def yReducedCubicOpen : CMProjectiveCubic.Opens := cubicEmbedding ⁻¹ᵁ yAmbientAffineOpen.1
theorem yReducedCubicOpen_isAffine : IsAffineOpen yReducedCubicOpen :=
  yAmbientAffineOpen.2.preimage cubicEmbedding
theorem yReducedChartIdeal_map :
    yCubicChartIdeal.map yAmbientChartRingIso.hom.hom =
      cubicIdealSheaf.ideal yAmbientAffineOpen := by
  rw [← yReducedChartIdeal]
  exact Ideal.map_comap_of_surjective _ yAmbientChartRingIso.commRingCatIsoToRingEquiv.surjective _

def yCubicChartRingEquiv : Γ(CMProjectiveCubic, yReducedCubicOpen) ≃+* YChartCubicRing :=
  (cubicIdealSheaf.subschemeObjIso yAmbientAffineOpen).commRingCatIsoToRingEquiv.trans
    ((Ideal.quotientEquiv yCubicChartIdeal (cubicIdealSheaf.ideal yAmbientAffineOpen)
      yAmbientChartRingIso.commRingCatIsoToRingEquiv yReducedChartIdeal_map.symm).symm.trans
        yChartCubicEquiv)
def yReducedCubicChartIso : yReducedCubicOpen.toScheme ≅ Spec (.of YChartCubicRing) :=
  yReducedCubicOpen_isAffine.isoSpec ≪≫
    Scheme.Spec.mapIso (yCubicChartRingEquiv.symm.toCommRingCatIso.op)

#print axioms yCubicChartIdeal_prime
#print axioms yReducedChartIdeal
#print axioms yCubicChartRingEquiv
#print axioms yReducedCubicChartIso
end Holonics.Hodge.CMGraphSource
