import CMZChartSheaf
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
The radical in the actual ideal-sheaf comparison is removed by a narrow
polynomial proof of primality, without importing affine group/class-group
owners. The reduced cubic's Z-chart ideal is therefore the principal
normalized cubic ideal, by proof rather than an assumed identification.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial
open scoped Polynomial.Bivariate
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def zPlaneBivariateEquiv : ZChartPlane ≃ₐ[ℂ] ℂ[X][Y] :=
  ((MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).trans
    (MvPolynomial.finSuccEquiv ℂ 1)).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)))

@[simp] theorem zPlaneBivariateEquiv_x :
    zPlaneBivariateEquiv (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp [zPlaneBivariateEquiv, MvPolynomial.finSuccEquiv_apply,
    ]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, Fin.cases_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]
@[simp] theorem zPlaneBivariateEquiv_y :
    zPlaneBivariateEquiv (MvPolynomial.X 1) = Polynomial.X := by
  simp [zPlaneBivariateEquiv, MvPolynomial.finSuccEquiv_apply]

theorem zPlaneBivariateEquiv_cubic :
    zPlaneBivariateEquiv zAffineCubic = squareCurve.toAffine.polynomial := by
  simp [zAffineCubic, WeierstrassCurve.Affine.polynomial, squareCurve, sub_eq_add_neg]

abbrev ZChartSquareRing := AdjoinRoot squareCurve.toAffine.polynomial
def zChartBivariateEquiv : ZChartAway ≃+* ℂ[X][Y] :=
  zAwayEquivPlane.trans zPlaneBivariateEquiv.toRingEquiv
theorem zChartBivariateEquiv_cubic :
    zChartBivariateEquiv zNormalizedCubic = squareCurve.toAffine.polynomial := by
  rw [zChartBivariateEquiv, RingEquiv.trans_apply, zNormalizedCubic_image]
  exact zPlaneBivariateEquiv_cubic

theorem zChartBivariateIdeal_map :
    zCubicChartIdeal.map zChartBivariateEquiv.toRingHom =
      Ideal.span {squareCurve.toAffine.polynomial} := by
  rw [zCubicChartIdeal, Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span {zChartBivariateEquiv zNormalizedCubic} = _
  rw [zChartBivariateEquiv_cubic]

def zChartSquareEquiv : (ZChartAway ⧸ zCubicChartIdeal) ≃+* ZChartSquareRing :=
  Ideal.quotientEquiv zCubicChartIdeal (Ideal.span {squareCurve.toAffine.polynomial})
    zChartBivariateEquiv zChartBivariateIdeal_map.symm

theorem zCubicChartIdeal_prime_narrow : zCubicChartIdeal.IsPrime := by
  let : IsDomain ZChartSquareRing :=
    AdjoinRoot.isDomain_of_prime (squareCurve.toAffine.irreducible_polynomial.prime)
  have hk : zCubicChartIdeal = RingHom.ker
      (zChartSquareEquiv.toRingHom.comp (Ideal.Quotient.mk zCubicChartIdeal)) := by
    rw [RingHom.ker_equiv_comp, Ideal.mk_ker]
  rw [hk]
  exact RingHom.ker_isPrime _

theorem zReducedChartIdeal :
    (cubicIdealSheaf.ideal zAmbientAffineOpen).comap zAmbientChartRingIso.hom.hom =
      zCubicChartIdeal := by
  rw [zReducedChartIdeal_radical, zCubicChartIdeal_prime_narrow.radical]

#print axioms zChartSquareEquiv
#print axioms zCubicChartIdeal_prime_narrow
#print axioms zReducedChartIdeal
end Holonics.Hodge.CMGraphSource
