import CMCurveCore
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The CM source on the actual homogeneous Weierstrass cubic

The invertible linear coordinate change [-X:iY:Z] preserves the actual
projective cubic ideal. This is a source-level homogeneous algebra law;
no Proj functor, cycle-class comparison, or global intersection number is
asserted here. The two standard chart formulas and their fixed point loci
are proved, so the point omitted by the affine curve ring stays visible.
-/

noncomputable section

namespace Holonics.Hodge.CMGraphSource

abbrev HomogeneousRing := MvPolynomial (Fin 3) ℂ

def projectiveCubic : HomogeneousRing := squareCurve.toProjective.polynomial

def homogeneousPullback (q : ℂ) : HomogeneousRing →ₐ[ℂ] HomogeneousRing :=
  MvPolynomial.aeval ![-MvPolynomial.X 0, MvPolynomial.C q * MvPolynomial.X 1,
    MvPolynomial.X 2]

theorem homogeneousPullback_cubic (q : ℂ) (hq : q ^ 2 = -1) :
    homogeneousPullback q projectiveCubic = -projectiveCubic := by
  simp [homogeneousPullback, projectiveCubic, WeierstrassCurve.Projective.polynomial,
    squareCurve, mul_pow, ← MvPolynomial.C_pow, hq]
  ring

def homogeneousIota := homogeneousPullback Complex.I
def homogeneousInverse := homogeneousPullback (-Complex.I)

theorem homogeneous_inverse_comp :
    homogeneousInverse.comp homogeneousIota = AlgHom.id ℂ HomogeneousRing := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;> simp [homogeneousIota, homogeneousInverse, homogeneousPullback,
    ← mul_assoc, ← MvPolynomial.C_mul]

theorem homogeneous_comp_inverse :
    homogeneousIota.comp homogeneousInverse = AlgHom.id ℂ HomogeneousRing := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;> simp [homogeneousIota, homogeneousInverse, homogeneousPullback,
    ← mul_assoc, ← MvPolynomial.C_mul]

def homogeneousIotaEquiv : HomogeneousRing ≃ₐ[ℂ] HomogeneousRing :=
  AlgEquiv.ofAlgHom homogeneousIota homogeneousInverse
    homogeneous_comp_inverse homogeneous_inverse_comp

def projectiveCubicIdeal : Ideal HomogeneousRing := Ideal.span {projectiveCubic}

theorem homogeneousIota_preserves_cubicIdeal :
    Ideal.map homogeneousIota projectiveCubicIdeal = projectiveCubicIdeal := by
  rw [projectiveCubicIdeal, Ideal.map_span]
  simp only [Set.image_singleton]
  rw [homogeneousIota, homogeneousPullback_cubic Complex.I Complex.I_sq]
  exact Ideal.span_singleton_neg (x := projectiveCubic)

/-- The two affine receiving faces of the same homogeneous cubic. -/
theorem cubic_in_affine_chart (x y : ℂ) :
    MvPolynomial.eval ![x, y, 1] projectiveCubic = y ^ 2 - (x ^ 3 - x) := by
  simp [projectiveCubic, WeierstrassCurve.Projective.eval_polynomial, squareCurve]
  ring

theorem cubic_in_infinity_chart (a b : ℂ) :
    MvPolynomial.eval ![a, 1, b] projectiveCubic = b - a ^ 3 + a * b ^ 2 := by
  simp [projectiveCubic, WeierstrassCurve.Projective.eval_polynomial, squareCurve]
  ring

/-- In Z=1, the CM fixed-point equations isolate (0,0). -/
theorem affine_fixed_point_iff (x y : ℂ) :
    (-x = x ∧ Complex.I * y = y) ↔ x = 0 ∧ y = 0 := by
  have hi : Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : (2 : ℂ) * x = 0 := by linear_combination -hx
    have hy' : (Complex.I - 1) * y = 0 := by linear_combination hy
    exact ⟨(mul_eq_zero.mp hx').resolve_left (by norm_num),
      (mul_eq_zero.mp hy').resolve_left hi⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- In Y=1 the same projective map is (a,b) -> (i*a,-i*b). -/
theorem infinity_chart_transport (a b : ℂ) :
    -a / Complex.I = Complex.I * a ∧ b / Complex.I = -Complex.I * b := by
  simp [div_eq_mul_inv]
  constructor <;> ring

theorem infinity_fixed_point_iff (a b : ℂ) :
    (Complex.I * a = a ∧ -Complex.I * b = b) ↔ a = 0 ∧ b = 0 := by
  have hi : Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hn : -Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : (Complex.I - 1) * a = 0 := by linear_combination ha
    have hb' : (-Complex.I - 1) * b = 0 := by linear_combination hb
    exact ⟨(mul_eq_zero.mp ha').resolve_left hi, (mul_eq_zero.mp hb').resolve_left hn⟩
  · rintro ⟨rfl, rfl⟩
    simp

#print axioms homogeneousPullback_cubic
#print axioms homogeneousIotaEquiv
#print axioms homogeneousIota_preserves_cubicIdeal
#print axioms cubic_in_affine_chart
#print axioms cubic_in_infinity_chart
#print axioms affine_fixed_point_iff
#print axioms infinity_chart_transport
#print axioms infinity_fixed_point_iff

end Holonics.Hodge.CMGraphSource
