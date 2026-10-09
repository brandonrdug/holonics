import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! The exact CoordinateRing abbreviation from Mathlib's Affine/Point.lean,
without its point group, class-group and norm imports. Its field-domain
instance is proved directly from the same actual irreducible polynomial. -/
noncomputable section
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Affine
universe r
variable {R : Type r} [CommRing R] (W' : Affine R)
abbrev CoordinateRing : Type r := AdjoinRoot W'.polynomial
namespace CoordinateRing
noncomputable instance : Algebra R W'.CoordinateRing := inferInstance
noncomputable instance : Algebra R[X] W'.CoordinateRing := inferInstance
instance : IsScalarTower R R[X] W'.CoordinateRing := inferInstance
end CoordinateRing
instance coordinateRing_domain_of_field {F : Type r} [Field F] (W : Affine F) :
    IsDomain W.CoordinateRing := AdjoinRoot.isDomain_of_prime W.irreducible_polynomial.prime
#print axioms coordinateRing_domain_of_field
end WeierstrassCurve.Affine
