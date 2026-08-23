import ElementaryHolonics.Millennium.GeneralCollision

/-!
# GeneralCertificate: the duplication cancellation is bounded on every full-2-torsion curve

The height descent needs one thing the descent itself does not: a bound on how much the
numerator and denominator of the doubled abscissa can cancel.  On `y² = x(x−a)(x−b)`
the doubled abscissa is

```text
x(2P) = (x² − ab)² / (4·x(x−a)(x−b))
```

and the cancellation is bounded by the **resultant** of the two, which this file
exhibits as an explicit Bézout identity with small cofactors:

```text
( (a−b)² + 2(a+b)X − 3X² )·(X² − ab)²
  + ( 3X³ + (a+b)X² − 5abX − 2ab(a+b) )·X(X−a)(X−b)
  = (ab)²(a−b)²
```

That constant is exactly `Res((X²−ab)², X(X−a)(X−b))` up to the power of two the
denominator's `4` carries, and it vanishes only where the curve degenerates.  So the
cancellation divides the primes of bad reduction and nothing else — the same law the
congruent slice carries with `16n⁶`, now with the constant the two-parameter family
actually forces.

* **`theDuplicationCertificate`** — the identity, over any commutative ring.
* **`theCancellationDividesTheDiscriminant`** — any common divisor of the two
  polynomials' values divides `(ab)²(a−b)²`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralCertificate

open Soma.Holonics.Millennium

/-! ## 1. The Bézout certificate -/

/-- **THE DUPLICATION CERTIFICATE**: the numerator and denominator of the doubled
abscissa are coprime up to `(ab)²(a−b)²`, exhibited by explicit cofactors of degree
two and three.  This is the exact statement that the doubling map's cancellation is
supported on the discriminant. -/
theorem theDuplicationCertificate {R : Type*} [CommRing R] (a b X : R) :
    ((a - b) ^ 2 + 2 * (a + b) * X - 3 * X ^ 2) * (X ^ 2 - a * b) ^ 2
      + (3 * X ^ 3 + (a + b) * X ^ 2 - 5 * (a * b) * X - 2 * (a * b) * (a + b))
        * (X * (X - a) * (X - b))
      = (a * b) ^ 2 * (a - b) ^ 2 := by
  ring

/-- The same identity with the curve's own denominator `4y² = 4x(x−a)(x−b)`. -/
theorem theDuplicationCertificateWithFour {R : Type*} [CommRing R] (a b X : R) :
    (4 * ((a - b) ^ 2 + 2 * (a + b) * X - 3 * X ^ 2)) * (X ^ 2 - a * b) ^ 2
      + (3 * X ^ 3 + (a + b) * X ^ 2 - 5 * (a * b) * X - 2 * (a * b) * (a + b))
        * (4 * (X * (X - a) * (X - b)))
      = 4 * ((a * b) ^ 2 * (a - b) ^ 2) := by
  ring

/-! ## 2. The cancellation bound -/

/-- **THE CANCELLATION DIVIDES THE DISCRIMINANT**: any integer dividing both the
numerator `(m² − ab e⁴)²`-shape and the denominator of the doubled abscissa divides
`4(ab)²(a−b)²`.  Stated in the homogeneous form the height argument uses: for
integers, a common divisor of the two evaluated polynomials divides the certificate's
constant. -/
theorem theCancellationDividesTheDiscriminant (a b X d : ℤ)
    (h₁ : d ∣ (X ^ 2 - a * b) ^ 2) (h₂ : d ∣ X * (X - a) * (X - b)) :
    d ∣ (a * b) ^ 2 * (a - b) ^ 2 := by
  have := theDuplicationCertificate a b X
  rw [← this]
  exact dvd_add (Dvd.dvd.mul_left h₁ _) (Dvd.dvd.mul_left h₂ _)

/-- The certificate constant vanishes only where the curve degenerates. -/
theorem theCertificateConstantIsNonzero {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a - b ≠ 0) : (a * b) ^ 2 * (a - b) ^ 2 ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero 2 (mul_ne_zero ha hb)) (pow_ne_zero 2 hab)

/-! ## 3. The doubled abscissa in the certificate's shape -/

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium.GeneralFace

/-- **THE DOUBLED ABSCISSA IS THE CERTIFIED QUOTIENT**: on every full-2-torsion curve
the doubling map sends `x` to `(x² − ab)² / (4·x(x−a)(x−b))`, whose numerator and
denominator the certificate above separates. -/
theorem theDoubledAbscissaIsTheCertifiedQuotient {a b x y : ℚ}
    (hns : (E a b).Nonsingular x y) (hy : y ≠ 0) :
    (E a b).addX x x ((E a b).slope x x y y)
      = (x ^ 2 - a * b) ^ 2 / (4 * (x * (x - a) * (x - b))) := by
  have hcurve := onCurve hns
  have hyne : y ≠ (E a b).negY x y := by
    simp only [negY, E]
    intro hc
    exact hy (by linarith)
  have h4y : (4 : ℚ) * y ^ 2 ≠ 0 := by positivity
  obtain ⟨key, -, -⟩ := theDoublingIdentities hcurve
  rw [show (4 : ℚ) * (x * (x - a) * (x - b)) = 4 * y ^ 2 from by rw [hcurve]]
  rw [slope_of_Y_ne rfl hyne]
  simp only [addX, negY, E]
  rw [show y - (-y - 0 * x - 0) = 2 * y from by ring]
  rw [eq_div_iff h4y]
  have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
  have hexp : ∀ N : ℚ, (N / (2 * y)) ^ 2 * (4 * y ^ 2) = N ^ 2 := by
    intro N
    rw [div_pow]
    field_simp
    ring
  set N : ℚ := 3 * x ^ 2 + 2 * -(a + b) * x + a * b - 0 * y with hNdef
  have hNeq : N = 3 * x ^ 2 - 2 * (a + b) * x + a * b := by rw [hNdef]; ring
  calc (((N / (2 * y)) ^ 2 + 0 * (N / (2 * y)) - -(a + b) - x - x)) * (4 * y ^ 2)
      = (N / (2 * y)) ^ 2 * (4 * y ^ 2) + ((a + b) - 2 * x) * (2 * y) ^ 2 := by ring
    _ = N ^ 2 + ((a + b) - 2 * x) * (2 * y) ^ 2 := by rw [hexp]
    _ = (x ^ 2 - a * b) ^ 2 := by rw [hNeq]; linear_combination key

end Soma.Holonics.Millennium.GeneralCertificate
