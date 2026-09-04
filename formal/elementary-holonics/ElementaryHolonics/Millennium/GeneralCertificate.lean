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


/-! ## 4. The two homogeneous certificates and the exact cancellation bound

Writing `x = p/q` in lowest terms, the doubled abscissa is `A/B` with

```text
A = (p² − ab·q²)²,      B = 2²·q·p·(p − a·q)·(p − b·q),
```

two binary quartics.  They have **two** Bézout relations, one killing `q` and one
killing `p`, and together those pin the cancellation exactly.  Constants are kept in
factored form so the composition stays visible: `2²·(ab)²·(a−b)²` is the discriminant
square times the denominator's `2²`, not an opaque integer. -/

/-- **THE `q`-SIDE CERTIFICATE**. -/
theorem theCertificateKillingTheDenominator (a b p q : ℤ) :
    (2 ^ 2 * q * ((a - b) ^ 2 * q ^ 2 + 2 * (a + b) * p * q - 3 * p ^ 2))
        * ((p ^ 2 - a * b * q ^ 2) ^ 2)
      + (3 * p ^ 3 + (a + b) * p ^ 2 * q - 5 * (a * b) * p * q ^ 2
          - 2 * (a * b) * (a + b) * q ^ 3)
        * (2 ^ 2 * q * p * (p - a * q) * (p - b * q))
      = 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 * q ^ 7 := by
  ring

/-- **THE `p`-SIDE CERTIFICATE**. -/
theorem theCertificateKillingTheNumerator (a b p q : ℤ) :
    (2 ^ 2 * p * ((a - b) ^ 2 * p ^ 2 + 2 * (a * b) * (a + b) * p * q
        - 3 * (a * b) ^ 2 * q ^ 2))
        * ((p ^ 2 - a * b * q ^ 2) ^ 2)
      + (-2 * (a * b) * (a + b) * p ^ 3 - 5 * (a * b) ^ 2 * p ^ 2 * q
          + (a + b) * (a * b) ^ 2 * p * q ^ 2 + 3 * (a * b) ^ 3 * q ^ 3)
        * (2 ^ 2 * q * p * (p - a * q) * (p - b * q))
      = 2 ^ 2 * (a - b) ^ 2 * p ^ 7 := by
  ring

/-- **THE CANCELLATION DIVIDES `2²·(ab)²·(a−b)²` EXACTLY**: for `x = p/q` in lowest
terms, any common divisor of the doubled abscissa's numerator and denominator divides
`2²·(ab)²·(a−b)²`.  The two certificates give divisibility of `K·q⁷` and `K·p⁷`; since
`p` and `q` are coprime so are their seventh powers, and the common divisor drops onto
`K` alone.  This is the height descent's exact input, on every full-2-torsion curve. -/
theorem theCancellationIsExactlyBounded (a b p q : ℤ) (hcop : IsCoprime p q) (d : ℤ)
    (h₁ : d ∣ (p ^ 2 - a * b * q ^ 2) ^ 2)
    (h₂ : d ∣ 2 ^ 2 * q * p * (p - a * q) * (p - b * q)) :
    d ∣ 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 := by
  set K : ℤ := 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 with hK
  have hq : d ∣ K * q ^ 7 := by
    rw [hK, ← theCertificateKillingTheDenominator a b p q]
    exact dvd_add (Dvd.dvd.mul_left h₁ _) (Dvd.dvd.mul_left h₂ _)
  have hp : d ∣ K * p ^ 7 := by
    have hsub : (2 : ℤ) ^ 2 * (a - b) ^ 2 * p ^ 7 ∣ K * p ^ 7 :=
      mul_dvd_mul_right ⟨(a * b) ^ 2, by rw [hK]; ring⟩ _
    refine dvd_trans ?_ hsub
    rw [← theCertificateKillingTheNumerator a b p q]
    exact dvd_add (Dvd.dvd.mul_left h₁ _) (Dvd.dvd.mul_left h₂ _)
  have hcop7 : IsCoprime (q ^ 7) (p ^ 7) := (hcop.symm).pow
  obtain ⟨u, v, huv⟩ := hcop7
  have hsum : d ∣ K * (u * q ^ 7 + v * p ^ 7) := by
    have e1 : d ∣ K * (u * q ^ 7) := by
      have : K * (u * q ^ 7) = u * (K * q ^ 7) := by ring
      rw [this]
      exact Dvd.dvd.mul_left hq _
    have e2 : d ∣ K * (v * p ^ 7) := by
      have : K * (v * p ^ 7) = v * (K * p ^ 7) := by ring
      rw [this]
      exact Dvd.dvd.mul_left hp _
    have : K * (u * q ^ 7 + v * p ^ 7) = K * (u * q ^ 7) + K * (v * p ^ 7) := by ring
    rw [this]
    exact dvd_add e1 e2
  rwa [huv, mul_one] at hsum

end Soma.Holonics.Millennium.GeneralCertificate
