import ElementaryHolonics.Foundation.ExactPartition
import ElementaryHolonics.Foundation.LatticeTransport
import ElementaryHolonics.Foundation.PrimeValuationRadixAtlas
import ElementaryHolonics.Foundation.ReceiverQuotient
import ElementaryHolonics.Geometry.DivisorAtlas
import ElementaryHolonics.Millennium.PlaceLedger

/-!
# The valuation--divisor--lattice atlas

This file is the composition surface for the exact arithmetic-interaction deed.  It keeps six
objects distinct:

1. a receiver quotient and its complete predecessor fibre;
2. a transport lift and its range obstruction;
3. a geometric partition and paired oriented boundary;
4. a natural-number factor witness through scalar multiplication;
5. a finite signed codimension-one divisor ledger; and
6. an integer-lattice map with kernel, image, cokernel, torsion, saturation, and finite index.

The existing holonic binary exponential quotient is imported rather than redefined.  The existing
prime/radix atlas is likewise imported as the arithmetic scalar receiver.  The new theorem below
places the established rational finite-place ledger into the signed-divisor carrier and proves
that inversion reverses the complete finitely supported ledger, not merely one coordinate.

This atlas is shared infrastructure for RH, BSD, Hodge, Yang--Mills, knot/three-manifold, fluid,
and complexity routes.  It proves none of their terminal conjectures by itself.
-/

namespace Soma.Holonics.Millennium.ValuationDivisorLatticeAtlas

open Soma.Holonics.Geometry.DivisorAtlas
open Soma.Holonics.Millennium.PlaceLedger

/-- [definition] A signed divisor ledger together with the proof that every occupied address is
actually prime.  The ambient natural address is an ordinal chart; `supportedOnPrimes` returns its
geometric/arithmetic typing. -/
structure PrimeSupportedDivisor where
  ledger : WeilDivisorLedger ℕ
  supportedOnPrimes : ∀ p, ledger p ≠ 0 → p.Prime

/-- [proved-derived; formal-checked] The finite-place valuation ledger of a nonzero rational,
returned as one finitely supported signed divisor population. -/
noncomputable def rationalFinitePlaceDivisor (x : ℚ) (hx : x ≠ 0) : PrimeSupportedDivisor where
  ledger := Finsupp.onFinset (places x) (ledger x) (by
    intro p hp
    by_contra hplace
    exact hp (theLedgerVanishesOffThePlaces hx hplace))
  supportedOnPrimes := by
    intro p hp
    have hplace : p ∈ places x := by
      by_contra hnot
      exact hp (by
        simp only [Finsupp.onFinset_apply]
        exact theLedgerVanishesOffThePlaces hx hnot)
    change p ∈ (x.num.natAbs * x.den).primeFactors at hplace
    exact Nat.prime_of_mem_primeFactors hplace

/-- The finitely supported ledger returns the existing local valuation at every prime address. -/
@[simp] theorem rationalFinitePlaceDivisor_apply (x : ℚ) (hx : x ≠ 0) (p : ℕ) :
    (rationalFinitePlaceDivisor x hx).ledger p = ledger x p := by
  simp [rationalFinitePlaceDivisor]

/-- [proved-derived; formal-checked] Rational inversion negates the complete signed finite-place
divisor ledger.  This is the oriented-difference law at all prime charts simultaneously. -/
theorem rationalFinitePlaceDivisor_inv (x : ℚ) (hx : x ≠ 0) :
    (rationalFinitePlaceDivisor x⁻¹ (inv_ne_zero hx)).ledger =
      -(rationalFinitePlaceDivisor x hx).ledger := by
  apply Finsupp.ext
  intro p
  simp only [rationalFinitePlaceDivisor_apply, Finsupp.neg_apply]
  exact theInversionNegatesTheLedger hx p

/-- [proved-derived; formal-checked] The scalar natural-divisor relation used by the earlier rank
bounds is exactly existence of a multiplication lift; it is not a decomposition of the source
geometry. -/
theorem arithmeticDivisorIsAMultiplicationLift (divisor value : ℕ) :
    divisor ∣ value ↔
      Nonempty (Soma.Holonics.Foundation.ExactPartition.NatFactorWitness divisor value) :=
  (Soma.Holonics.Foundation.ExactPartition.NatFactorWitness.nonempty_iff_dvd
    divisor value).symm

section Audit

#print axioms rationalFinitePlaceDivisor_apply
#print axioms rationalFinitePlaceDivisor_inv
#print axioms arithmeticDivisorIsAMultiplicationLift

end Audit

end Soma.Holonics.Millennium.ValuationDivisorLatticeAtlas
