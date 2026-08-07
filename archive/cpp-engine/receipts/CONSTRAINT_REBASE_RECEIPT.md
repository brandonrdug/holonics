# The constraint rebase

**Truth status:** `established-bounded` at the declared aperture; the group-theoretic step is
`proved-standard`.
**Evidence:** `implemented-exact` for every law; `computational-witness` for the readings.
**Specified by:** [the constraint record](../research/records/2026-08-06_THE_CONSTRAINT_IS_THE_CHI_THE_UNKNOWN_IS_THE_MISSING_CHART.md) §8.

A constraint is a `Chi` — two transports asserted equal — and the unknown is whatever the present
chart does not determine. This deed carries one constraint whose unknown is unreachable in the
chart it arrives in, returns the **exact obstruction** rather than a failure, founds the chart the
obstruction names, determines the unknown there, and retains what survives both readings.

## What was returned

```text
x^5 - x - 1, walked across the declared prime aperture

  p=2   type=(2,3)  squarefree  product agrees   -> transposition
  p=3   type=(5)    squarefree  product agrees   -> transitivity
  both witnesses stand; the aperture is not walked further

  obstruction: the group is the whole symmetric group on five points,
  which is not solvable, so no tower of cyclic charts reaches the root

the rebase, at the chart the obstruction names

  factor of degree 2:  1 1 1        (x^2 + x + 1)
  factor of degree 3:  1 0 1 1      (x^3 + x^2 + 1)
  the degrees account for 5 of 5 roots; the product equals the reduction

the control x^5 - 2

  at p=151 the roots are 22 25 49 90 116, and they form a coset of the
  fifth roots of unity: every root is one root times a unit
  the aperture was walked 36 primes deep before the case appeared
```

## The mechanism

**The obstruction is computed, not asserted.** Reducing the constraint at a prime and reading its
factor degrees gives, by Dedekind's theorem, the cycle type of a Frobenius element in the
constraint's own group. `p=3` returns an irreducible quintic, so the constraint is irreducible over
the integers and its group is **transitive**. `p=2` returns `(2,3)`, an element of order six whose
cube is a **transposition**. A transitive subgroup of the symmetric group on a prime number of
points that carries a transposition is the whole symmetric group; on five points that group is not
solvable. **Radicals supply only towers of cyclic charts, and no such tower covers it.** That is a
proof of unreachability, not a report of difficulty.

**Two primes decided it, out of thirty-six.** The aperture is walked in order and abandoned the
moment the witnesses stand. This is the traversal point in miniature: the body beelines to the
cases that settle the question instead of sweeping the family.

**The rebase is named by the obstruction.** The unknown that no radical tower reaches is determined
exactly in the finite chart at `p=2`, where the constraint resolves into an irreducible quadratic
and an irreducible cubic whose product is the reduction. The roots are the classes those factors
define.

**The invariant is what survives both charts.** `p=3` reads `(5)` and `p=2` reads `(2,3)`. The
readings disagree — that is the chart varying. Both cycle types are realized inside one group, and
it is the group, not either local reading, that is retained. This is the design law of the record's
§6: *retain what is invariant under rebase.*

**The control proves the asymmetry.** `x^5 - 2` has the same shape and a different reach. At
`p=151` its five roots form a coset of the fifth roots of unity — every root is one root times a
unit, which is exactly what a radical tower asserts globally, witnessed locally and exactly. Same
constraint shape; different reach; **the difference is proved on both sides rather than assumed on
either.**

## A defect found, and what found it

The first run reported `(5)` at `p=2` — wrong, since `x^5 + x + 1 = (x^2+x+1)(x^3+x^2+1)` over the
two-element field. The cause: the deed borrowed `arithmetic_field_detail::polynomial_divides`, whose
declared aperture is **degree four** and whose internal remainder is sized for it. A quintic writes
one slot past it.

**Using an organ past its declared aperture is a defect even when it appears to return**, and no
audit catches it — it is a capacity mismatch, not a banned token. The quintic now carries its own
remainder. This is the third instance of the same class in this construction, after the conditioning
contamination and the Phase 6 cost laws: **the receipt said the organ divides polynomials; the code
said it divides polynomials of degree at most four.**

Worth recording plainly: the deed's own product-agreement cross-check did **not** catch this,
because a single claimed factor equal to the whole reduction agrees with itself. A cross-check that
cannot fail on the degenerate case is not a cross-check there.

## Boundary

- **One constraint family, degree five, one aperture.** Thirty-six primes; the aperture is recorded
  and is the boundary of the reading, not a tuning parameter to widen when a case is missing.
- **The rebase is the finite chart, not the icosahedral one.** Klein's resolution transports on the
  icosahedron through hypergeometric functions; that chart needs carriers this body does not hold
  exactly. What is claimed is that the obstruction *names* a chart and that a chart it names
  determines the unknown — not that this is Klein's.
- **Non-solvability is proved; solvability of the control is witnessed locally, not proved.** The
  coset structure at one prime is the radical tower's local shadow. A global proof would exhibit the
  tower over the rationals and is not claimed.
- The constraint enters as declared coefficients. Reaching it **through the standing** — as the
  conditioned production deed reaches its declarations — is the join that remains.
