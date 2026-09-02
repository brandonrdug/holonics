# The harmonic representative: harmonic forms are the cohomology of a finite differential

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 2393 jobs for the owner cone; the root module was red at that commit and is repaired in the following commit)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the harmonic receiver of each cohomology class on the Hodge line. Assistant derivation for the proofs.
**Band:** CLOSED = ker d / EXACT = range d / CLOSED = HARMONIC ⊔ EXACT / HARMONIC ⊓ EXACT = ⊥ / IsCompl INSIDE THE CLOSED FORMS / HARMONIC ≃ₗ CLOSED ⧸ EXACT / finrank HARMONIC = finrank COHOMOLOGY / EXACTLY ONE HARMONIC REPRESENTATIVE PER CLASS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] For a `Differential` on a finite-dimensional real inner product space, `closed`
is the kernel of `d` and `exact` its range; `exact ≤ closed` by `d ∘ d = 0`, `harmonic ≤ closed`
by the harmonic characterisation, and `closed = harmonic ⊔ exact`
(`closed_eq_harmonic_sup_exact`) by the earlier decomposition of a closed form into a harmonic
form plus an exact form.

[proved-derived] Read inside the closed forms, the harmonic and exact submodules are complementary
(`isCompl_harmonicInClosed_exactInClosed`): disjoint by `harmonic ⊓ range d = ⊥`, codisjoint by
the decomposition. Mathlib's quotient-by-a-complement equivalence then returns the Hodge
isomorphism `harmonicEquivCohomology : harmonic ≃ₗ[ℝ] closed ⧸ exact`, hence
`finrank_harmonic_eq_finrank_cohomology`.

[proved-derived] `existsUnique_harmonic_representative`: every cohomology class has exactly one
harmonic representative. Existence takes the harmonic part of any lift; uniqueness reads the
difference of two harmonic representatives as harmonic and exact at once, hence zero.

## Holonic reading

[definition] A cohomology class is a receiver defined up to an exact defect; the harmonic
representative is the unique member of the class that is simultaneously closed and co-closed,
the member of least energy in its class. The isomorphism says the class and its harmonic
receiver carry the same information: the cohomology of the finite complex is realised inside the
complex itself, as the kernel of the Laplacian, with no quotient left to take.

[established-bounded] This is the finite-dimensional Hodge theorem for an abstract differential
on an inner product space. The Hodge conjecture concerns the rational (p,p)-classes of a
projective variety; this owner supplies the harmonic-representative mechanism that the
algebraic-cycle side would have to meet, and closes no conjecture.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HodgeHarmonicRepresentative.lean`
  compiles under `lake env lean` and
  `lake build ElementaryHolonics.Millennium.HodgeHarmonicRepresentative`; printed axioms
  `[propext, Classical.choice, Quot.sound]`.
- Registered in `ElementaryHolonics.lean` together with
  `ElementaryHolonics.Millennium.HodgeFiniteDecomposition`, which the earlier commit had left
  unregistered; the root module `ElementaryHolonics` builds with both.

Next in the loop: BSD sign law, NS frontier chain; on Hodge, the graded differential with a
bidegree and the (p,p)-harmonic receiver.
