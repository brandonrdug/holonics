# The heat step never creates a pair: Hermite–Poulain with parity

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9751 jobs)
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02, building forward preservation for the flow: the non-real root count of a real polynomial is even (conjugate pairs), Rolle on e^{x/a}p gives #real(p + a p′) ≥ #real(p) − 1 with multiplicity, so p ↦ p + a p′ and hence the heat step p ↦ p − λp″ = (1 − √λ D)(1 + √λ D)p never increase the non-real count. Assistant derivation for the proofs.
**Band:** CONJUGATION-INVARIANT MULTISET OF NON-REALS HAS EVEN CARD / nonreal p = #COMPLEX ROOTS WITH Im ≠ 0, EVEN / ROOT OF MULTIPLICITY k SURVIVES p + a p′ WITH MULTIPLICITY ≥ k−1 / ROLLE ON e^{x/a}p BETWEEN CONSECUTIVE ROOTS / #real(p + a p′) ≥ #real(p) − 1 / nonreal(p + a p′) ≤ nonreal p BY PARITY / nonreal(p − λp″) ≤ nonreal p / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `even_card_of_conj_invariant`: a conjugation-invariant multiset of non-real
complex numbers has even cardinality (strong induction, removing a pair `{x, x̄}` at a time).
`roots_map_ofReal`, `card_roots_map`, `nonreal_eq_card_filter`, `roots_map_conj`, `even_nonreal`:
for a real polynomial, `nonreal p := deg p − #real roots` equals the number of complex roots with
nonzero imaginary part, which is even (**parity**).

[definition] `step a p = p + a p′`; `heatStep λ p = p − λ p″`.

[proved-derived] `natDegree_step`, `step_ne_zero`; `rootMultiplicity_sub_one_le_step`: a real
root of multiplicity `k` survives with multiplicity at least `k − 1`;
`exists_step_root_between`: Rolle on `e^{x/a} p` puts a root of `step a p` strictly between
consecutive roots of `p`; `card_roots_toFinset_le_step`, `card_roots_le_step` (**the weighted
Rolle count**): `#real(step a p) ≥ #real(p) − 1` with multiplicity, mirroring Mathlib's
`card_roots_le_derivative`.

[proved-derived] `nonreal_step_le` (**Hermite–Poulain**): `nonreal (p + a p′) ≤ nonreal p`, by
the count and parity. `heatStep_eq`: `p − λp″ = (1 − √λ D)(1 + √λ D) p` for `λ ≥ 0`.
`nonreal_heatStep_le` (**the heat step never creates a pair**).

## Constants

[definition] `√λ · √λ = λ` is the only constant; the factorization is exact. `−1` in the count
is Rolle's one lost root, repaid by parity.

## Holonic reading

[definition] Forward in the flow no pair is born: each Euler step `1 − λD²` of the backward
heat flow is a product of two Hermite–Poulain steps, each of which can only lose non-real
roots. The pair population is monotone under every discrete step of the flow; what remains is
the passage from the Euler steps to `e^{−tD²}` itself, which needs the root count to be lower
semicontinuous in the coefficients (Hurwitz), and the semigroup law of the flow.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PolyaStep.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PairDescent`.
- Axiom audit for `nonreal_heatStep_le`, `nonreal_step_le`, `even_nonreal`:
  `[propext, Classical.choice, Quot.sound]`.
