# The trivial zeros, and the Riemann hypothesis is the emptiness of the pair population

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9748 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, classifying the zeros of ζ left of Re s = 0 as the trivial zeros (Bernoulli values at the odd negative integers, the functional equation elsewhere), so that Mathlib's RiemannHypothesis is exactly the ξ-form and hence exactly the emptiness of the pair population. Assistant derivation for the proofs.
**Band:** B_{2k} ≠ 0 THROUGH ζ(2k) ≠ 0 / ζ(−k) ≠ 0 FOR ODD k / ζ(s) = 0 WITH Re s ≤ 0 ⟺ s = −2(n+1) / RiemannHypothesis ⟺ EVERY ZERO OF ξ HAS Re = ½ ⟺ pairPopulation = ∅ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `bernoulli_two_mul_ne_zero`: `B_{2k} ≠ 0` for `k ≠ 0`, since Mathlib's
`ζ(2k) = (−1)^{k+1} 2^{2k−1} π^{2k} B_{2k}/(2k)!` and `ζ(2k) ≠ 0`. `riemannZeta_neg_odd_ne_zero`:
`ζ(−k) ≠ 0` for odd `k`, from `ζ(−k) = (−1)^k B_{k+1}/(k+1)`.

[proved-derived] `riemannZeta_eq_zero_iff_of_re_nonpos` (**the trivial zeros**): for `Re s ≤ 0`,
`ζ(s) = 0` exactly when `s = −2(n + 1)`; at the nonpositive integers by the Bernoulli values
(`ζ(0) = −½`, odd `k` nonzero, even `k` trivial), elsewhere by the functional equation
`ζ(1 − s) = 2 (2π)^{−s} Γ(s) cos(πs/2) ζ(s)` with `ζ(1 − s) ≠ 0`.

[proved-derived] `riemannHypothesis_iff_xi`: Mathlib's `RiemannHypothesis` holds exactly when
every zero of `ξ` has real part `½`. `riemannHypothesis_iff_pairPopulation_eq_empty` (**the
Riemann hypothesis is the emptiness of the pair population**).

## Constants

[definition] `½` is the fixed locus; `−2(n + 1)` are the trivial zeros; no other constant.

## Holonic reading

[definition] The route's object is now named in Mathlib's own terms: the Riemann hypothesis is
the statement that the zero comb of `ξ` has no pair, no member exchanged with a distinct point
across the line by `s ↦ 1 − s̄`. The explicit formula reads that comb against the primes for
every Weil chart; the phase-flow ledger moves it; the pair population is what must be shown
empty at `t = 0`.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/TrivialZeros.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PairPopulation`.
- Axiom audit for `riemannHypothesis_iff_pairPopulation_eq_empty`,
  `riemannZeta_eq_zero_iff_of_re_nonpos`: `[propext, Classical.choice, Quot.sound]`.
