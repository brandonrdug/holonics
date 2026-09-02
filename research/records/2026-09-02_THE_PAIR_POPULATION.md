# The pair population

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9747 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, making the corpus's reading of ½ (the exponent at which a thing meets its own conjugate) a definition: the reflection s ↦ 1 − s̄ is a fixed-point-free involution on the zeros of ξ off the critical line, the Riemann hypothesis empties that population, and its emptiness puts every zero on the line. Assistant derivation for the proofs.
**Band:** reflect s = 1 − s̄ / reflect ∘ reflect = id / FIXED LOCUS = CRITICAL LINE / ξ(reflect s) = conj ξ(s) / pairPopulation = {ρ | ξ ρ = 0 ∧ reflect ρ ≠ ρ} / reflect PRESERVES IT WITHOUT FIXED POINTS / RH ⇒ pairPopulation = ∅ / pairPopulation = ∅ ⟺ EVERY ZERO OF ξ HAS Re = ½ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `reflect s = 1 − s̄`; `zeroSet = {ρ | ξ ρ = 0}`;
`pairPopulation = {ρ | ξ ρ = 0 ∧ reflect ρ ≠ ρ}`.

[proved-derived] `reflect_reflect`: an involution. `reflect_eq_self_iff`: fixed exactly on
`Re s = ½` (the corpus's `criticalLine_fixedLocus`). `riemannXi_reflect`:
`ξ(reflect s) = conj(ξ s)`, from `ξ(1 − s) = ξ(s)` and `ξ(s̄) = conj ξ(s)`.
`riemannXi_reflect_eq_zero_iff`, `reflect_mem_zeroSet`: the reflection preserves the zero set.

[proved-derived] `reflect_mem_pairPopulation`, `reflect_ne_self_of_mem`, `re_ne_half_of_mem`:
on the pair population the reflection is a fixed-point-free involution, so its members come in
pairs `{ρ, 1 − ρ̄}` straddling the line, and none has real part `½`.

[proved-derived] `pairPopulation_eq_empty_of_RH`: **the Riemann hypothesis empties the pair
population.** `re_eq_half_of_pairPopulation_eq_empty`, `pairPopulation_eq_empty_iff`: **the pair
population is empty exactly when every zero of `ξ` lies on the critical line.**

## Constants

[definition] `½ = 1/2` is the fixed locus of the reflection; no other constant appears.

## Holonic reading

[definition] The explicit formula reads the whole zero set of `ξ` against the prime comb; the
pair population is the part of that set the Riemann hypothesis forbids, and it has a structure
of its own: pairs exchanged by the reflection, each member paired with the point that meets it
across the line. The corpus's phase-flow ledger showed the zero comb has no coherence defect
and that the flow contracts toward the line; what remains is to show that no pair survives at
`t = 0`. That population, and not a positivity criterion, is the object of the route.

[established-bounded] The converse from the `ξ`-form to Mathlib's `RiemannHypothesis` needs the
classification of the zeros of `ζ` with nonpositive real part as the trivial zeros, which the
corpus has not returned; the forward direction is the corpus's `riemannXi_zero_re_of_RH`.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PairPopulation.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PrimeSideConverges`.
- Axiom audit for `pairPopulation_eq_empty_iff`, `pairPopulation_eq_empty_of_RH`,
  `reflect_mem_pairPopulation`: `[propext, Classical.choice, Quot.sound]`.
