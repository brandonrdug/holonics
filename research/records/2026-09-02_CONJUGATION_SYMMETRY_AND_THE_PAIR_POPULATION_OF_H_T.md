# Conjugation symmetry and the pair population of H_t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/ConjugationEntire.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow: conj ∘ g ∘ conj has derivative conj g′ through the real Fréchet derivative of conjugation, iterated derivatives inherit the conjugation symmetry, the flow inherits it, and with reflection the pair population of H_t is closed under conjugation, s ↦ 1 − s, and reflect, reducing at t = 0 to the pair population of Ξ. Assistant derivation for the proofs.
**Band:** (conj ∘ g ∘ conj)′ = conj g′ / iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ f^{(n)} ∘ conj / H_t(conj z) = conj H_t(z) / H_0 = Ξ / H_t(reflect s) = conj H_t(s) / pairPopulationH t = {ρ | H_t ρ = 0 ∧ reflect ρ ≠ ρ} / pairPopulationH 0 = pairPopulation / CLOSED UNDER conj, 1 − ·, reflect / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.ConjugationEntire` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/ConjugationEntire.lean`, importing
`RH.ZeroDynamicsEntire` and `RH.PairPopulation`. Receiver: the value of `H_t` at `conj z` and at
`reflect z`, and the set `pairPopulationH t`.

## Theorems

[proved-derived] `hasDerivAt_conj_conj`: if `g` has derivative `g′` at `conj z` then
`w ↦ conj (g (conj w))` has derivative `conj g′` at `z`, via the real Fréchet derivative of
`conjCLE` and `hasFDerivAt_of_restrictScalars`.

[proved-derived] `iteratedDeriv_conj_conj`: `iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ f^{(n)} ∘ conj`
for entire `f`.

[proved-derived] `heatE_conj`: if `f (conj s) = conj (f s)` then `heatE t f (conj z) = conj (heatE t f z)`.

[proved-derived] `heatE_zero`: `heatE 0 f = f`.

[proved-derived] `heatE_riemannXi_conj`, `heatE_riemannXi_reflect`: `H_t (conj z) = conj (H_t z)`
and `H_t (reflect s) = conj (H_t s)`.

[definition] `pairPopulationH t = {ρ | H_t ρ = 0 ∧ reflect ρ ≠ ρ}`.

[proved-derived] `pairPopulationH_zero`: `pairPopulationH 0 = pairPopulation`, the pair population
of `Ξ` from `RH.PairPopulation`, so `RiemannHypothesis ↔ pairPopulationH 0 = ∅`.

[proved-derived] `reflect_mem_pairPopulationH`, `conj_mem_pairPopulationH`,
`one_sub_mem_pairPopulationH`: the pair population of `H_t` is closed under the three symmetries.

## Position on the route

[established-bounded] The pair population under the de Bruijn–Newman flow now exists as a family
of sets `pairPopulationH t`, symmetric under conjugation and reflection, with the Riemann
hypothesis as its emptiness at `t = 0`. What the corpus has for it: `H_t` entire, the backward
heat equation, the velocity of a simple zero, and, at the polynomial face, monotonicity of the
count and pair descent. What it does not have: the transport of monotonicity and descent to
`pairPopulationH t`, which rests on the Hadamard product of `H_t`.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the local count of the pair population is stable in `t`, by Hurwitz
for the locally uniform limit `H_s → H_t` as `s → t` on compact sets; then the Hadamard passage.
