# The heat semigroup and the monotone pair count

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatSemigroup.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow: the semigroup e^{−sD²} e^{−tD²} = e^{−(s+t)D²} on real polynomials by the Cauchy product of exponential coefficients (binomial theorem and C(l,j)·j!·(l−j)! = l!), the flow is a one-parameter group, and forward preservation composed with the semigroup gives a non-increasing non-real count in t with real-rootedness absorbing. Assistant derivation for the proofs.
**Band:** Σ_{j≤l} (−s)^j/j!·(−t)^{l−j}/(l−j)! = (−(s+t))^l/l! / heatR s (heatR t p) = heatR (s+t) p / heatR (−t) (heatR t p) = p / nonreal(heatR t' p) ≤ nonreal(heatR t p) FOR t ≤ t' / REAL-ROOTED AT t IMPLIES REAL-ROOTED AT t' ≥ t / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.HeatSemigroup` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatSemigroup.lean`, importing
`RH.ForwardPreservation`. Receiver: the non-real root count `nonreal` of a real polynomial under the
backward heat flow `heatR t p = e^{−tD²} p`.

## Theorems

[proved-derived] `scalar_cauchy`: the Cauchy product of exponential coefficients,
`Σ_{j ≤ l} (−s)^j/j! · (−t)^{l−j}/(l−j)! = (−(s+t))^l/l!`, from the binomial theorem and
`C(l,j)·j!·(l−j)! = l!`.

[proved-derived] `heatR_heatR`: `heatR s (heatR t p) = heatR (s + t) p`. The double sum is folded
along diagonals (`Finset.sum_range_diag_flip`) after truncating each inner sum to the triangle on
which the iterated derivative survives.

[proved-derived] `heatR_zero`, `heatR_neg_heatR`, `heatR_injective`: the flow is a one-parameter
group on polynomials; `e^{tD²}` inverts `e^{−tD²}`, so no information is lost at any finite time.

[proved-derived] `nonreal_heatR_antitone`: for `t ≤ t'`, `nonreal (heatR t' p) ≤ nonreal (heatR t p)`.
This is forward preservation (`nonreal_heatR_le`) composed with the semigroup.

[proved-derived] `nonreal_heatR_eq_zero_of_le`: once `heatR t p` is real-rooted, so is `heatR t' p`
for every `t' ≥ t`. Real-rootedness is absorbing along the flow.

## Position on the route

[established-bounded] Together with `highest_pair_dead` (PairDescent) and `nonreal_heatR_le`
(ForwardPreservation), the polynomial face of the de Bruijn–Newman flow now carries: pairs move by
the comb flux, no pair is born, the population is non-increasing in `t`, and the highest simple pair
is dead by `t = y₀²/2`. The de Bruijn–Newman constant of a polynomial is therefore a well-defined
threshold, `Λ(p) = inf {t | nonreal (heatR t p) = 0}`, with the set on the right an up-set.

[established-bounded] Nothing here touches the face `t = 0` of `Ξ`. The polynomial face is exact;
the transport of these four facts to the entire function `H_t` is the open passage, and its `t = 0`
statement is the Riemann hypothesis itself. Axioms: `[propext, Classical.choice, Quot.sound]`; no
`sorry`.

[established-bounded] Next: the polynomial de Bruijn–Newman threshold as an owner, `Λ(p)` with
`Λ(p) ≤ y₀²/2` from pair descent and `Λ(p) ≥ 0` where `p` has a pair, then the Jensen-polynomial
approximants of `Ξ` as the passage from the polynomial face to `H_t`.
