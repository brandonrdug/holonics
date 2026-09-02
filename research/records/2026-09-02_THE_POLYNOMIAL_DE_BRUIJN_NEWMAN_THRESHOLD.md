# The polynomial de Bruijn–Newman threshold

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/DeBruijnNewmanPolynomial.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow: the real-rooted times of a polynomial form an up-set, their infimum is the polynomial threshold Λ(p), Λ(p) ≥ 0 when p carries a pair and Λ(p) ≤ 0 when p is real-rooted, and Hurwitz continuity of the flow at t = 0 gives the polynomial face of RH ⟺ Λ ≤ 0. Assistant derivation for the proofs.
**Band:** realRootedTimes p = {t | nonreal(heatR t p) = 0} IS AN UP-SET / Λ(p) = sInf realRootedTimes p / nonreal p ≠ 0 ⇒ 0 ≤ Λ(p) / nonreal p = 0 ⇒ Λ(p) ≤ 0 / coeff_j(heatR t p) CONTINUOUS IN t / REAL-ROOTED FOR ALL t > 0 ⇒ REAL-ROOTED AT 0 / nonreal p = 0 ⟺ Λ(p) ≤ 0 GIVEN A REAL-ROOTED TIME / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.DeBruijnNewmanPolynomial` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/DeBruijnNewmanPolynomial.lean`, importing
`RH.HeatSemigroup`. Receiver: the set of real-rooted times of a real polynomial under the backward
heat flow and its infimum.

## Theorems

[definition] `realRootedTimes p = {t | nonreal (heatR t p) = 0}`; `lambda p = sInf (realRootedTimes p)`.

[proved-derived] `mem_realRootedTimes_of_le`: the real-rooted times form an up-set (from
`nonreal_heatR_eq_zero_of_le`).

[proved-derived] `nonneg_of_mem`, `lambda_nonneg`, `bddBelow_realRootedTimes`: when `p` carries a
pair, every real-rooted time is non-negative, since a negative real-rooted time would flow forward
to real-rootedness at `t = 0`.

[proved-derived] `mem_of_lambda_lt`, `not_mem_of_lt_lambda`: strictly above the threshold the
population is empty (given one real-rooted time); strictly below it the population is non-empty
(given a pair at `t = 0`).

[proved-derived] `lambda_nonpos`: a real-rooted polynomial has threshold at most `0`, with the
unbounded-below case handled by the real infimum convention.

[proved-derived] `continuous_coeff_heatR`: each coefficient of `heatR t p` is a polynomial in `t`.

[proved-derived] `nonreal_eq_zero_of_forall_pos`: if `heatR t p` is real-rooted for every `t > 0`,
then `p` is real-rooted. Hurwitz (`nonreal_le_of_tendsto`) along `t = 1/(N+1) → 0`.

[proved-derived] `nonreal_eq_zero_iff_lambda_nonpos`: given some real-rooted time,
`nonreal p = 0 ↔ lambda p ≤ 0`. This is the polynomial face of `RH ⟺ Λ_DN ≤ 0`.

## Position on the route

[established-bounded] At the polynomial face the whole de Bruijn–Newman shape is now a theorem:
pairs move by the comb flux, no pair is born, the population is non-increasing, real-rootedness is
absorbing, and real-rootedness at `t = 0` is equivalent to the threshold being at most zero. The
only face left at the polynomial level is the existence of a real-rooted time for every `p`, which
is the Hermite asymptotics of `e^{−tD²} x^n` and is not yet an owner.

[established-bounded] None of this touches `Ξ`. The passage from the polynomial face to `H_t` is
the derivative-series flow `Σ_k (−t)^k/k! f^{(2k)}` on real entire functions of order below two,
its agreement with the polynomial flow, and its commutation with locally uniform polynomial
approximation; the `t = 0` statement of that passage is the Riemann hypothesis. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the derivative-series heat flow on entire functions of order below two.
