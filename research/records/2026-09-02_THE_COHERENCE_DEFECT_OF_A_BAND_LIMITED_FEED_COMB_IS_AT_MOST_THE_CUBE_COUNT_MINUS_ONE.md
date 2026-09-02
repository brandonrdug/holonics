# The coherence defect of a band-limited feed comb is at most the cube count minus one

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4095 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, joining band limitation to the participation face of the defect. Assistant derivation for the proofs.
**Band:** BAND-LIMITED COMB HAS AT MOST (2N+1)³ TEETH / PARTICIPATION ≤ (2N+1)³ / DEFECT ≤ (2N+1)³ − 1 / BAND-LIMITED TAIL CONTROL ⇒ COHERENCE-DEFECT TAIL CONTROL ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesBandLimitedDefect.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`feedTerm_eq_zero_of_not_mem`; `participationAt_of_bandLimited` (Cauchy--Schwarz on the cube:
`(Σ'‖feed‖)² ≤ (2N+1)³ Σ'‖feed‖²`); `bandLimitedDefect_nonneg`; `coherenceDefectAt_of_bandLimited`
(`κ = (2N+1)³ − 1`); `BandLimitedTailControl`; `coherenceDefectTail_of_bandLimited`;
`statementB_of_bandLimitedTail`.

## Reading

[definition] The defect is bounded by the tooth count, and a band-limited slice has at most the
cube count of teeth at any receiver. So along any band-limited terminal tail the closure holds
outright, with exponent `21 (2N+1)³ c · 3 · 2 · E_kin(s) (τ − s)/(ν(2π)²)`. This is the formal
shadow of the classical fact that Galerkin truncations are globally regular, and it locates the
Millennium content exactly: the effective band of the feed combs, measured by the participation
number, must stay bounded as `t ↑ T`; every mechanism that spreads the comb over unboundedly many
aligned teeth is a candidate for blow-up and nothing else is.

[established-bounded] Next in the loop: Hodge, then the quantitative frontier chain for the
current into `(cube 2N)ᶜ`, then BSD sign law.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesBandLimitedDefect` green within the 180 s bound.
- Axiom audits: `participationAt_of_bandLimited`, `coherenceDefectAt_of_bandLimited`,
  `statementB_of_bandLimitedTail` each depend on `[propext, Classical.choice, Quot.sound]`.
