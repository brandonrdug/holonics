# The multiplicity of the factorization is the analytic order

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8710 jobs for the owner cone; root module green, 9735 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, identifying the comb of a zero factorization with the divisor of the function: inside the open half disc the multiplicity is the analytic order, so the weighted interior sum of the argument principle is canonical in the function alone. Assistant derivation for the proofs.
**Band:** COFACTOR AT ρ = PRODUCT OVER THE OTHER ZEROS × UNIT, NONVANISHING AT ρ / f = (z − ρ)^{m_ρ} · COFACTOR ON THE DISC / analyticOrderAt f ρ = m_ρ INSIDE THE OPEN HALF DISC / ORDER 0 OFF THE COMB / DIVISOR ON ANY SUBSET OF THE HALF DISC = THE COMB / Σᶠ divisor·h = Σ_{ρ ∈ zeros ∩ U} m_ρ h(ρ) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `cofactor Z ρ z = (∏_{σ ∈ zeros ∖ {ρ}} (z − σ)^{m_σ}) · unit z`.

[proved-derived] `cofactor_ne_zero`: nonvanishing at `ρ` inside the open half disc.
`differentiableOn_cofactor`: holomorphic on the disc. `factor_cofactor`:
`f z = (z − ρ)^{m_ρ} · cofactor Z ρ z` on the disc for `ρ` in the comb.

[proved-derived] `analyticOrderAt_eq_mult`: for `f` holomorphic on the disc and `ρ` in the comb
inside the open half disc, `analyticOrderAt f ρ = m_ρ` (Mathlib's characterisation of the order
by a nonvanishing analytic cofactor). `analyticOrderAt_eq_zero_of_notMem`: off the comb, inside
the open half disc, the order is `0` since `f ≠ 0` there.

[proved-derived] `divisor_eq`: on any `U` inside the open half disc,
`divisor f U u = [u ∈ U] · [u ∈ zeros] · m_u`. `finsum_divisor_eq`:
`Σᶠ_u divisor f U u · h(u) = Σ_{ρ ∈ zeros} [ρ ∈ U] · m_ρ · h(ρ)`.

## Constants

[definition] No constant appears.

## Holonic reading

[definition] The interior comb of the rectangle argument principle is now the divisor of `ξ`
on the open rectangle, weighted by the test: a quantity of `ξ` alone. The finite-height explicit
formula therefore compares, for every selected height, a canonical partial zero comb against
the prime comb, the archimedean integrals, and the bounded horizontal edges; the factorization
is scaffolding that no longer appears in the statement.

[established-bounded] Remaining: the limit along the selected heights with a weight that
decays faster than any power on horizontal lines, and the convergence of the partial zero
combs to the full comb.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/FactorizationMultiplicity.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.HorizontalEdgeBound`.
- Axiom audit for `finsum_divisor_eq`, `analyticOrderAt_eq_mult`:
  `[propext, Classical.choice, Quot.sound]`.
