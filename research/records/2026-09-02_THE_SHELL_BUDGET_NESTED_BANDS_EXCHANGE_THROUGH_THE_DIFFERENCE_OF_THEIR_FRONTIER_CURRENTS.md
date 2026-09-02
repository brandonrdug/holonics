# The shell budget: nested bands exchange through the difference of their frontier currents

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4092 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, completing the finite band ledger. Assistant derivation for the proofs.
**Band:** SHELL MASS E_G − E_F = Σ_{G∖F} modeMass / SHELL BUDGET −2ν D_{G∖F} − 2 Σ_{G∖F} transfer / SHELL BUDGET THROUGH THE TWO FRONTIERS / CUMULATIVE CURRENT OF THE SHELL IS THE DIFFERENCE / ALL IDENTITIES / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesShellBudget.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`shellMass F G = E_G − E_F`; `shellMass_eq_sum`; `shellMass_nonneg`; `hasDerivAt_shellMass`:
`(E_G − E_F)' = −2ν Σ_{G∖F} λ_k ‖û_k‖² − 2 Σ_{G∖F} transfer k`; `hasDerivAt_shellMass_kirchhoff`:
`(E_G − E_F)' = −2ν(D_G − D_F) + 2 Σ'_{k∉G} transfer − 2 Σ'_{k∉F} transfer`; `cumulativeCurrent_sub`:
`C_G − C_F = (shell(τ) − shell(s))/2 + ν ∫ D_{G∖F}`.

## Reading

[definition] The finite ledger is complete: every band, every shell between nested bands, and
their cumulative currents are exact identities of the open solution, and the only exchange is
the conserved transfer current across frontiers. The Millennium content lives entirely in the
coherence of that current at the frontier as the cubes grow.

[established-bounded] Next in the loop: Hodge (the finite sphere-product ruling model's
repeated-label normalization seam remains the named next exact seam there), then RH conjugation
symmetry, then BSD sign law.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesShellBudget` green within the 180 s bound.
- Axiom audits: `hasDerivAt_shellMass_kirchhoff`, `cumulativeCurrent_sub` each depend on
  `[propext, Classical.choice, Quot.sound]`.
