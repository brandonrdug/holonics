# The frontier defect vanishes: the band budgets converge to the exact dissipation law

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 4093 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the frontier chain in the large-band limit on the NS line. Assistant derivation for the proofs.
**Band:** EXTERIOR MASS → 0 / JACOBIAN TAIL MASS → 0 / FRONTIER PRODUCT → 0 / FRONTIER DEFECT frontier(N) · exterior(2N) → 0 / dE_{C_{2N}}/dt + 2ν D_{C_{2N}} → 0 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `tendsto_exteriorMass`: the exterior `ℓ¹` velocity mass beyond `C_M` tends to
zero as `M → ∞`, being the tail of a summable series along the cofinal cubes.
`tendsto_jacobianTailMass`: the Jacobian coefficient tail mass beyond `C_N` tends to zero, entry
by entry in the sup-norm array.

[proved-derived] `tendsto_frontierBound`: the frontier product tends to zero; its first term is
squeezed between zero and the total `ℓ¹` mass times the Jacobian tail, its second is the exterior
mass times a constant. `tendsto_frontier_defect`: `frontier(N) · exterior(2N) → 0`.

[proved-derived] `tendsto_bandBudget`: `d/dt E_{C_{2N}} + 2ν D_{C_{2N}} → 0` as `N → ∞`, by the
frontier transfer bound of the previous owner.

## Holonic reading

[definition] The frontier chain is closed in the large-band limit. Every finite band leaks
current across its frontier, and the leak is bounded by tail quantities; as the band exhausts the
lattice the tails vanish and the band's law becomes the exact energy law of the whole solution.
The ledger half of the closure ladder is now complete from the single mode to the whole lattice:
modal law, band law with bounded leak, and the exact law as the limit.

[established-bounded] Convergence is at each fixed time in the open lifespan; uniformity in time
and the coherence half of the ladder remain the open content.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesFrontierVanishing.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesFrontierTransfer`.

Next in the loop: Hodge bigraded differential; RH certification of `ξ(½) ≠ 0`; BSD finiteness
of the analytic rank.
