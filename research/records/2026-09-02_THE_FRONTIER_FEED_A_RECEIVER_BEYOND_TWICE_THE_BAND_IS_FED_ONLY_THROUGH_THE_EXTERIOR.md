# The frontier feed: a receiver beyond twice the band is fed only through the exterior

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 4064 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the frontier chain of the Fourier ledger on the NS line. Assistant derivation for the proofs.
**Band:** k ∉ C_{2N} ⇒ EVERY FEED HAS AN EXTERIOR PARTICIPANT / ADVECTION = BAND FEEDS + EXTERIOR FEEDS / BAND FEEDS ≤ BAND ℓ¹ MASS · JACOBIAN MASS BEYOND THE BAND / EXTERIOR FEEDS ≤ EXTERIOR ℓ¹ MASS · TOTAL JACOBIAN MASS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `feed_participant_exterior`: for a receiver `k ∉ C_{2N}` and any `p`, either
`p ∉ C_N` or `k − p ∉ C_N`. It is the feed-term face of the closed-triad law of
`NavierStokesFrequencyReach`, read through the symmetry of the cube.

[proved-derived] `advectionMode_eq_band_add_exterior`: the advection coefficient at `k` is the
finite sum of the feeds with `p ∈ C_N` plus the summable series of the feeds with `p ∉ C_N`.

[proved-derived] `norm_advectionMode_le_frontier`: for `k ∉ C_{2N}`,
`‖adv_k(o)‖ ≤ (Σ_{p ∈ C_N} ‖û_p‖₁) · J(C_N) + (Σ'_{p ∉ C_N} ‖û_p‖₁) · J(∅)`, where `J(F)` is the
Jacobian coefficient mass beyond `F`. The first product uses that every band feed into `k` has
its Jacobian leg outside the band; the second uses the exterior velocity mass directly.

## Holonic reading

[definition] The band `C_N` is the leader's interior; `C_{2N}` is the reach of one interaction.
A receiver beyond the reach cannot be fed by two interior participants: every current into it
crosses the frontier of the band at least once. The bound names the two ways a current crosses:
an interior velocity leg with an exterior Jacobian leg, or an exterior velocity leg. Both factors
are tail quantities, so the exterior current is controlled by the band's tails alone; the
cumulative-current ledger of the relevance owners now has its exterior source bounded.

[established-bounded] The bound is stated at the advection coefficient. Feeding it into the
Kirchhoff transfer and the cumulative current at the frontier is the next step of this chain.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesFrontierFeed.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesBandLimitedDefect`.

Next in the loop: RH line; on NS, the frontier bound carried into the transfer and the cumulative
current beyond `C_{2N}`.
