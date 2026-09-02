# The frontier transfer: the band's net current is bounded by the frontier product times the exterior mass

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 4092 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, carrying the frontier bound into the Kirchhoff transfer on the NS line. Assistant derivation for the proofs.
**Band:** |transfer k| ≤ FRONTIER(N) · ‖û_k‖₁ BEYOND C_{2N} / EXTERIOR TRANSFER MASS ≤ FRONTIER(N) · EXTERIOR MASS(2N) / KIRCHHOFF: |Σ_{C_{2N}} transfer| ≤ THE SAME / |dE_{C_{2N}}/dt + 2νD| ≤ 2 · FRONTIER(N) · EXTERIOR MASS(2N) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `frontierBound N` is the frontier product of the previous owner; `exteriorMass M` is
the exterior `ℓ¹` velocity mass beyond `C_M`.

[proved-derived] `abs_transfer_le_frontier`: for `k ∉ C_{2N}`,
`|transfer k| ≤ frontierBound N · ‖û_k‖₁`, from the frontier bound on every output of the
advection coefficient.

[proved-derived] `tsum_compl_abs_transfer_le`: the exterior transfer mass beyond `C_{2N}` is at
most `frontierBound N · exteriorMass (2N)`. `abs_sum_transfer_cube_le`: by the Kirchhoff law the
net current into `C_{2N}` is the negative of the exterior transfer, so it obeys the same bound.

[proved-derived] `abs_deriv_bandMass_add_dissipation_le`:
`|d/dt E_{C_{2N}} + 2ν D_{C_{2N}}| ≤ 2 · frontierBound N · exteriorMass (2N)`, from the band
energy budget.

## Holonic reading

[definition] The cumulative-current ledger of the relevance owners had one unbounded entry: the
net current across the frontier of a band. That entry is now bounded by tail quantities of two
radii, the frontier product at radius `N` and the exterior mass at radius `2N`. The band's energy
therefore evolves as pure dissipation up to a defect controlled by what lies beyond it; a solution
whose tails vanish faster than its band dissipates is, on the band, a heat flow.

[established-bounded] The bound is uniform in the band's interior structure and does not use
the coherence defect; it is the ledger half of the closure ladder, not the coherence half.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesFrontierTransfer.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesFrontierFeed`.

Next in the loop: RH on-line mass against the argument-principle count; Hodge bigraded
differential.
