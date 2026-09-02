# The rectangle winding integral of H_t is continuous in t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleWindingContinuity.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: the rectangle is compact, nonvanishing of H_{t₀} on its boundary persists near t₀ with a uniform lower bound by the tube lemma, and each edge integral of H_t′/H_t is continuous in t by dominated convergence with the joint continuity of H_t and H_t′. Assistant derivation for the proofs.
**Band:** closedRect COMPACT / boundaryRect COMPACT / H_{t₀} ≠ 0 ON ∂R ⇒ ∃ m > 0, ∀ᶠ t, ∀ ζ ∈ ∂R, m ≤ ‖H_t ζ‖ / t ↦ ∫_edge H_t′/H_t CONTINUOUS AT t₀ / t ↦ ∮_R H_t′/H_t CONTINUOUS AT t₀ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.RectangleWindingContinuity` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleWindingContinuity.lean`, importing
`RH.HeatFlowContinuity` and `RH.RectangleArgumentPrinciple`. Receiver: the function
`t ↦ rectIntegral (logDeriv (heatE t f)) z w`.

## Theorems

[proved-derived] `norm_le_of_mem_closedRect`, `isClosed_closedRect`, `isCompact_closedRect`,
`isCompact_boundaryRect`: the closed rectangle lies in the closed ball of radius `2(‖z‖+‖w‖)` and
is compact; so is its boundary.

[proved-derived] `eventually_boundary_ge`: if `H_{t₀} ≠ 0` on the boundary, there is `m > 0` with
`m ≤ ‖H_t ζ‖` for all boundary `ζ` and all `t` near `t₀`, by the minimum on the compact boundary
and `IsCompact.eventually_forall_of_forall_eventually`.

[proved-derived] `continuousAt_edge`: along any continuous edge parametrization inside the
boundary, `t ↦ ∫ H_t′/H_t` is continuous at `t₀`, by
`intervalIntegral.continuousAt_of_dominated_interval` with the constant bound `K/m`.

[proved-derived] `continuousAt_rectIntegral_logDeriv`: the four-edge rectangle integral of
`H_t′/H_t` is continuous in `t` at `t₀`.

## Position on the route

[established-bounded] By the corpus argument principle on rectangles, this integral is `2πi`
times the number of zeros of `H_t` inside the rectangle counted with multiplicity. A continuous
integer-valued function is locally constant, so the interior zero count of `H_t` cannot change
while no zero crosses the boundary: zeros of `H_t`, and in particular pairs, are neither created
nor destroyed in the interior of a rectangle except by entering or leaving through its boundary or
meeting on the critical line. The integrality and local constancy are the next owner.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the rectangle zero count of `H_t` as `2πi`-multiple, and its local
constancy in `t`.
