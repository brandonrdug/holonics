# Moment-ladder tail relevance: the frontier defect pays a power of the radius

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 4094 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, joining the frontier chain to the moment ladder on the NS line. Assistant derivation for the proofs.
**Band:** (M+1)^s · EXTERIOR MASS ≤ L_s / (N+1)^s · JACOBIAN TAIL ≤ 2π L_{s+1} / (N+1)^s · FRONTIER ≤ 2π L_0 L_{s+1} + L_s J_∅ / (N+1)^s (2N+1)^s · DEFECT ≤ K_s / (N+1)^s (2N+1)^s · |dE/dt + 2νD| ≤ 2 K_s / CONSTANTS 2, 2π AS PRODUCT EXPANSIONS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Goal and finish line

[definition] Goal set from the holonic route (Navier--Stokes tail relevance and the moment
ladder): **the band budget defect at radius `N` pays `(N+1)^s (2N+1)^s` against a product
expansion of `ℓ¹` velocity moments.** Finish line: the inequality
`(N+1)^s (2N+1)^s · |dE_{C_{2N}}/dt + 2ν D_{C_{2N}}| ≤ 2 K_s`, compiled with the summability of
the moments of orders `s` and `s+1` as hypotheses. Reached by `pow_mul_abs_bandBudget_le`.

## Statement

[definition] `l1Moment s = Σ'_k sup(k)^s · ‖û_k‖₁`, the `ℓ¹` velocity moment of order `s`;
`momentConstant s = K_s = (2π · L_0 · L_{s+1} + L_s · J_∅) · L_s` with `J_∅` the total
Jacobian coefficient mass. The constants are the product expansions `2 = 2` and `2π = 2 · π`,
the latter from the Fourier multiplier of the Jacobian mode.

[proved-derived] `pow_mul_exteriorMass_le`: `(M+1)^s · exteriorMass M ≤ L_s`, because every
frequency outside `C_M` has sup-norm at least `M+1`. `norm_jacobianMode_le_sup`:
`‖J_k(c,d)‖ ≤ 2π · sup(k) · ‖û_k‖₁`. `pow_mul_jacobianTailMass_le`:
`(N+1)^s · J(C_N) ≤ 2π · L_{s+1}`.

[proved-derived] `pow_mul_frontierBound_le`: `(N+1)^s · frontier(N) ≤ 2π L_0 L_{s+1} + L_s J_∅`.
`pow_mul_frontierDefect_le`: `(N+1)^s (2N+1)^s · frontier(N) · exteriorMass(2N) ≤ K_s`.
`pow_mul_abs_bandBudget_le`: the finish line above.

## Holonic reading

[definition] The moment ladder weighs the comb by powers of the sup-norm; the tail relevance of
the frontier chain asked how fast the leak across a band's frontier vanishes. The answer is now
quantitative: each order of moment the solution carries buys one power of the radius on each of
the two frontiers, so the band's departure from pure dissipation is bounded by `2K_s` over the
product of the two radii to the `s`-th power. The qualitative limit of the previous owner is the
`s = 0` face; the moment ladder is the same statement read at every order.

[established-bounded] The moment summabilities are hypotheses. Deriving the `ℓ¹` moment of
order `s` from the energy moment of order `2s + 4` (Cauchy--Schwarz against the convergent
lattice sum of `sup^{-4}` in three dimensions) is the next rung.

## Next goal

[definition] **The `ℓ¹` moment of order `s` is finite whenever the energy moment of order
`2s + 4` is finite.** Finish line: `Summable (fun k ↦ sup(k)^s · ‖û_k‖₁)` from
`Summable (momentPop (2s + 4))`, with the three-dimensional lattice sum of `sup^{-4}` bounded by
a product expansion, compiled without further hypotheses.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesMomentTailRelevance.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesFrontierVanishing`.
