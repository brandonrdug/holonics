# The continuous zero curve through a simple zero of H_t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/SimpleZeroCurve.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: persistence on every sufficiently small square, the selection of the unique zero of H_t in the square about z₀, and its continuity by persistence applied at (t₁, ζ t₁) on a smaller square inside the first. Assistant derivation for the proofs.
**Band:** Q z₀ η = OPEN SQUARE / PERSISTENCE FOR ALL η ≤ η₀ / sel = THE UNIQUE ZERO IN Q / ζ t₀ = z₀ / ζ CONTINUOUS ON (t₀ − ε, t₀ + ε) / H_t (ζ t) = 0, ζ t SIMPLE, UNIQUE IN Q / SAME FOR Ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.SimpleZeroCurve` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/SimpleZeroCurve.lean`, importing
`RH.SimpleZeroPersists`. Receiver: the selected zero `ζ t` of `H_t` in the square about a simple
zero `z₀` of `H_{t₀}`, as a function of `t`.

## Theorems

[definition] `Q z₀ η`, the open square of half-side `η`; `mem_Q_iff`, `center_mem_Q`, `Q_subset`.

[proved-derived] `simple_zero_persists_small`: persistence holds on every square of half-side
`η ≤ η₀`, not only one.

[definition] `sel f S z₀ t`, the unique zero of `H_t` in `S` when it exists; `sel_spec`, `sel_eq`.

[proved-derived] `exists_zero_curve`, `exists_zero_curve_riemannXi`: for a simple zero `z₀` of
`H_{t₀}` there are `η, ε > 0` and `ζ : ℝ → ℂ` with `ζ t₀ = z₀`, `ζ` continuous on
`(t₀ − ε, t₀ + ε)`, and for every `t` there `ζ t` is the unique zero of `H_t` in `Q z₀ η` and is
simple.

## Position on the route

[established-bounded] Every simple pair of `H_t` lies on a continuous curve of simple pairs for a
short time on either side. Its differentiability, with velocity `H″/H′` through
`zero_curve_velocity`, is the next owner; then the curve of a pair can be continued until it
either meets the critical line or leaves every bounded region, which is the exact dichotomy the
polynomial pair descent resolves through the Hadamard sum.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: differentiability of `ζ` with `ζ′ = H″/H′`.
