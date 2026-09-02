# The Green operator: the Laplacian is invertible on the harmonic complement

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 2395 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, returning the Green operator of the finite Hodge Laplacian on the Hodge line. Assistant derivation for the proofs.
**Band:** Δ SELF-ADJOINT / RANGE Δ ⊆ harmonicᗮ / Δ INJECTIVE ON harmonicᗮ (KERNEL = HARMONIC) / Δ SURJECTIVE ON harmonicᗮ BY FINITE DIMENSION / x = h + Δ y WITH h HARMONIC, y ⟂ HARMONIC / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `inner_laplacian_left`: the Laplacian `Δ = dδ + δd` is self-adjoint, by the
adjunction of `d` and `δ` applied twice.

[proved-derived] `laplacian_mem_orthogonal`: the range of `Δ` lies in the harmonic complement,
so `Δ` maps the complement into itself. `laplacianRestrict_injective`: on the harmonic
complement `Δ` is injective, since its kernel is the harmonic space and the harmonic space meets
its complement only at zero. `exists_green`: by finite dimension the restriction is surjective,
so every form orthogonal to the harmonic space is a Laplacian of a form orthogonal to the
harmonic space.

[proved-derived] `exists_harmonic_add_laplacian`: every form is a harmonic form plus the
Laplacian of a form in the harmonic complement, the Hodge--Green decomposition `x = H x + Δ G x`.

## Holonic reading

[definition] The Laplacian is the second-order defect operator of the complex; its kernel is the
harmonic space, the forms with no defect in either direction. On the complement of that kernel
the defect operator is invertible: every non-harmonic form is the defect of a unique form in the
complement. The Green operator is the receiver that returns a form from its defect, and the
decomposition says a form is exactly its harmonic part plus the returned defect.

[established-bounded] Finite-dimensional real inner product spaces; the operator `G` is
established by existence and uniqueness, not yet packaged as a linear map.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HodgeGreenOperator.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.HodgeLeastNorm`.

Next in the loop: BSD finiteness of the analytic rank; RH certification of `ξ(½) ≠ 0`.
