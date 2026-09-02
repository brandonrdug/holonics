# The ℓ¹ moment of order s from the energy moment of order 2s + 2

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone within the Navier–Stokes tree; root module green, 9738 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, taking the next rung of the moment ladder named by the previous record: the three-dimensional lattice sum of sup⁻⁴ converges, and the arithmetic–geometric mean inequality against it makes the ℓ¹ velocity moment of order s finite from the vorticity energy moment of order 2s + 2. Assistant derivation for the proofs.
**Band:** SHELL sup = n HAS ≤ 26n² POINTS / Σ_{k} sup(k)⁻⁴ ≤ 26·ζ(2) / ‖û_k‖₁ ≤ √3·‖û_k‖₂ / sup^{w+2}·velPop ≤ momentPop(w)/(2π)² / AM–GM: sup^s‖û‖₁ ≤ (√3/2)(sup⁻⁴ + sup^{2s+4}velPop) / Summable(sup^s‖û_k‖₁) FROM Summable(momentPop(2s+2)) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Goal and finish line

[definition] **The `ℓ¹` moment of order `s` is finite whenever the energy moment of order
`2s + 4` is finite** (the previous record's next goal). Finish line:
`Summable (fun k ↦ sup(k)^s · ‖û_k‖₁)` from `Summable (momentPop (2s + 4))`, with the
three-dimensional lattice sum of `sup⁻⁴` bounded by a product expansion, compiled without
further hypotheses. Reached, and sharpened to order `2s + 2`.

## Statement

[proved-derived] `shell_subset_sdiff`, `card_shell_le`: the shell `sup(k) = n` inside any cube
lies in `cube(n) ∖ cube(n − 1)`, which has `(2n + 1)³ − (2n − 1)³ = 24n² + 2 ≤ 26n²` points.
`shell_term_le`, `sum_inv_sup_pow_four_le`: every finite partial sum of `sup(k)⁻⁴` is at most
`26 · Σ_n n⁻² = 26 · π²/6`, by fibering the cube over the sup-norm. `summable_inv_sup_pow_four`:
**the lattice sum converges**.

[proved-derived] `l1Pop_sq_le`, `l1Pop_le_sqrt`: `‖û_k‖₁² ≤ 3 ‖û_k‖₂²`.
`sup_pow_add_two_velPop_le`: `sup^{w+2} · ‖û_k‖₂² ≤ momentPop(w)/(2π)²`, from
`ω̂_k = 2πi k × û_k` and `sup(k)² ≤ |k|²`. `l1MomentTerm_le_of_ne`: for `k ≠ 0`,
`sup^s ‖û_k‖₁ ≤ (√3/2)(sup⁻⁴ + sup^{2s+4} ‖û_k‖₂²)` by `2ab ≤ a² + b²` with `a = sup⁻²`,
`b = sup^{s+2} ‖û_k‖₂`.

[proved-derived] `summable_l1MomentTerm` (**the rung**): `Summable (fun k ↦ sup(k)^s ‖û_k‖₁)`
from `Summable (momentPop (2s + 2))`; the `k = 0` term is handled as a single finite term.
`summable_l1MomentTerm_of_four`: the record's finish line with `2s + 4`, by monotonicity of the
moments.

## Constants

[definition] `26 = 24 + 2`: the shell count `(2n+1)³ − (2n−1)³ = 24n² + 2`, with `2 ≤ 2n²`.
`ζ(2) = π²/6` is Mathlib's Basel value. `√3` is the `ℓ¹`–`ℓ²` constant in three coordinates.
`(2π)²` is the curl multiplier. `2` in the arithmetic–geometric mean. All elementary product
expansions with lineage in the proofs.

## Holonic reading

[definition] The energy moments (vorticity, `ℓ²`) are what the dissipation law pays for; the
`ℓ¹` velocity moments are what the frontier transfer and the tail relevance consume. This rung
converts the former into the latter at a cost of two orders, through the lattice's own
geometry (its shells grow quadratically, so `sup⁻⁴` is summable). The moment ladder now runs
from the energy moment of order `2s + 2` to every `ℓ¹` moment of order `s`.

[established-bounded] The energy moments of order `2s + 2` remain hypotheses on the solution
(the eleventh moment in the closure statements); deriving them from the dissipation law along
a tail is the ladder's next rung, and is where the coherence-defect family enters.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesL1MomentLadder.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesMomentTailRelevance`.
- Axiom audit for `summable_l1MomentTerm`, `summable_inv_sup_pow_four`:
  `[propext, Classical.choice, Quot.sound]`.
