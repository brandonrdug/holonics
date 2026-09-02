# The periodic official alternative follows from a bounded fourth-moment tail energy

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: *"Stop vaguely gesturing at next steps, give me a goal to set so you can get shit done."* Goal set by the assistant and accepted by construction: `statementB_of_weightedTailEnergy`. Assistant derivation for the proofs.
**Band:** GOAL REACHED / BOUNDED CONTROL REPLACES CONTINUITY / LAGRANGE ON THE TORUS MODES / LATTICE WEIGHT 52 BY SHELL COUNTS / CAUCHY-SCHWARZ ON THE TAIL / STATEMENT B FROM ONE SCALAR / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## The goal

[definition] For every admitted solution, if there exist `m ≥ 1`, a start `s ∈ (0, T)`, and a
constant `C` such that every finite partial sum of `|k|_∞⁴ · E_k(t)` over modes with `|k|_∞ ≥ m` is
at most `C` for all `t ∈ (s, T)`, then `StatementB`. `E_k` is the modal vorticity energy of the
Riccati owners.

## Return

[proved-derived; formal-checked] `NavierStokesTailBoundedControl.lean`: a constant aligned strain
budget needs no measurability, continuity, or integrability; `TailBoundedControl`
(some radius has a tail mass bounded on a terminal tail) returns `StatementB`
(`statementB_of_tailBounded`).

[proved-derived; formal-checked] `NavierStokesModeLagrange.lean`:
`sum_norm_sq_complexCross_of_dot_eq_zero`, Lagrange on a divergence-free mode,
`Σ_i |(k × v)_i|² = |k|² |v|²`, proved by `linear_combination` against the real and imaginary parts
of `k · v = 0`; `sum_norm_sq_frequencyCurlMultiplier` (the vorticity mode's energy is
`(2π)² |k|² |v|²`); `sum_norm_sq_fourierJacobianMode` (the Jacobian mode's Frobenius norm is the
same); `norm_fourierJacobianMode_sq_le` (every Jacobian entry is paid by the modal energy).

[proved-derived; formal-checked] `NavierStokesWeightedTailEnergy.lean` (registered; `lake build`
job count in the commit receipt; axioms `[propext, Classical.choice, Quot.sound]` on every
theorem; no `sorry`):

- `sum_inv_sq_Icc_le`, `sum_inv_sq_le_two`: `Σ j⁻² ≤ 2`, by induction with the telescoping bound
  `2 − 1/n`.
- `card_shell_le`: the shell at sup-norm `j ≥ 1` carries at most `26 j²` modes, from
  `(2j+1)³ − (2j−1)³ = 24 j² + 2`.
- `sum_inv_pow_four_le`: every finite partial sum of `|k|_∞⁻⁴` over nonzero modes is at most
  `52 = 26 · 2`, by fibring over the sup-norm.
- `norm_jacobianMode_sq_le_modalEnergy`: on the actual slice, every Jacobian entry squared is at
  most the modal energy, through the mode identification and divergence-freeness.
- `sum_norm_jacobianMode_le`: Cauchy--Schwarz on a finite family, `Σ ‖J_{ij}(q)‖ ≤ √(52 C)`.
- `tailMass_le_of_weighted`: the Jacobian tail mass beyond the cube of radius `m` is at most
  `√(52 C)`, through `Real.tsum_le_of_sum_le`.
- `WeightedTailEnergyControl`, `tailBoundedControl_of_weightedTailEnergy`,
  `statementB_of_weightedTailEnergy`, `officialProblem_of_weightedTailEnergy`.

## What it says

[interpretation] The periodic official alternative is now the boundedness of one scalar function
of time, `W₄(t) = Σ_{|k|_∞ ≥ m} |k|_∞⁴ E_k(t)`, on a terminal tail. The hypothesis carries a count
of modes per shell, the fourth power of the sup-norm, the modal energy, and one constant; no
analytic vocabulary. The constants are product expansions: `52 = 2 · 26`, `26 = 24 + 2` from the
shell count, `2` from the telescoping series. The Riccati and Gronwall owners act on `E_k`
directly, so the next object is the weighted Riccati inequality for `W₄` itself.

## What this does not establish

[open] `WeightedTailEnergyControl` is not inhabited. Nothing here bounds `W₄`.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesTailBoundedControl.lean`,
`ElementaryHolonics/Millennium/NavierStokesModeLagrange.lean`,
`ElementaryHolonics/Millennium/NavierStokesWeightedTailEnergy.lean` (all new; registered).
