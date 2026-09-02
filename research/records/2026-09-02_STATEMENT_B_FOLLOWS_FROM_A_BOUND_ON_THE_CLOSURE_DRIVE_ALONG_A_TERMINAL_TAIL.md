# Statement B follows from a bound on the closure drive along a terminal tail

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4083 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** GRÖNWALL WITH CONSTANT FORCING / CUBE FAMILY / SIXTH MOMENT BEYOND THE CUBE PAID BY W₁₁/(N+1)⁵ / TERMINAL-TAIL CLOSURE W₄(τ) ≤ W₄(s)·exp(b(τ−s)) / CLOSURE-DRIVE CONTROL ⇒ WEIGHTED TAIL ENERGY CONTROL ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesMomentClosure.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`le_exp_of_hasDerivAt_le`: `f' ≤ b f + G` on `[s, τ]`, `0 ≤ b`, `0 ≤ G` returns
`f τ ≤ (f s + G (τ − s)) exp(b (τ − s))` (antitone weighted difference, no integral).
`cubeFamily N`: the nonzero modes of the cube of radius `N`. `moment_six_le`:
`W₆ ≤ M₆(cube N) + W₁₁ / (N+1)⁵`. `closureDrive t = 3 K(t) / (ν (2π)²)`.
`momentEnergy_cubeFamily_riccati`: `M₄(cube N)' ≤ closureDrive · M₄(cube N) + ν(2π)² W₁₁/(N+1)⁵`.
`momentEnergy_cubeFamily_le`: the Grönwall passage on the cube family.
`moment_four_le`: with the eleventh moment finite and at most `B` on `[s, τ]` and the closure
drive at most `b` there, `W₄(τ) ≤ W₄(s) · exp(b (τ − s))` (`N → ∞` through
`Real.tsum_le_of_sum_le` and `le_of_forall_pos_lt_add`).
`ClosureDriveControl`: along a terminal tail `[s, T)`, the eleventh moment is finite, the closure
drive is at most `b`, and the eleventh moment is bounded on every compact `[s, τ]`, `τ < T`.
`weightedTailEnergy_of_closureDrive : ClosureDriveControl → WeightedTailEnergyControl` with
`m = 1`, `C = W₄(s) exp(b (T − s))`. `statementB_of_closureDrive`, `officialProblem_of_closureDrive`.

## Reading

[definition] The goal `weightedTail_energy_inequality` is reached: the fourth moment on the whole
terminal tail is paid by its value at the start of the tail and one exponential of the closure
drive. The closure drive carries only the second moment `W₂` (enstrophy-weight one above the
enstrophy) and the zero mode; the interior finiteness premise (`W₁₁` bounded on compacts
`[s, τ]`, `τ < T`) is the smoothness of the open solution on its own lifespan, not a bound at `T`.

[established-bounded] The remaining Millennium content is exactly the bound on `W₂` along a
terminal tail. Everything above `W₂` is now formally closed to `StatementB`. The next owner is
the second-moment Riccati with its own Young drive, and the ladder below it: `W₂` against `W₄`,
`W₀` (enstrophy) against `W₂`, and the energy identity at the base.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesMomentClosure` green within the 180 s bound.
- Axiom audits: `le_exp_of_hasDerivAt_le`, `moment_four_le`, `statementB_of_closureDrive` each
  depend on `[propext, Classical.choice, Quot.sound]`.
