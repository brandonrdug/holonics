# The velocity mass is paid by the kinetic energy at the start of the tail

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4086 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, discharging the velocity-mass premise of `IncoherentControl`. Assistant derivation for the proofs on the line's existing Parseval and energy--dissipation owners.
**Band:** PARSEVAL ON THE SLICE / VELOCITY MASS ≤ 3·2·E_kin / KINETIC ENERGY NONINCREASING ON THE OPEN LIFESPAN / VELOCITY-MASS PREMISE DISCHARGED / INCOHERENT TAIL CONTROL ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesVelocityMassEnergy.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`velocityMode_eq_smoothSliceFourierL2`; `tsum_sq_velocityMode_eq` (Parseval per component:
`Σ'_p ‖û_p(c)‖² = ∫_cube (u_c)²`); `summable_sq_velocityMode`; `velocityMass_le_kineticEnergy`:
`V(t) ≤ 3 · 2 · E_kin(t)`. `periodicKineticEnergy_le_of_le`: `E_kin(b) ≤ E_kin(a)` for
`0 < a ≤ b < T` (the unforced energy--dissipation identity with nonnegative dissipation).
`velocityMass_le_of_le`: `V(σ) ≤ 3 · 2 · E_kin(s)` on the tail. `IncoherentTailControl` (incoherence
at every nonzero receiver and interior finiteness only); `incoherentControl_of_tail`;
`moment_two_le_kineticEnergy`:

```text
W₂(τ) ≤ W₂(s) · exp( 21 c · 3 · 2 · E_kin(s) · (τ − s) / (ν (2π)²) ),   c = 3³ (2π)² · 3 · 2³;
```

`statementB_of_incoherentTail`; `officialProblem_of_incoherentTail`.

## Reading

[definition] With the energy discharged, the conditional theorem reads: **if every nonzero receiver
is incoherent along a terminal tail, and the eleventh moment is finite there with interior bounds,
then the open solution extends past `T`.** The exponent carries the initial-tail kinetic energy and
the viscosity only. Blow-up therefore requires a coherent comb: receivers whose feeds interfere
constructively.

[established-bounded] Next: the quantitative coherence defect. Replace `IncoherentAt` by
`‖adv_k(o)‖² ≤ (1 + κ) Σ'_p ‖feed_{k,p}(o)‖²` and carry `κ` through the same ladder; then relate
`κ` to the barycentric spread of the feed comb (`cross_eq_pairs_mul_mean_sq_sub_spread`).

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesVelocityMassEnergy` green within the 180 s bound.
- Axiom audits: `velocityMass_le_kineticEnergy`, `periodicKineticEnergy_le_of_le`,
  `moment_two_le_kineticEnergy`, `statementB_of_incoherentTail` each depend on
  `[propext, Classical.choice, Quot.sound]`.
