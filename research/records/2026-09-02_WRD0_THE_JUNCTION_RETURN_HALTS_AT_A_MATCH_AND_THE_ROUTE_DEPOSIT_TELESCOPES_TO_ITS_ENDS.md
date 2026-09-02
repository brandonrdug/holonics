# WRD0: the junction return halts at a match, and the route deposit telescopes to its ends

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audit below; focused build 3,172 jobs, campaign umbrella `HolonicQuantumTransport` 3,772 jobs on 2026-09-02; `lake build ElementaryHolonics.Computation.HolonicWorldReturnDeposit 2>&1 | grep -c sorry` returned 0 on 2026-09-02)
**Provenance:** Assistant (Claude), under Brandon's direct instruction of 2026-09-02 to deposit and complete the WRD campaign. Assistant derivation for the proofs.
**Band:** T + GAMMA² = 1 / GAMMA = 0 IFF MATCHED / SERVICE ROUNDS = CEIL(1/T) / ROUNDS ≥ 2 WHEN UNMATCHED / A ROUTE DEPOSIT SUMS TO ZERO AND VANISHES OFF THE ROUTE / INTERIOR CANCELS, ENDS CARRY / A THREE-SITE ROUTE CULTIVATION RESTS OUTSIDE ITS CONE / EQUAL KERNEL FACES, DIFFERENT REFLECTIONS

---

## Statement

[proved-derived] `soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicWorldReturnDeposit.lean`
(namespace `Soma.Holonics.Computation.HolonicWorldReturnDeposit`, imported by
`HolonicMachineLearning.lean`) owns:

- `JunctionReturn` (positive incident and transmitted counts) with `reflection`, `transmission`,
  and `serviceRounds`; `transmission_add_reflection_sq` (`T + Γ² = 1`), `reflection_eq_zero_iff`
  (`Γ = 0 ↔ R = M`), `transmission_pos`, `transmission_le_one`, `transmission_of_matched`,
  `serviceRounds_eq_ceil_inv_transmission`, `serviceRounds_of_matched` (`= 1`),
  `one_lt_inv_transmission_of_unmatched`, and `serviceRounds_ge_two_of_unmatched`;
- `RouteStep` with a unit hand and `deposit`; `deposit_outside`, `sum_deposit` (`= 0`);
  `routeDeposit` over a list of steps, `routeDeposit_cons`, `sum_routeDeposit` (`= 0`),
  `routeDeposit_outside`; `twoStep_interior_cancels` and `twoStep_boundary_carries` (the
  telescoping law: a chained route deposits only at its two ends);
- `Control.threeSiteRouteCultivation`, a `LocalCausalConeCultivation` on three sites whose
  cone is the route; `threeSiteRouteCultivation_outside_rests`,
  `_boundary_gives_and_receives`, `_changedProbe_meets_cone`;
- `KernelFace`, `ReturnFaces`, `matchedJunction = ⟨3, 3⟩`, `partialJunction = ⟨3, 1⟩`,
  `equalKernelFace_differentReflection`, `matchedJunction_halts`, `partialJunction_reenters`.

[definition] The junction fixes no unit: `R` and `M` are counts of whatever crosses the boundary.
WRD3 fixes the unit as the emission; the Lean owner is unchanged by that choice.

## Axiom audit (printed by the build on 2026-09-02)

```
'JunctionReturn.transmission_add_reflection_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'JunctionReturn.reflection_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'JunctionReturn.serviceRounds_of_matched' depends on axioms: [propext, Classical.choice, Quot.sound]
'JunctionReturn.serviceRounds_ge_two_of_unmatched' depends on axioms: [propext, Classical.choice, Quot.sound]
'sum_routeDeposit' depends on axioms: [propext, Classical.choice, Quot.sound]
'routeDeposit_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
'twoStep_interior_cancels' depends on axioms: [propext, Classical.choice, Quot.sound]
'twoStep_boundary_carries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Control.threeSiteRouteCultivation_outside_rests' depends on axioms: [propext, Classical.choice, Quot.sound]
'Control.threeSiteRouteCultivation_changedProbe_meets_cone' depends on axioms: [propext, Classical.choice, Quot.sound]
'equalKernelFace_differentReflection' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` and no new axiom appear.
