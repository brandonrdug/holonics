# The global Yang–Mills energy identity on the torus: the energy decreases by twice the squared flow

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audit below); `measured` (`lake` job count below: 3723 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, integrating the local Yang--Mills identity with the periodic box law. Assistant derivation for the proofs.
**Band:** PERIODICITY PROPAGATES THROUGH ∂, [·,·], F, D, G / DIVERGENCE FIELD V_i = Σ_j B(G_j, F_ij) IS C¹ PERIODIC / ∫_box Σ_{ij} B((D_A G)_ij, F_ij) = −2 Σ_j ∫_box B(G_j, G_j) / FIRST GLOBAL YANG–MILLS IDENTITY IN THE LINE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsGlobalEnergy.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`differential_periodic`, `bracket_periodic`, `curvature_periodic`, `covariantDerivative_periodic`,
`yangMillsDirection_periodic`; `integral_sum_pairing_covariantVariation_yangMillsDirection`: for a
`C³` one-periodic connection on `Base (n+1)` and an ad-invariant pairing,

```text
∫_box Σ_{ij} B((D_A G)_ij, F_ij) = −2 Σ_j ∫_box B(G_j, G_j).
```

## Reading

[definition] With `curvature_add_smul`, the left side is the first variation of the Yang--Mills
energy `½ ∫ Σ B(F, F)` along the flow direction `G`, so the energy decreases exactly by twice the
squared flow. The divergence current through the box faces cancels by periodicity; nothing else
enters. This is the gauge twin of the fluid's energy--dissipation identity on the torus, and the
Y1 contract's flow clause is now exact: connection, curvature, covariant derivative, Bianchi,
gauge covariance, first variation, Ricci, Weitzenböck, and the energy law along the flow.

[established-bounded] Next: the Yang--Mills heat flow as an actual time-dependent connection
(`∂_t A = −G`) with the energy monotone along it, and the mass-gap receiver's spectral reading of
the linearized Weitzenböck operator; then Hodge.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsGlobalEnergy` green within the 180 s bound.
- Axiom audit: `integral_sum_pairing_covariantVariation_yangMillsDirection` depends on
  `[propext, Classical.choice, Quot.sound]`.
