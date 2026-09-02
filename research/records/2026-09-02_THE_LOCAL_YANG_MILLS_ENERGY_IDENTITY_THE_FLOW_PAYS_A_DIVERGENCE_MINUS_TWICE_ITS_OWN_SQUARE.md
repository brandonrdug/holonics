# The local Yang–Mills energy identity: the flow pays a divergence minus twice its own square

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3721 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, on the Y1 covariant-lift contract. Assistant derivation for the proofs.
**Band:** AD-INVARIANT PAIRING / DIFFERENTIAL OF A PAIRING / THE COVARIANT DERIVATIVE IS METRIC / Σ_{ij} B((D_A G)_ij, F_ij) = 2Σ_{ij}∂_iB(G_j,F_ij) − 2Σ_j B(G_j,G_j) / POINTWISE, NO INTEGRATION / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsEnergy.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`InvariantPairing 𝔤` (a continuous bilinear `B` with `B([a,x],y) + B(x,[a,y]) = 0`);
`differential_pairing` (`∂_i B(X,Y) = B(∂_iX, Y) + B(X, ∂_iY)`); `differential_pairing_eq_covariant`
(the covariant derivative is metric: `∂_i B(X,Y) = B(D_iX, Y) + B(X, D_iY)`);
`sum_pairing_covariantVariation_yangMillsDirection`: for a `C³` connection,

```text
Σ_{ij} B((D_A G)_ij, F_ij) = 2 Σ_{ij} ∂_i B(G_j, F_ij) − 2 Σ_j B(G_j, G_j).
```

## Reading

[definition] With `curvature_add_smul` this is the first variation of the Yang--Mills energy
density along the flow: a divergence (a current through the boundary of any cell) minus twice the
squared flow direction. Integrated over a base without boundary the divergence vanishes and the
energy decreases exactly by the squared flow; this is the Yang--Mills twin of the Navier--Stokes
energy--dissipation identity, with the flow direction in the role of the strain and no
nonlinear work term at all: the gauge field's self-interaction is invisible to the energy, exactly
as the advection is invisible to the fluid's.

[established-bounded] Next on Y1: the integrated identity on the torus (the divergence integrates
to zero by periodicity, reusing the Navier--Stokes cube divergence law), and the pairing with the
NS vorticity Riccati under `F ↔ ω`.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsEnergy` green within the 180 s bound.
- Axiom audits: `differential_pairing_eq_covariant`, `sum_pairing_covariantVariation_yangMillsDirection`
  each depend on `[propext, Classical.choice, Quot.sound]`.
