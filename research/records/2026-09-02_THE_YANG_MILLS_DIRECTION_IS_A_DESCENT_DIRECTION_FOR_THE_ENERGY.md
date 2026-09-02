# The Yang–Mills direction is a descent direction for the energy

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3724 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the Y1 flow clause with the first variation of the energy. Assistant derivation for the proofs.
**Band:** SYMMETRIC AD-INVARIANT PAIRING / YANG–MILLS ENERGY ON THE BOX / ENERGY ALONG A + εG IS A QUARTIC IN ε WITH INTEGRAL COEFFICIENTS / DERIVATIVE AT 0 IS −2Σ_j∫B(G_j,G_j) / NONPOSITIVE FOR NONNEGATIVE SQUARES / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsDescent.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`SymmetricPairing` (an invariant pairing with `B x y = B y x`); `yangMillsEnergy P A = ½ ∫_box Σ B(F,F)`;
`pairing_expand` (the quartic of a quadratic); `hasDerivAt_yangMillsEnergy_direction`: for a `C³`
one-periodic connection,

```text
d/dε YM(A + ε G) |_{ε=0} = −2 Σ_j ∫_box B(G_j, G_j),
```

exactly, the energy along the line being a quartic polynomial in `ε` whose coefficients are
integrals of continuous fields; `deriv_yangMillsEnergy_direction_nonpos`: with nonnegative
squares the derivative is `≤ 0`.

## Reading

[definition] The Yang--Mills direction is the gradient direction of the energy, with the flow's
dissipation equal to twice the squared direction: the Y1 contract's heat flow clause is exact at
the level of the first variation. No PDE well-posedness is used: the path is linear in `ε`, the
curvature is a polynomial along it, and the energy is a quartic whose derivative is computed
algebraically; only the periodic box law enters analytically.

[established-bounded] Next in the loop: Hodge, then the NS frontier chain, then BSD sign law; on
Y1, the second variation (the Hessian of the energy, the linearized Weitzenböck operator) as the
object the mass-gap receiver reads.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsDescent` green within the 180 s bound.
- Axiom audits: `hasDerivAt_yangMillsEnergy_direction`, `deriv_yangMillsEnergy_direction_nonpos`
  each depend on `[propext, Classical.choice, Quot.sound]`.
