# The Young source is paid by the sixth moment times the second moment and the zero mode

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4082 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** SOURCE PAID BY K(t)·W₆ / CLOSURE COEFFICIENT IN W₂ AND THE ZERO MODE / ARITHMETIC-GEOMETRIC ABSORPTION / CLOSURE FORM OF THE FOURTH-MOMENT RICCATI / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesYoungClosure.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`closureCoefficient K(t) = 3³ (2π)² · 3 · 2⁵ · [ (3/(2π)²) · 52 · W₂ + (ℓ¹(û(0)) + √(52·3/(2π)²) √W₂)² ]`,
nonnegative. `sourceBound_le`: `sourceBound ≤ K(t) · W₆`, by the interpolation `W₄² ≤ W₂ W₆`
(`moment_four_sq_le`) and the velocity mass in moments (`tsum_l1Pop_le`).
`two_mul_sqrt_mul_sqrt_le`: `2 √x √y ≤ x + y`.
`momentEnergy_riccati_closure`: for every finite family `F` of nonzero modes, with the eleventh
moment summable,

```text
M₄(F)' ≤ −2 ν (2π)² M₆(F) + ν (2π)² W₆ + (3 K(t) / (ν (2π)²)) · M₄(F).
```

## Reading

[definition] The drive of the fourth-moment Riccati is paid entirely at weight six, with a
coefficient that carries only the second moment `W₂` (the enstrophy-like weight) and the zero
mode `ℓ¹(û(0))`. The dissipation `−2ν(2π)² M₆(F)` on the family stands against the drive
`ν(2π)² W₆` on the whole lattice: as the family exhausts the lattice, the balance is
`−ν(2π)² W₆ + (3K/(ν(2π)²)) W₄`. The gap that was five weights at the coherent swap is now zero
weights, and the drive is a linear return on `W₄` itself with coefficient `3K(t)/(ν(2π)²)`.

[established-bounded] The closure statement that remains is the passage from the finite family
to the whole tail (monotone limit of `M₄(F)` and `M₆(F)` with `F ↑ lattice`), then the scalar
weighted maximum principle (`le_max_of_hasDerivAt_le`) under a bound on `W₂` along a terminal
tail of `(0,T)`. That is the sole remaining premise between this owner and
`WeightedTailEnergyControl`, hence `StatementB`.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesYoungClosure` green within the 180 s bound.
- Axiom audits: `sourceBound_le`, `momentEnergy_riccati_closure` each depend on
  `[propext, Classical.choice, Quot.sound]`.
