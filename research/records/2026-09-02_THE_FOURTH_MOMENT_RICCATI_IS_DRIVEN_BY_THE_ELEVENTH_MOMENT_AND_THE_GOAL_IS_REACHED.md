# The fourth-moment Riccati is driven by the eleventh moment, and the goal is reached

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: `/loop` with the goal `weightedTailEnergy_riccati`, final piece. Assistant derivation for the proofs.
**Band:** GOAL REACHED / GENERIC SWAP WITH WEIGHT / VELOCITY TAIL PAID BY THE NINTH MOMENT / TOTAL JACOBIAN MASS PAID BY THE FOURTH / BAND FACTOR PAID BY THE SECOND / DRIVE READ ENTIRELY IN MOMENTS / LADDER GAP FIVE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesMomentGap.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`). With `W_w = Σ'_q |q|_∞^w E_q` the `w`-th
moment of the modal vorticity energy and the eleventh moment summable:

- `sum_pow_four_tailMoment_le`: the generic swap, weight `4` on the receiver against the `w`-th
  moment tail beyond the half radius returns `26 · 2⁷ · W_{w+7}`.
- `sum_l1_le`, `velocityTailMass_sq_le`: the velocity tail beyond radius `r`, squared, is at most
  `52 · (3/(2π)²)` times the second-moment tail beyond `r`.
- `jacobianMode_zero`, `totalJ_sq_le`: the total Jacobian mass, squared, is at most `52 · W₄`.
- `bandSecondMoment_le`, `incoherentCost_le`: the band factor is `ℓ¹(û(0)) + √(52·3/(2π)²) √W₂`.
- `momentCost_le`: for any finite family of nonzero modes,

```text
momentCost ≤ 2 (ℓ¹(û(0)) + √(52·3/(2π)²) √W₂)² · 52·26·2⁷ · W₁₁
             + 2 · 52 W₄ · 52·(3/(2π)²) · 26·2⁷ · W₉.
```

- `momentEnergy_riccati_moments`: the fourth-moment Riccati inequality with that drive,

```text
M₄' ≤ −ν (2π)² M₆ + (3⁵/ν) · [ the bound above ].
```

## The exact gap

[interpretation] The controlled moment is four. The dissipation acts on the sixth. The drive is
the eleventh moment, times a band factor paid by the second, plus the product of the fourth and
the ninth. The ladder gap between the dissipating moment and the driving moment is
`11 − 6 = 5`. Every constant is a product expansion: `52 = 2 · 26`, `26 = 24 + 2` the shell face,
`2⁷` the doubling of the half radius, `3⁵` the five coordinate comparisons, `3/(2π)²` the
`ℓ¹`-to-energy comparison over the circle constraint. No analytic vocabulary remains. The
coherence question of the band comb is now exactly whether the half power can be taken again
on the swap, which would move the eleventh moment toward the sixth.

## What this does not establish

[open] Nothing bounds any moment in time. The gap of five is not closed. `TailRelevanceControl`
and `WeightedTailEnergyControl` remain uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesMomentGap.lean` (new; registered).
