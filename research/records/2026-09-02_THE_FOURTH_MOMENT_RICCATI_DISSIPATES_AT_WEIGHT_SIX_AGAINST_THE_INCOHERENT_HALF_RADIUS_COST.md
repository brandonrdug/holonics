# The fourth-moment Riccati dissipates at weight six against the incoherent half-radius cost

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: `/loop` with the goal `weightedTailEnergy_riccati`, second piece. Assistant derivation for the proofs.
**Band:** RICCATI CHAIN MADE GENERIC / INCOHERENT HALF-RADIUS COST / FOURTH-MOMENT FAMILY RICCATI PROVED / DISSIPATION AT WEIGHT SIX / DRIVE AS WEIGHTED SQUARED COST / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesFourthMomentRiccati.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`complexVectorL1_vorticityNonlinearMode_le_of`, `modalEnergy_riccati_of`,
`modalEnergy_riccati_amgm_of`: the Riccati chain for any bound `B` on the advection coefficient.
`incoherentCost t r = (ℓ¹(û(0)) + √(52·3/(2π)²) · √S₂(r)) · tailJ(r) + velocityTail(r) · totalJ`,
with `S₂(r)` the band's second moment of vorticity energy; `norm_openActualAdvectionMode_le_incoherent`;
`modalEnergy_riccati_incoherent`: the modal Riccati with the incoherent cost at the mode's half
radius. `momentEnergy w F τ = Σ_{k∈F} |k|_∞^w E_k(τ)`; `momentCost t F = Σ_{k∈F} |k|_∞⁴ · incoherentCost(⌊(|k|_∞−1)/2⌋)²`.
`momentEnergy_riccati`: for any finite family of nonzero modes,

```text
M₄' ≤ −ν (2π)² M₆ + (3⁵/ν) · momentCost.
```

## What it says

[interpretation] The controlled moment is the fourth; the dissipation acts on the sixth; the drive
is the fourth-moment sum of squared incoherent costs. Reading the drive in moments of `E_k` is the
swap lemma, the last piece of the goal, which returns the exact exponent of the driving moment.

## What this does not establish

[open] The drive is not yet expressed in moments of `E_k`; nothing bounds it.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesFourthMomentRiccati.lean` (new; registered).
