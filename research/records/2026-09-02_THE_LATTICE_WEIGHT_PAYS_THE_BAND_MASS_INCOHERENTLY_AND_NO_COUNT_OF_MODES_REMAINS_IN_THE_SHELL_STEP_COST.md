# The lattice weight pays the band mass incoherently, and no count of modes remains in the shell-step cost

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: `/loop` with the goal `weightedTailEnergy_riccati`, first piece. Assistant derivation for the proofs.
**Band:** INCOHERENT BAND MASS PROVED / COUNT REMOVED FROM THE SHELL-STEP COST / BAND PAID BY ITS SECOND MOMENT AND THE ZERO MODE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesIncoherentBandMass.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`bandMass_le_incoherent`: `bandMass(N) ≤ ℓ¹(û(0)) + √52 · √(Σ_{p ∈ cube N, p ≠ 0} |p|_∞⁴ ℓ¹(û(p))²)`,
Cauchy--Schwarz against the lattice weight `Σ |p|_∞⁻⁴ ≤ 52` already proved.
`fourthMoment_tooth_le`: `|p|_∞⁴ ℓ¹(û(p))² ≤ (3/(2π)²) · |p|_∞² · E_p`, through Lagrange on the
divergence-free mode and `|p|_∞² ≤ |p|²`.
`bandMass_le_secondMoment`: `bandMass(N) ≤ ℓ¹(û(0)) + √(52 · 3/(2π)²) · √(Σ_{p ∈ cube N, p ≠ 0} |p|_∞² E_p)`.
`norm_bandFeed_le_secondMoment`: the band feed at a receiver outside the cube of radius `2N` is
at most that quantity times the Jacobian tail mass beyond `N`.

## What it says

[interpretation] The shell-step cost no longer carries the count `(2N+1)³`. The band is paid by
its own second moment of vorticity energy and the zero mode, with the constant
`√(52 · 3/(2π)²) = √(2 · 26 · 3) / (2π)`: the telescoping `2`, the shell face `26 = 24 + 2`, the
coordinate comparison `3`, and the circle constraint. This is the half power of the band comb
made unconditional: Cauchy--Schwarz against a summable weight is the incoherent composition,
exact, with no hypothesis on the barycenter.

## What this does not establish

[open] The fourth-moment Riccati inequality is not yet written; the drive still carries the tail
masses `tailJ(N)`, `velocityTail(N)`, `totalJ` rather than moments of `E_k`.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesIncoherentBandMass.lean` (new; registered).
