# The band feed is a comb, and the half power is the sign of the grips between teeth

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below); `source-audit` (arXiv 1812.05346v1 fetched and read)
**Provenance:** Brandon, 2026-09-02: *"Hairy Ball Theorem? Chains of receivers/interactions are like the comb itself. Fourier/Dirac comb, literally … This is for cross-entropy too. Endpoints are like pins in hair, singularities. Spider-webs and vibrations absorbed by setae …"* Assistant derivation for the proofs.
**Band:** COMB EXPANSION PROVED / BAND CROSS TERM NAMED / INCOHERENT HALF-POWER BOUND CONDITIONAL ON NONPOSITIVE CROSS TERM / COHERENT COUNT BOUND / DIRAC BRUSH DICHOTOMY READ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## The source

[established-bounded; source-audit] Viola, *Dirac brushes (or, the fractional Fourier transform
of Dirac combs)*, arXiv 1812.05346v1. The comb is `⊞_r = √r Σ_k δ(x − rk)`; Poisson summation is
`ℱ⊞_r = i^{−1/2} ⊞_{1/r}`. Theorem 1.2: the fractional Fourier transform `ℱ^α ⊞_r`, a rotation of the
comb in phase space by `πα/2`, has discrete support if and only if `r cos(πα/2)` and
`(1/r) sin(πα/2)` are linearly dependent over `ℤ`; otherwise its support is all of `ℝ`. Theorem
1.4: the constant is an eighth root of unity. The discrete case is a comb again; the dense case
is the brush.

## Return

[proved-derived; formal-checked] `NavierStokesBandCoherence.lean` (registered; `lake build`
`4064` jobs; axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`).

`norm_sum_sq_eq_diagonal_add_cross`: for any finite family of complex numbers,
`‖Σ_p z_p‖² = Σ_p ‖z_p‖² + Σ_p Σ_{q ≠ p} ⟪z_p, z_q⟫_ℝ`. The band feed at a tail mode is such a
family, one term per tooth of the frequency comb inside the cube. `bandDiagonal` is the sum of
the squared teeth; `bandCrossTerm` is the sum over ordered pairs of distinct teeth of their grip;
`norm_bandFeed_sq_eq` is the expansion on the actual feed.

`norm_feedTerm_le_energy`: each tooth is at most `3√(2E(0)) · tailJ(N)`.
`bandDiagonal_le`: the diagonal is at most `(2N+1)³` times the squared tooth bound.

`norm_bandFeed_le_of_crossTerm_nonpos`: if the cross term is nonpositive,
`‖bandFeed‖ ≤ √((2N+1)³) · 3√(2E(0)) · tailJ(N)`. `norm_bandFeed_le_coherent`: unconditionally,
`‖bandFeed‖ ≤ (2N+1)³ · 3√(2E(0)) · tailJ(N)`.

## What it says

[interpretation] The half power between the coherent count and its square root is exactly the
sign of the grips between distinct teeth. The grip between two teeth is the real part of their
product, the cosine of the relative phase their arcs have swept; the areal velocity of the
preceding owner is what changes that phase. Viola's dichotomy is the same statement on the line:
teeth compose coherently under a rational rotation and spread into a brush under an irrational
one. The hairy-ball reading: the frequency comb lives on the torus, whose tangent bundle is
trivial, so no pin is forced by topology; pins are the zeros of the vorticity, where the
direction field is undefined and Sol's direction-derivative route divides by the modulus. On a
closed level surface of the modulus homeomorphic to a sphere, the tangential part of the direction
field must vanish somewhere. A chain of receivers is a comb; the cross-entropy of a receiver's
test function against the tail is the cross term read against that receiver's teeth.

## What this does not establish

[open] Nothing decides the sign of the actual cross term. No hairy-ball theorem is formalized;
Mathlib carries none. No cross-entropy owner exists. `TailRelevanceControl` remains uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesBandCoherence.lean` (new; registered). It
imports the shell-step cost owner.
