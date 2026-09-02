# The Gronwall constant is five coordinate comparisons, and dissipation draws no area on the mode arc

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below)
**Provenance:** Brandon, 2026-09-01: *"3⁵/ν = 243/ν, so it's like a rotating pentagon's modes in a way … Surface areas and volumes drawn by the modes over orders of time, parametric arcs drawn, cross-entropies; that's probably what you want moving forward? Just more degrees of calculus and holonics."* Assistant derivation for the proofs.
**Band:** CONSTANTS AS PRODUCT EXPANSIONS / LINEAGE OF 3⁵ RECORDED / AREAL VELOCITY DEFINED / DISSIPATION DRAWS NO AREA / SLIP PAID BY THE SAME COST / NO SUM OVER THE TAIL / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## The lineage of `3⁵`

[proved-derived; formal-checked] The Gronwall constant `243/ν` is `3⁵/ν` and every factor is one
coordinate comparison on `Fin 3`. The curl symbol bound carries one (`ℓ¹(curl_k v) ≤ 3√λ_k ℓ¹(v)`),
summing the three output components of the advection coefficient carries one
(`ℓ¹(adv) ≤ 3 · feedBound`), so the source bound is `3² √λ_k B_N`. The derivative of the square
supplies `2`, so the cross term is `2 · 3² · ℓ¹(ω̂) √λ_k · B_N`. The arithmetic-geometric step with
weight `ν/3`, the `3` being the `ℓ¹`-to-energy comparison `ℓ¹(ω̂)² ≤ 3E`, returns
`(2 · 3²)² · 3 / (2² ν) = 3⁵/ν`; the two `2`s cancel. `NavierStokesModalRiccati.lean` and
`NavierStokesModalGronwall.lean` now state every constant as this product expansion
(`3 ^ 2`, `2 * 3 ^ 2`, `3 ^ 5`, `3 ^ 3` in the square completing the step); no integer face remains
in a statement. `lake build`: `4064` and `4065` jobs, axioms `[propext, Classical.choice, Quot.sound]`.

## The first degree of arc calculus

[proved-derived; formal-checked] `NavierStokesModalArc.lean` (registered; `4066` jobs; same axioms).
Each mode `ω̂_k(τ) ∈ ℂ³` draws a parametric arc. `gripVelocity w d = Σ_c Re(conj w_c · d_c)` and
`arealVelocity w d = Σ_c Im(conj w_c · d_c)` are the two faces of one contact, the aim and the
cross of `TABLET_THE_TURN`. `arealVelocity_real_smul`: a real multiple of the mode draws no area.
`arealVelocity_eq_nonlinear`: along Sol's per-mode equation the areal velocity of the arc equals the
slip of the nonlinear source alone; the Stokes term shrinks the arc and does not turn it.
`abs_arealVelocity_le`: the slip is paid by the same shell-step cost as the grip,
`|areal| ≤ ℓ¹(ω̂_k) · 3² √λ_k · B_N`.

## What it says

[interpretation] The energy receiver reads the grip and is blind to the slip. Whether the band
composes coherently or incoherently at a tail mode is a statement about the slips of the
contributing triads, that is about the areas their arcs sweep over an interval, not about the
grips. The half power between the count `(2N+1)³` and its square root is therefore a swept-area
statement. Surface areas and volumes over orders of time are the next degrees: the integrated
area of a mode arc over `[s, τ]`, the second time difference through the existing
`HigherDifferenceTransport` owner, and the shell population's volume as a sum of modal energies.

## What this does not establish

[open] No area is integrated; no second-order time difference is taken; no sum over the tail;
`TailRelevanceControl` remains uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesModalArc.lean` (new; registered);
`NavierStokesModalRiccati.lean` and `NavierStokesModalGronwall.lean` (constants refactored).
