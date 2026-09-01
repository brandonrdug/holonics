# A tail mode is fed only in proportion to the tail, and the band coefficient is a face count times the initial energy

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-01: *"Yeah, go for it. Stop waiting for my permission on things that are obviously progress."* Assistant derivation for the proofs.
**Band:** FEED TERMS DEFINED / ADVECTION COEFFICIENT IS THE TSUM OF FEED TERMS / BAND-TAIL SPLIT BY REACH / BAND FEED PAID BY TAIL / TAIL FEED PAID BY TAIL / BAND MASS IS COUNT TIMES ENERGY / NO DIFFERENTIAL INEQUALITY CLOSED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Present question

[definition] The reach owner proved that the tail beyond twice the band radius is fed only through
the tail, as a statement about which triads exist. The shell-step cost asks how much a tail mode
can be fed, and by what. This record turns the reach statement into a bound on the actual
advection coefficient of the actual solution slice.

## Return

[proved-derived; formal-checked] `NavierStokesShellStepCost.lean` (registered; `lake build`
`4063` jobs; axioms `[propext, Classical.choice, Quot.sound]` on every theorem; no `sorry`).

`feedTerm k p output = ∑_c û_c(p) · J_{output,c}(k − p)` pairs the velocity coefficient at the
advecting frequency `p` with the Jacobian coefficient at the transported frequency `k − p`.
`openActualAdvectionMode_eq_tsum_feedTerm`: the actual advection coefficient at `k` is
`∑'_p feedTerm k p`, through Sol's `openActualAdvectionMode_eq_h3AdvectiveConvolution` and the
identification of the native `H³` slice state with the solution's Fourier modes
(`sliceState_coeff`).

`openActualAdvectionMode_eq_bandFeed_add_tailFeed`: the coefficient splits exactly into the band
feed (advecting `p` inside the cube of radius `N`) and the tail feed (advecting `p` outside).

`norm_bandFeed_le`: for a receiver `k` outside the cube of radius `2N`,
`‖bandFeed‖ ≤ bandMass(N) · tailJ(N)`, where `tailJ(N)` is Sol's Jacobian coefficient tail mass
beyond the cube. The reach theorem supplies that every transported frequency `k − p` lies outside
the cube of radius `N`.

`norm_tailFeed_le`: `‖tailFeed‖ ≤ velocityTail(N) · totalJ`, the velocity coefficient tail mass
times the complete Jacobian coefficient mass.

`bandMass_le_count_mul_energy`: `bandMass(N) ≤ (2N + 1)³ · 3 · √(2 · E(0))`, the cube's mode count
times the half-density of the initial energy, through the per-coefficient `ℓ¹`-to-`L²` receiver
and the energy inequality.

`norm_openActualAdvectionMode_le`: assembled,

```text
‖advection^(k)‖ ≤ (2N+1)³ · 3·√(2·E(0)) · tailJ(N) + velocityTail(N) · totalJ,   k ∉ cube 2N.
```

## What it says

[interpretation] A tail mode cannot be fed except in proportion to the tail. The linear
coefficient is an integer face count times the half-density of the initial energy, and that count
is the coherent composition of the band: every band mode is allowed to contribute with aligned
phase. Replacing the count `(2N+1)³` by its square root is the incoherent composition the
traversible-chain trichotomy names, and it is the half-power step between the energy-paid and the
enstrophy-paid coefficient. The per-mode vorticity equation in diagonal Stokes form
(`openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes`) has this coefficient as its nonlinear
source up to the curl symbol; the differential inequality for the tail is the Riccati owner this
one prepares and does not close.

## What this does not establish

[open] No sum over the tail is differentiated; no Gronwall or Riccati inequality is closed; the
tail masses are not shown integrable in time. `TailRelevanceControl` remains uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesShellStepCost.lean` (new; registered). It
imports the reach and relevance owners and Sol's advection convolution bridge, carrier
integration, open Fourier mild identity, and vorticity shell dissipation bridge.
