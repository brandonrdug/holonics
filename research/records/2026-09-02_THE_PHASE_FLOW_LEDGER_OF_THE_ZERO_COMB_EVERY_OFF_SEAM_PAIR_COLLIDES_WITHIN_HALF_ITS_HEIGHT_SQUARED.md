# The phase-flow ledger of the zero comb: every off-seam pair collides within half its height squared

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8706 jobs for the owner cone; root module green at 9720)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, attacking RH along the de Bruijn--Newman phase flow as Brandon directed, transporting the Navier--Stokes Fourier ledger onto the zero comb. Assistant derivation for the proofs.
**Band:** ZERO-COMB FLUX 2/(z_j − z_k) / KIRCHHOFF: TOTAL FLUX = 0 / SECOND-MOMENT FLUX = 2N(N−1), CONFIGURATION-INDEPENDENT / PAIR HEIGHT ẏ ≤ −1/y / y² + 2t NONINCREASING / COLLISION WITHIN y₀²/2 (DE BRUIJN Λ ≤ ½ MECHANISM) / RH = EMPTY PAIR POPULATION AT t = 0, A REALIZER STATEMENT / RODGERS–TAO DYNAMICS A NAMED PORT / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Goal and route

[definition] Brandon's directive of 2026-09-02: attack RH, NS, and BSD directly along the
holonic one-shape route rather than by bounded bookkeeping. The route is the atlas entry
`RH.0070` (de Bruijn--Newman phase flow, Rodgers--Tao arXiv:1801.05914): `t` deforms the zero
comb, RH is the undeformed face `t = 0`, the threshold is the discriminant where a conjugate
pair collides with the seam. The August scratchwork read RH as half-turns cancelling to
square-root order and the null cone of a semi-definite form as its radical. The Navier--Stokes
Fourier ledger built earlier this session (pairwise antisymmetric transfer, Kirchhoff
conservation, frontier and moment bounds) is the same shape; this owner transports it onto the
zero comb.

## Statement

[definition] `zeroFlux x j = Σ_k 2/(x_j − x_k)`, the backward-heat velocity of the `j`-th zero
of a real comb (the diagonal term is `2/0 = 0` in Lean's convention, so no erasure is needed).
`heightFlux a y x = −1/y − Σ_k 2y/((a − x_k)² + y²)`, the imaginary part of the flux felt by a
conjugate pair `a ± iy` above the comb: the pair's own term `2/(z − z̄) = −i/y` and the crowd's
terms.

[proved-derived] `sum_zeroFlux`: the total flux vanishes (Kirchhoff on the comb).
`sum_mul_zeroFlux`: `Σ_j 2x_j · flux_j = 2N(N−1)` for every injective comb, so the
second-moment flux is configuration-independent. `hasDerivAt_centre`,
`hasDerivAt_secondMoment`: along any solution the centre is conserved and the second moment
grows at exactly `2N(N−1)`, with constants the product expansions `2 · N · (N − 1)`.

[proved-derived] `heightFlux_le`: for `y > 0`, `heightFlux ≤ −1/y`; every real zero pushes the
pair toward the seam, so the crowd only helps the collision. `sq_add_two_mul_le`: if the pair's
height follows the height flux and stays positive on `[0, T]`, then `y(T)² + 2T ≤ y(0)²`.
`two_mul_le_sq`: hence `2T ≤ y(0)²`, the pair meets the seam within time `y(0)²/2`. This is the
mechanism behind de Bruijn's `Λ ≤ 1/2` (zeros in the unit strip in `H`-coordinates).

[project-postulate] `RodgersTaoZeroDynamics`: that the zeros of `H_t` obey this flux is the
Csordas--Smith--Varga / Rodgers--Tao dynamics, carried as a named port with source, consumed by
no theorem here.

## Holonic reading, and what the attack returned

[definition] On the zero comb the ledger closes with no defect: the second-moment flux is a
constant of the population size alone. That is exactly what the Navier--Stokes comb lacks; its
coherence defect measures the departure of the modal exchange from a configuration-independent
law. So the one-shape thesis reads: the zero comb is perfectly coherent, and RH is not a flux
statement at all. Forward in `t` the flux annihilates every off-seam pair in bounded time, which
is Rodgers--Tao's `t > 0` half and de Bruijn's bound; the `t = 0` face asks whether the pair
population is empty *before* any flow, and no monotone quantity of the flux can see that,
because backward in `t` pairs are created rather than destroyed (the atlas boundary: forward
regularization does not reverse). The emptiness of the pair population is a statement about the
realizer population, the primes through the explicit formula, which is the same missing half
named in the August record on Weil positivity.

[established-bounded] Consequence for the three lines: the shared receiver is the pair
collision locus (the null cone of the pair form), and the shared obstruction is the population
that must be shown empty (RH), coherent (NS), or counted by the analytic order (BSD). The next
deed on this route is the population side, not more flux: the explicit-formula residual
identity that ties the zero flux to the prime flux, `ExplicitFormulaReceiver`'s open port.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PhaseFlowLedger.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.OffLineJensen`.
