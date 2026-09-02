# Landau's remainder: the log-derivative of a nonvanishing disc is bounded by eight M over r

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8706 jobs for the owner cone; root module green at 9721)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, building the population side of the explicit formula as Brandon directed: the analytic remainder of Landau's lemma from Mathlib's Borel--Carathéodory. Assistant derivation for the proofs.
**Band:** ANALYTIC LOGARITHM ON A DISC FROM THE PRIMITIVE OF g′/g / Re h ≤ M, h(z₀) = 0 / BOREL–CARATHÉODORY: ‖h‖ ≤ 2M ON THE HALF-RADIUS CIRCLE / CAUCHY: ‖g′/g‖ ≤ 8M/r ON THE QUARTER DISC / 8 = 2 · 2 · 2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Goal and route

[definition] The phase-flow owner returned that RH is the emptiness of the pair population at
`t = 0`, a realizer statement carried by the primes through the explicit formula. The corpus's
explicit-formula port (`HasPrimeArchimedeanResidualIdentity`) is open because it needs the
log-derivative of `ξ` controlled off the zeros. The classical tool is Landau's lemma: on a disc
where `‖f/f(z₀)‖ ≤ e^M`, the log-derivative is the Coulomb flux `Σ 1/(z − ρ)` of the zeros in
the half disc plus a remainder `O(M/r)`. Holonically the lemma is the identification of the
`ξ` log-derivative with the zero-comb flux of the phase-flow ledger. This owner proves the
remainder half, generically, from Mathlib's new Borel--Carathéodory theorem.

## Statement

[proved-derived] `exists_log`: a nonvanishing analytic `g` on `ball z₀ r` is `g z₀ · exp h` for
an analytic `h` with `h z₀ = 0` and `h′ = g′/g`; `h` is the primitive of `g′/g` supplied by
Mathlib's `isExactOn_ball`, and `g · exp(−h)` has zero derivative on the convex ball, hence is
constant.

[proved-derived] `norm_logDeriv_le`: if moreover `‖g z‖ ≤ ‖g z₀‖ e^M` on the ball with
`M > 0`, then `‖g′(z)/g(z)‖ ≤ 8M/r` for `z` in the closed quarter disc. The real part of `h` is
at most `M`, Borel--Carathéodory on the translated ball gives `‖h‖ ≤ 2M‖w‖/(r − ‖w‖)`, which is
`≤ 2M` on every circle of radius `r/4` about a point of the quarter disc, and Cauchy's estimate
returns `‖h′‖ ≤ 2M/(r/4)`. The constant is the product expansion `8 = 2 · 2 · 2`: one factor
from Borel--Carathéodory, two from the two halvings of the radius.

## Holonic reading

[definition] After the zeros of a receiver are extracted, what remains is a nonvanishing unit
whose log-derivative is the gradient of a bounded potential; the bound says the unit's flux is
controlled by the growth budget `M` per unit radius. The zero comb carries the singular flux and
the unit carries only a bounded background. This is the analytic statement that the
log-derivative *is* the comb flux, up to a background the growth bound pays for.

[established-bounded] The extraction half (dividing out the finitely many zeros in the half disc
and bounding the quotient by `e^M` on the smaller disc through the maximum principle) is the
next owner; then the application to `ξ` with the corpus's abscissa growth bound gives Landau's
lemma for `ξ` on every disc, the input the explicit-formula port needs.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/LogDerivativeRemainder.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PhaseFlowLedger`.
