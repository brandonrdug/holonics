# The highest pair descends: de Bruijn's bound at the polynomial face

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9750 jobs)
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow: for a real polynomial the partner z̄ is in the comb and every other root lies no higher, so the highest pair's imaginary part obeys ẏ ≤ −1/y along the flow and its height squared loses at least 2t; a pair of height y₀ is dead by t = y₀²/2. Assistant derivation for the proofs.
**Band:** Im 1/(z−w) ≤ 0 FOR Im w ≤ Im z / Im 1/(z−z̄) = −1/(2 Im z) / Im(FLUX) ≤ −1/Im z AT THE HIGHEST PAIR / ROOTS OF REAL POLYNOMIALS ARE CONJUGATION-CLOSED AND THE FLOW IS REAL / Im z(T)² + 2T ≤ Im z(0)² / T < Im z(0)²/2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `im_one_div_sub_nonpos`: `Im 1/(z − w) ≤ 0` when `Im w ≤ Im z`.
`im_one_div_sub_conj`: `Im 1/(z − z̄) = −1/(2 Im z)`. `im_flux_le` (**the highest pair
descends**): if `z̄` is a root and no root lies above `z` (`Im z > 0`), the flux
`2 Σ_{w ≠ z} 1/(z − w)` has imaginary part at most `−1/Im z`.

[proved-derived] `eval_map_conj`, `conj_mem_roots`: the roots of a real polynomial are closed
under conjugation. `heatR`, `heat_map`, `conj_mem_roots_heat`: the backward heat flow of a real
polynomial is real, so its roots stay conjugation-closed.

[proved-derived] `sq_add_two_mul_le'`: a positive `C¹` function with `y′ ≤ −1/y` on `[0, T]`
satisfies `y(T)² + 2T ≤ y(0)²`. `highest_pair_descent`: along a `C¹` curve of simple zeros of
`heat t p` (`p` real) that stays highest among the roots with positive height,
`Im z(T)² + 2T ≤ Im z(0)²`. `highest_pair_dead` (**de Bruijn's bound at the polynomial face**):
such a curve cannot persist to `T ≥ Im z(0)²/2`.

## Constants

[definition] `2 = 1 + 1` in `−1/(2 Im z)`: `z − z̄ = 2i Im z`; doubled by the flux's `2`, it
gives the descent speed `1/Im z` and the `2T` in the height-squared law. `½` in `y₀²/2` is the
integral of that law. No other constant.

## Holonic reading

[definition] Under the flow the pair population can only die: the highest pair descends at
speed at least `1/y`, its partner pulling it down and the whole comb below adding to the pull.
This is the mechanism by which the de Bruijn–Newman constant is finite, now a theorem of the
flow for every real polynomial. Nothing here creates a pair; creation is the backward direction.

[established-bounded] The `t = 0` face remains what it was: the flow says nothing about
whether the pair population of `ξ` itself is empty; it says that if it is not, the pairs die
by `t = 1/8` in these units (heights at most `½`), and Rodgers–Tao say they cannot all be dead
before `t = 0`. The Riemann hypothesis is the statement that the death is already complete at
`t = 0`. What the flow offers toward that is the *rate* at each height, and the record's
reading is that the rate is where the arithmetic (the explicit formula's prime side) must enter.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PairDescent.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.HeatFlowOfPolynomials`.
- Axiom audit for `highest_pair_dead`, `highest_pair_descent`, `im_flux_le`:
  `[propext, Classical.choice, Quot.sound]`.
