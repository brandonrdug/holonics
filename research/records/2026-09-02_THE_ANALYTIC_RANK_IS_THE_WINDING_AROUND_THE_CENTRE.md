# The analytic rank is the winding of L′/L around the centre

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone across the RH and BSD trees; root module green, 9739 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02 (RH, Navier–Stokes, and BSD as one shape), reading the analytic rank of a posed L-datum through the same rectangle receiver that returns the zero comb of ξ. Assistant derivation for the proof.
**Band:** analyticRank = analyticOrderAt L 1 / RECTANGLE CONTAINING 1 WITH NO OTHER ZERO ON ITS CLOSURE / FACTORIZATION ON A HALF DISC ABOUT ANY NONVANISHING POINT / ∮ L′/L = 2πi·analyticRank / SAME RECEIVER AS THE ξ ZERO COMB / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `eq_zero_of_mem_zeros`: the zeros of a factorization of an entire function are
its zeros. `closedRect_subset_ball_of_radius`: every closed rectangle lies in the half disc of
radius `2(‖z‖ + ‖w‖) + ‖s₀‖ + 1` about any point `s₀`.

[proved-derived] `rectIntegral_logDeriv_eq` (**the analytic rank is the winding**): for an
`LDatum W` with `analyticRank W = m` and a rectangle with `1` in its interior on whose closure
`L` vanishes only at `1`, `∮ L′/L = 2πi · m`. The factorization of `L` on a half disc about a
nonvanishing point covers the rectangle; no zero lies on the boundary; the rectangle argument
principle with the constant weight returns the multiplicities inside; only the centre lies
inside, and its multiplicity is the analytic order (or the centre is not a zero and the rank is
zero).

## Constants

[definition] `2πi` inherited from the rectangle residue. The half-disc radius
`2(‖z‖ + ‖w‖) + ‖s₀‖ + 1` is `|Re| + |Im|` of the farthest corner plus the base point's norm plus
one.

## Holonic reading

[definition] RH-for-ℚ and BSD are the same shape here: the receiver that returns the zero comb
of `ξ` (the rectangle argument principle with multiplicities as analytic orders) returns the
analytic rank of an elliptic curve's L-function as the winding of `L′/L` around the centre.
The population on the zero side of BSD is one point counted with multiplicity, and the
conjecture asks that this count be the rank of the realizer population, the Mordell–Weil group.
The corpus's parity law already ties the sign to the parity of this count.

[established-bounded] The hypothesis that `L` has no other zero on the closure of the rectangle
is the local isolation of the centre, true for a small enough rectangle by the identity
theorem when `L ≠ 0`; returning that smallness explicitly is a bounded next step.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/BirchSwinnertonDyerWinding.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.BirchSwinnertonDyerFiniteRank`.
- Axiom audit for `rectIntegral_logDeriv_eq`: `[propext, Classical.choice, Quot.sound]`.
