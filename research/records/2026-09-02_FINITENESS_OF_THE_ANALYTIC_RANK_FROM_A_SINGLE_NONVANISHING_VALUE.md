# Finiteness of the analytic rank from a single nonvanishing value

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3490 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, discharging the order hypothesis of the sign law by the identity theorem on the BSD line. Assistant derivation for the proofs.
**Band:** RANK = ⊤ ⇔ L ≡ 0 / RANK < ⊤ ⇔ ∃ s, L(s) ≠ 0 / ∃ m, RANK = m FROM ONE NONVANISHING VALUE / SIGN = (−1)^m WITHOUT AN ORDER HYPOTHESIS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `analyticRank_eq_top_iff`: the analytic rank is infinite exactly when the
continued `L` vanishes identically, by Mathlib's identity theorem for functions analytic on the
connected plane. `analyticRank_ne_top_iff`: the rank is finite exactly when `L` has a
nonvanishing value.

[proved-derived] `exists_analyticRank_eq`: one nonvanishing value returns a natural number `m`
with `analyticRank W = m`. `exists_analyticRank_eq_and_sign`: the same value returns `m` with
`sign = (−1)^m`, the sign law with no hypothesis on the order.

## Holonic reading

[definition] The analytic rank is the order of the centre's defect. An entire receiver whose
defect is infinite at one point has no signal anywhere; a single nonzero reading anywhere
therefore certifies a finite order at the centre. The sign law's hypothesis is thus discharged
by any nonvanishing value of `L`, which the Dirichlet-series normalisation `coeff 1 = 1`
supplies on the half-plane of agreement once the series' tail is controlled.

[established-bounded] The nonvanishing value is a hypothesis: the datum carries no coefficient
growth bound, so the series' convergence and its limit at large real part are not derivable
inside the pose. That bound is the next seam of this line.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/BirchSwinnertonDyerFiniteRank.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.BirchSwinnertonDyerAlgebraicParity`.

Next in the loop: NS coherence half; RH certification of `ξ(½) ≠ 0`; Y1 orbit-space descent.
