# Landau's lemma: the log-derivative is the zero-comb flux plus a bounded background

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8707 jobs for the owner cone; root module green at 9722)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, building the population side of the explicit formula as Brandon directed: Landau's lemma given a zero factorization, the extraction half by the maximum principle. Assistant derivation for the proofs.
**Band:** ZERO FACTORIZATION f = P · unit ON THE DISC / ‖P‖ ≥ (r/4)^N ON THE 3r/4 CIRCLE, ‖P(z₀)‖ ≤ (r/2)^N / MAXIMUM PRINCIPLE: ‖unit‖ ≤ ‖unit(z₀)‖ e^{M + N log 2} / LOG-DERIVATIVE = Σ m_ρ/(z − ρ) + unit′/unit / ‖f′/f − FLUX‖ ≤ 32 (M + N log 2)/(3r) ON THE 3r/16 DISC / 32 = 2⁵, 3 = 3 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `ZeroFactorization f z₀ r`: a finite set of zeros in the half disc with positive
multiplicities and an analytic nonvanishing `unit` on the disc such that
`f = (∏ (· − ρ)^{m_ρ}) · unit` on the disc; `count = N = Σ m_ρ`; `poly` the zero polynomial.

[proved-derived] `norm_poly_ge`: on the circle of radius `3r/4` every zero factor has modulus at
least `r/4`, so `‖P‖ ≥ (r/4)^N`; `norm_poly_centre_le`: `‖P(z₀)‖ ≤ (r/2)^N`. `norm_unit_le`: if
`f(z₀) ≠ 0` and `‖f‖ ≤ ‖f(z₀)‖ e^M` on the disc, the maximum principle on the three-quarter
ball gives `‖unit‖ ≤ ‖unit(z₀)‖ e^{M + N log 2}` there; the factor `2^N = (r/2)^N/(r/4)^N` is
one halving per zero.

[proved-derived] `norm_logDeriv_sub_flux_le`: for `z` in the closed `3r/16` disc off the zeros,
`‖f′/f(z) − Σ_ρ m_ρ/(z − ρ)‖ ≤ 32 (M + N log 2)/(3r)`. The log-derivative of the product splits
into the flux of each zero factor and the unit's log-derivative, and the previous owner's
remainder bound applied to the unit on the three-quarter disc with budget `M + N log 2` returns
`8 · (M + N log 2)/(3r/4)`.

## Holonic reading

[definition] This is the identification the phase-flow owner asked for: the log-derivative of
a receiver is the Coulomb flux of its zero comb, the same pairwise law `1/(z − ρ)` as the
de Bruijn--Newman zero dynamics, plus a background bounded by the growth budget per unit radius.
The comb carries all the singular current; the unit is a bounded reservoir. For `ξ` this will
turn the explicit-formula contour into a sum over the zero comb with a controlled remainder,
which is the analytic input the population side (the primes) needs.

[established-bounded] The factorization is a hypothesis here. Its existence for an entire
function not vanishing at the centre follows from Mathlib's zero extraction
(`MeromorphicOn.extract_zeros_poles`) once the codiscrete equality is upgraded to a pointwise one
by continuity; that passage, then the application to `ξ` with the abscissa growth bound, are the
next two owners. Jensen's bound `N ≤ M/log 2` (`AnalyticOnNhd.sum_divisor_le`) then removes `N`
from the constant.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/LandauLemma.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.LogDerivativeRemainder`.
