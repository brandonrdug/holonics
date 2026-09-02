# Every entire function has a zero factorization on every disc, and Landau's lemma holds unconditionally

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8708 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, discharging the factorization hypothesis of Landau's lemma from Mathlib's zero extraction, and sharpening the lemma so the unit need only avoid the half disc. Assistant derivation for the proofs.
**Band:** MEROMORPHIC ORDER NEVER ⊤ FOR A NONZERO ENTIRE FUNCTION / DIVISOR SUPPORT ON THE BALL FINITE VIA THE CLOSED BALL / MATHLIB EXTRACTION f = φ · g CODISCRETELY / CODISCRETE + CONTINUOUS ⇒ POINTWISE / SUPPORT SPLIT: HALF DISC INTO THE POLYNOMIAL, ANNULUS INTO THE UNIT / LANDAU SHARPENED: UNIT NONVANISHING ON THE HALF DISC, ‖f′/f − FLUX‖ ≤ 16 (M + N log 2)/r ON THE r/8 DISC / 16 = 2⁴ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `LandauLemma.lean` is sharpened: the factorization's unit need only be
nonvanishing on the half disc `ball z₀ (r/2)` (zeros of `f` in the outer annulus may stay inside
the unit), the maximum principle is taken on the three-quarter ball as before, and Landau's
remainder is applied on the half disc, so `norm_logDeriv_sub_flux_le` now reads
`‖f′/f(z) − Σ m_ρ/(z − ρ)‖ ≤ 16 (M + N log 2)/r` on the closed `r/8` disc off the zeros;
the constant is `16 = 2⁴` from `8 · 2`.

[proved-derived] `ZeroFactorizationExists.lean`: `meromorphicOrderAt_ne_top` (a nonzero entire
function has finite order everywhere, by the identity theorem on the connected plane);
`eq_of_codiscreteWithin` (two functions continuous at a point of an open set that agree on a
codiscrete subset agree at the point, by uniqueness of limits along the punctured
neighbourhood); `exists_zeroFactorization`: for entire `f` with `f z₀ ≠ 0` and `r > 0` there is
a `ZeroFactorization f z₀ r`. The divisor of `f` on the open ball has finite support because it
is dominated by the divisor on the compact closed ball; Mathlib's `extract_zeros_poles` returns
the unit and the codiscrete factorization; the factorized rational is a finite product over the
support, its integer exponents are the nonnegative analytic orders, and the support splits into
the half disc, which becomes the zero polynomial, and the annulus, whose factors fold into the
unit and are nonvanishing on the half disc.

[proved-derived] Composing the two owners: Landau's lemma now holds for every entire `f` with
`f z₀ ≠ 0` and `‖f‖ ≤ ‖f z₀‖ e^M` on the disc, with no factorization hypothesis.

## Holonic reading

[definition] The receiver's zero comb is now an exact output of Mathlib's extraction rather than
a declared datum: the population, the multiplicities, and the unit are constructed, and the
log-derivative is read as the comb flux plus the unit's bounded background. The population side
of the explicit formula can now be built on top of a constructed comb.

[established-bounded] Next: the application to `ξ` with the corpus's pointwise abscissa growth
bound, giving Landau's lemma for `ξ` on every disc with `M` a product expansion in
`(‖z₀‖ + r + 3) log(‖z₀‖ + r + 3)`; then Jensen's count to remove `N`.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ZeroFactorizationExists.lean` and the
  sharpened `RH/LandauLemma.lean` compile under `lake env lean` and `lake build`; the root
  module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.LandauLemma`.
