# Jensen counts the comb: Landau's lemma for ξ carries no free count

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8721 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, tying the constructed comb's multiplicity to the divisor mass and bounding it by Mathlib's Jensen inequality. Assistant derivation for the proofs.
**Band:** COUNT OF THE CONSTRUCTED COMB = DIVISOR MASS OF THE CLOSED HALF DISC / JENSEN ON RADII r/2 < 3r/4: MASS ≤ log(M′/‖ξ(z₀)‖)/log(3/2) / M′ = max 1 (‖ξ(z₀)‖ e^B) / ‖ξ′/ξ − FLUX‖ ≤ 16 (B + log 2 · log(M′/‖ξ(z₀)‖)/log(3/2))/r / 3/2 = (3r/4)/(r/2) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `ZeroFactorizationExists.exists_zeroFactorization_count`: the constructed zero
factorization's total multiplicity equals the divisor mass of the closed half disc,
`(Z.count : ℤ) = Σᶠ_u divisor f (closedBall z₀ (r/2)) u`, because the half-disc divisor agrees
with the ball divisor at every point of the half disc and vanishes outside it.

[definition] `jensenCeiling C z₀ r = max 1 (‖ξ z₀‖ e^{xiBudget})`, the Jensen ceiling on the
three-quarter circle.

[proved-derived] `finsum_divisor_le`: by Mathlib's Jensen inequality with inner radius `r/2` and
outer radius `3r/4`, the divisor mass of the closed half disc is at most
`log (M′/‖ξ z₀‖) / log (3/2)`. `exists_zeroFactorization_riemannXi_jensen`: Landau's lemma for
`ξ` with the count replaced by that bound, on the `r/8` disc off the zeros:
`‖ξ′/ξ − Σ m_ρ/(z − ρ)‖ ≤ 16 (B + log 2 · log(M′/‖ξ z₀‖)/log(3/2)) / r`.

## Holonic reading

[definition] The comb's population is now paid for by the same growth budget as its background:
the number of receivers in the half disc is at most the growth on the three-quarter circle over
`log(3/2)`, the one halving-and-a-half of radius that Jensen charges per zero. Landau's lemma
for `ξ` is closed: on every disc about a non-zero, the log-derivative is the constructed comb's
flux plus a background, and both the comb size and the background are explicit functions of
the abscissa growth. This is the whole analytic input of the horizontal-segment estimates in the
rectangular explicit formula.

[established-bounded] The explicit formula itself still needs the rectangle contour and the
termwise integration of the Dirichlet series on the right edge; the corpus's circle-contour
port is not the right shape for it and should be re-posed on a rectangle.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/JensenCountsTheComb.lean` and the
  strengthened `RH/ZeroFactorizationExists.lean` compile under `lake env lean` and `lake build`;
  the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.LandauXi`.
