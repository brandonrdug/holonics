# Gauge invariance of the first and second variations of the Yang--Mills energy

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3729 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the Y1 gauge-rebase clause at the level of the variations on the Yang--Mills line. Assistant derivation for the proofs.
**Band:** (A + εB)^g = A^g + ε g B g⁻¹ / A^g AND g B g⁻¹ ARE C¹ / ENERGY ALONG THE TRANSFORMED LINE = ENERGY ALONG THE LINE / FIRST VARIATION INVARIANT / HESSIAN INVARIANT / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `gaugeDirection G B = g B g⁻¹` is the gauge action on a direction.

[proved-derived] `gaugeTransform_add_smul`: the gauge acts affinely along a line,
`(A + εB)^g = A^g + ε · gaugeDirection G B`. `contDiff_gaugeTransform` and
`contDiff_gaugeDirection`: for `C²` data and a `C²` gauge the transformed connection and
direction are `C¹`.

[proved-derived] `yangMillsEnergy_gauge_line`: the energy along the transformed line equals the
energy along the original line for every `ε`, by the energy invariance at `A + εB`.
`firstVariation_gaugeTransform` and `hessian_gaugeTransform`: matching the first and second
Taylor coefficients at `ε = 0` returns the invariance of the first variation and of the Hessian
under the simultaneous gauge action on connection and direction.

## Holonic reading

[definition] The descent apparatus is a function on lines through a connection; a gauge maps
lines to lines affinely and leaves the energy along each line unchanged. So every derivative of
the energy along a line, the gradient pairing and the Hessian form, is a quantity of the orbit
space. With the covariance of the curvature, the covariant derivative, and the Yang--Mills
direction, the Y1 gauge-rebase clause is now closed for the energy, its gradient, its Hessian,
and its flow direction.

[established-bounded] The direction transforms by conjugation only; gauge-orbit directions
(infinitesimal gauge transformations `D_A ξ`) and the Coulomb slice are not yet named.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicYangMillsVariationInvariance.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.HolonicCovariantDerivativeCovariance`.

Next in the loop: Y1 gauge-orbit directions and the vanishing of the first variation along
them; NS coherence half; RH certification of `ξ(½) ≠ 0`.
