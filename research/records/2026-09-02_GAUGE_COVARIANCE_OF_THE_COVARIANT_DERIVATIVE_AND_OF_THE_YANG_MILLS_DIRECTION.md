# Gauge covariance of the covariant derivative and of the Yang--Mills direction

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3727 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the Y1 gauge-rebase clause at the level of the flow direction on the Yang--Mills line. Assistant derivation for the proofs.
**Band:** D^{A^g}(g X g⁻¹) = g (D^A X) g⁻¹ / YM(A^g) = g · YM(A) · g⁻¹ / LEIBNIZ + DIFFERENTIATED UNIT LAW + CANCELLATION / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `covariantDerivative_gaugeTransform`: for a differentiable section `X` and a
`C²` gauge, `D^{A^g}_i (g X g⁻¹) = g (D^A_i X) g⁻¹`. The Leibniz expansion of `∂_i(g X g⁻¹)`
produces three terms; the bracket with `A^g = g A g⁻¹ + g ∂g⁻¹` produces the conjugated bracket
plus two terms which, through the differentiated unit law `∂g⁻¹ = −g⁻¹ (∂g) g⁻¹`, cancel the two
outer Leibniz terms exactly.

[proved-derived] `yangMillsDirection_gaugeTransform`: for a `C²` connection,
`YM(A^g) = g · YM(A) · g⁻¹`, by the curvature covariance of the earlier owner and the covariant
derivative covariance summed over the coordinate directions.

## Holonic reading

[definition] The covariant derivative is the transport-corrected defect of a section; a gauge
rebases every fibre, and the correction term of the transformed connection absorbs exactly the
derivative of the rebasing. The Yang--Mills direction is the divergence of the curvature defect;
it rebases the same way. Together with the energy invariance this closes the Y1 gauge-rebase
clause for the whole descent apparatus: the energy, its gradient direction, and the curvature all
live on the orbit space.

[established-bounded] Sections are conjugated by the gauge, connections transform affinely; the
Hessian's covariance follows the same pattern and is not yet written.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicCovariantDerivativeCovariance.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.HolonicYangMillsGaugeInvariance`.

Next in the loop: NS coherence half; RH certification of `ξ(½) ≠ 0`; Hodge bigraded
differential.
