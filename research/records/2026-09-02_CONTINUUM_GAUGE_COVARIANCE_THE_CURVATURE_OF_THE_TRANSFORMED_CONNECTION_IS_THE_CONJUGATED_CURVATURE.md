# Continuum gauge covariance: the curvature of the transformed connection is the conjugated curvature

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3720 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the Y1 gauge-rebase clause in the continuum. Assistant derivation for the proofs.
**Band:** GAUGE = C² UNITS WITH INVERSE / A^g = gAg⁻¹ + g∂g⁻¹ / DIFFERENTIATED UNIT LAW ∂g⁻¹ = −g⁻¹(∂g)g⁻¹ / LEIBNIZ EXPANSION OF ∂A^g / F(A^g) = g F g⁻¹ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicGaugeCovariance.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`Gauge n 𝔤` (a `C²` family `g` with its inverse `g⁻¹`); `gaugeTransform G A`:
`A^g_i = g A_i g⁻¹ + g ∂_i g⁻¹`; `Gauge.differential_ginv`: `∂_i g⁻¹ = −g⁻¹ (∂_i g) g⁻¹`;
`differential_gaugeTransform` (the Leibniz expansion of `∂_k A^g_l`); `curvature_gaugeTransform`:

```text
F(A^g)_ij = g F_ij g⁻¹.
```

## Reading

[definition] The curvature transforms by conjugation: the returned face defect is the same
defect read in the rebased fibre. This is the continuum twin of the discrete face covariance
already proved on the four-force carrier (`returnedCurvature_gaugeTransform`), and it closes the
Y1 contract's gauge-rebase clause: connection, curvature, covariant derivative, Bianchi, gauge
covariance in both readings, first and second variation, Weitzenböck, flow direction, descent, and
the abelian reduction to the fluid.

[established-bounded] Next in the loop: NS frontier chain, BSD sign law, RH divisor conjugation;
on Y1, gauge invariance of the Yang--Mills energy under an ad-invariant pairing
(`B(g x g⁻¹, g y g⁻¹) = B(x, y)` needs the integrated invariance, a separate port).

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicGaugeCovariance` green within the 180 s bound.
- Axiom audits: `Gauge.differential_ginv`, `curvature_gaugeTransform` each depend on
  `[propext, Classical.choice, Quot.sound]`.
