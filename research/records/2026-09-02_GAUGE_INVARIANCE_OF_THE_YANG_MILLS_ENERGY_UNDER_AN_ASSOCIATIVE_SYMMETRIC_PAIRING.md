# Gauge invariance of the Yang--Mills energy under an associative symmetric pairing

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3726 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the Y1 gauge-rebase clause at the level of the energy on the Yang--Mills line. Assistant derivation for the proofs.
**Band:** TRACE LAW B(xy, z) = B(x, yz) / CONJUGATION INVARIANCE B(g x g⁻¹, g y g⁻¹) = B(x, y) / F(A^g) = g F g⁻¹ / YM ENERGY OF A^g = YM ENERGY OF A / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `IsAssociative P`: the symmetric pairing satisfies the trace law
`B (x * y) z = B x (y * z)`.

[proved-derived] `pairing_conj`: for an associative symmetric pairing and a unit `g` with
inverse `ginv`, `B (g x ginv) (g y ginv) = B x y`. Six trace-law and symmetry moves walk the
unit around the pairing and cancel it against its inverse.

[proved-derived] `yangMillsEnergy_gaugeTransform`: for a `C²` connection and a `C²` gauge, the
Yang--Mills energy of the gauge transform equals the energy of the connection, by the curvature
covariance `F(A^g) = g F g⁻¹` of the previous owner and conjugation invariance under the
integral.

## Holonic reading

[definition] The energy is the total squared defect of the connection read through the pairing.
A gauge rebases every fibre; the defect is conjugated but the pairing, being a trace, does not
see the rebasing. So the energy is a property of the connection's orbit, not of its chart: the
Y1 gauge-rebase clause holds at the level of the energy, and the descent and Hessian owners
describe motion on the orbit space.

[established-bounded] Associativity is the trace form's law and is assumed, not derived from
infinitesimal invariance; every matrix trace pairing satisfies it.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicYangMillsGaugeInvariance.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.HolonicGaugeCovariance`.

Next in the loop: NS frontier bound into the transfer; RH on-line mass against the
argument-principle count.
