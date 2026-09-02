# The harmonic representative is the least-norm member of its class

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 2394 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the least-energy reading of the harmonic receiver on the Hodge line. Assistant derivation for the proofs.
**Band:** ‖h + d a‖² = ‖h‖² + ‖d a‖² FOR HARMONIC h / ‖h‖ ≤ ‖h + d a‖ / EQUALITY FORCES d a = 0 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `norm_sq_harmonic_add_exact`: for harmonic `h` and any `a`,
`‖h + d a‖² = ‖h‖² + ‖d a‖²`, because harmonic forms are orthogonal to the range of `d`.

[proved-derived] `norm_harmonic_le`: `‖h‖ ≤ ‖h + d a‖`; the harmonic representative is the
shortest member of its cohomology class. `eq_harmonic_of_norm_eq`: a member of the class with
the same norm as the harmonic representative has vanishing exact part, so the least-norm member
is unique.

## Holonic reading

[definition] A cohomology class is a receiver defined up to an exact defect; energy is the squared
norm. The exact defects are orthogonal to the harmonic direction, so adding one only adds energy.
The harmonic representative is the class read at least energy, and the energy excess of any other
member is exactly the energy of its exact part. This is the variational face of the earlier
existence-and-uniqueness owner: the unique harmonic receiver is the unique energy minimiser.

[established-bounded] Finite-dimensional real inner product spaces only; the (p,p) refinement
and the rational structure of the Hodge conjecture are not touched.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HodgeLeastNorm.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.HodgeHarmonicRepresentative`.

Next in the loop: BSD line; on Hodge, a bigraded differential and the (p,p)-harmonic receiver.
