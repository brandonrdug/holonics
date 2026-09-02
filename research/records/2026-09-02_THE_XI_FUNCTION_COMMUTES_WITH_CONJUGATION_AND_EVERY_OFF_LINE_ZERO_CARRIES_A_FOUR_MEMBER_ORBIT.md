# The xi function commutes with conjugation, and every off-line zero carries a four-member orbit

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3765 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the conjugation half of the zero-comb symmetry. Assistant derivation for the proofs on Mathlib's `Gamma_conj`, `cpow_conj`, `riemannZeta_conj`, and the line's classical product.
**Band:** Γ_ℝ COMMUTES WITH CONJUGATION / ξ(s̄) = conj ξ(s) AWAY FROM THE TRIVIAL ZEROS BY THE CLASSICAL PRODUCT / CARRIED ACROSS THE TRIVIAL ZEROS BY THE REFLECTION / ZERO SET CONJUGATION SYMMETRIC / FOUR-MEMBER ORBIT OF ACTUAL ZEROS OFF THE LINE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `ElementaryHolonics/RH/XiConjugation.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`Gammaℝ_conj`: `Γ_ℝ(s̄) = conj Γ_ℝ(s)`. `riemannXi_conj_of_Gammaℝ_ne_zero` (away from `0`, `1`,
and the zeros of `Γ_ℝ`, by `ξ = ½ s(s−1) Γ_ℝ ζ` and `riemannZeta_conj`); `riemannXi_conj`:
`ξ(s̄) = conj ξ(s)` for every `s` (the trivial-zero points carried across by `ξ(1 − s) = ξ(s)`,
since `Γ_ℝ(s)` and `Γ_ℝ(1 − s)` never vanish together). `riemannXi_conj_eq_zero_iff`; `zeroOrbit`:
with `ρ` the points `1 − ρ`, `ρ̄`, `1 − ρ̄` are zeros; `orbitDistinct`: off the line and off the
real axis the four are pairwise distinct.

## Reading

[definition] The zero comb of `ξ` is closed under both involutions of `Balance.lean`; an off-line
zero never comes alone but as a four-tooth orbit, and RH is the statement that every orbit
collapses to the two-tooth conjugate pair on the line. The remaining seam for the reality of the
Weil receiver is the conjugation symmetry of the divisor with multiplicity, which needs the order
of a meromorphic function under an antiholomorphic involution; Mathlib carries the holomorphic
case only.

[established-bounded] Next in the loop: Hodge, then BSD sign law, then NS frontier coherence.

## Evidence

- `lake build ElementaryHolonics.RH.XiConjugation` green within the 180 s bound.
- Axiom audits: `Gammaℝ_conj`, `riemannXi_conj`, `zeroOrbit`, `orbitDistinct` each depend on
  `[propext, Classical.choice, Quot.sound]`.
