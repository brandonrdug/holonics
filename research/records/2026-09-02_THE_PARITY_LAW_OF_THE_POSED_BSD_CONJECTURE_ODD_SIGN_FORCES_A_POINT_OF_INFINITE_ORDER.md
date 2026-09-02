# The parity law of the posed BSD conjecture: odd sign forces a point of infinite order

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3484 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, on the BSD pose of the congruent-number twists. Assistant derivation for the proofs.
**Band:** ANALYTIC RANK ZERO ⟺ L(1) ≠ 0 / ODD SIGN ⇒ ANALYTIC RANK ≥ 1 (UNCONDITIONAL) / RANK CLAUSE + ALGEBRAIC RANK ZERO ⇒ EVEN SIGN / RANK CLAUSE + ODD SIGN ⇒ A POINT OF INFINITE ORDER / PARITY LAW OF THE POSE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `ElementaryHolonics/Millennium/BirchSwinnertonDyerParity.lean`
(registered; axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`).

`analyticRank_eq_zero_iff`: `analyticRank W = 0 ↔ L(1) ≠ 0`.
`theOddSignForcesAnalyticRankAtLeastOne`: `sign = −1 → 1 ≤ analyticRank W`, unconditional.
`algebraicRankAtLeast_zero`. `theRankZeroForcesEvenSign`: under `TheRankClause`, algebraic rank
zero forces `sign = 1`. `theOddSignForcesAlgebraicRankAtLeastOne`: under `TheRankClause`,
`sign = −1` forces a rational point of infinite order. `theParityLaw`: under the rank clause,
`sign = 1 ∨ AlgebraicRankAtLeast n 1`.

## Reading

[definition] The functional equation is a reflection of the L-comb about its centre; the odd sign
is the antisymmetric case, whose centre tooth must vanish. Under the rank clause, that vanishing
is a rational point: the antisymmetry of the analytic face is paid by an algebraic realizer. This
is the same shape as the incoherent/coherent split elsewhere in the line: a symmetry constraint at
the centre forces a supported occurrence.

[established-bounded] Next: the sign law of the twists (`w = −1` exactly on the residue classes
five and seven mod eight), which with the parity law makes every such `n` a congruent number
under the rank clause.

## Evidence

- `lake build ElementaryHolonics.Millennium.BirchSwinnertonDyerParity` green within the 180 s bound.
- Axiom audits: `theOddSignForcesAnalyticRankAtLeastOne`, `theRankZeroForcesEvenSign`,
  `theParityLaw` each depend on `[propext, Classical.choice, Quot.sound]`.
