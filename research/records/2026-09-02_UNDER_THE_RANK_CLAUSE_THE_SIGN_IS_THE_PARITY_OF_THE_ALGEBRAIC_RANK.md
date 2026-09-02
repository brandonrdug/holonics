# Under the rank clause, the sign is the parity of the algebraic rank

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3489 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the parity conjecture of the pose under the rank clause on the BSD line. Assistant derivation for the proofs.
**Band:** SIGN LAW ∘ RANK CLAUSE / sign = (−1)^r AT ALGEBRAIC RANK r / sign = +1 ⇔ EVEN RANK / sign = −1 ⇔ ODD RANK / RANK CLAUSE IS THE ONLY HYPOTHESIS / NO CONJECTURE CLOSED UNCONDITIONALLY / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `sign_eq_neg_one_pow_algebraicRank`: under `TheRankClause n W` and
`AlgebraicRankIs n r`, `sign = (−1)^r`. It is the sign law composed with the rank clause's
identification of the analytic rank with the algebraic rank.

[proved-derived] `sign_one_iff_even_algebraicRank` and `sign_neg_one_iff_odd_algebraicRank`:
under the rank clause and at algebraic rank `r`, sign `+1` holds exactly when `r` is even and
sign `−1` exactly when `r` is odd. The earlier parity owner returned only the one-way
implication from the odd sign to a point of infinite order; this owner returns the full
biconditional.

## Holonic reading

[definition] The rank clause is the pose's bridge between the analytic receiver (the order of the
centre) and the algebraic receiver (the independent points). The sign law reads the analytic
receiver's parity from the reflection phase; through the bridge the same phase reads the
algebraic receiver's parity. The parity conjecture is therefore not an independent law of the
pose but the shadow of the sign law across the rank clause.

[established-bounded] Every statement here is conditional on `TheRankClause n W`, which is the
BSD rank conjecture itself for the twist; nothing is closed unconditionally.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/BirchSwinnertonDyerAlgebraicParity.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.BirchSwinnertonDyerSignLaw`.

Next in the loop: NS frontier bound into the transfer; Y1 gauge invariance of the Yang--Mills
energy.
