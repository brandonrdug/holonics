# The fourth-moment tail cost is the eleventh moment, and the ladder gap is five

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: `/loop` with the goal `weightedTailEnergy_riccati`, third piece. Assistant derivation for the proofs.
**Band:** SWAP OF SUMMATION PROVED / FEEDABLE MODES COUNTED / EXPONENT ELEVEN DERIVED / LADDER GAP FIVE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesMomentSwap.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`tailMass_le_of_weighted_succ`: the Jacobian tail mass beyond the cube of radius `m` is at most
`√(52 C)` when every finite partial sum of `|q|_∞⁴ E_q` over modes with `|q|_∞ ≥ m + 1` is at most
`C`, with no threshold on `m`. `tailJ_sq_le`: `tailJ(r)² ≤ 52 · Σ'_{|q|_∞ ≥ r+1} |q|_∞⁴ E_q`.
`halfRadius_succ_le_iff`: `q` lies beyond the half radius of `k` exactly when `|k|_∞ ≤ 2 |q|_∞`.
`sum_pow_four_filter_le`: the modes with `|k|_∞ ≤ 2s` carry fourth-moment weight at most
`26 · 2⁷ · s⁷`, by fibring over the sup-norm with the shell count `26 j²` and `Σ_{j ≤ 2s} j⁶ ≤ 2s · (2s)⁶`.
`sum_pow_four_tailJ_sq_le`: for any finite family of nonzero modes, with the eleventh moment
summable,

```text
Σ_k |k|_∞⁴ · tailJ(⌊(|k|_∞ − 1)/2⌋)²  ≤  52 · 26 · 2⁷ · Σ'_q |q|_∞¹¹ E_q.
```

## What it says

[interpretation] The exponent `11 = 4 + 7` is exact: the receiver's weight `4`, and `7 = 6 + 1`
from the feeding side, where `6 = 2 + 4` is the shell face times the feeding mode's weight and
the `1` is the count of shells. The fourth-moment Riccati dissipates at weight `6`. The driving
moment is `11`. The ladder gap is `5`, an integer, and the constants are `52 · 26 · 2⁷ =
2 · 26 · 26 · 2⁷`: the telescoping `2`, the shell face `26` twice, and the doubling `2⁷` of the half
radius. Closing at weight four needs weight eleven; that is the supercritical ladder as one
integer, with no analytic vocabulary in it.

## What this does not establish

[open] The band factor and the velocity-tail term of `incoherentCost` are not yet read in moments;
the assembled inequality for `momentCost` is the next owner. Nothing bounds any moment in time.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesMomentSwap.lean` (new; registered).
