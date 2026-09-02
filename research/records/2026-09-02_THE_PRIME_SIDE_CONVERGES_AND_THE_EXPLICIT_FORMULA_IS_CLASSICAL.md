# The prime side converges and the explicit formula is classical

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9746 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, closing the explicit formula: the prime side converges as the height grows (absolute convergence of the archimedean integrals, Tannery's theorem for the von Mangoldt sum), so the weighted zero comb of ξ converges to the prime side at infinite height, for every entire weight of strip decay and in particular for every Weil test function of the corpus. Assistant derivation for the proofs.
**Band:** (1+|t|)^{−k} INTEGRABLE FOR k ≥ 2 / h·archimedean AND h·Λ(n)s^{−n} INTEGRABLE ON THE LINE / ∫_{−T}^{T} → ∫_ℝ / TANNERY EXCHANGES THE HEIGHT LIMIT WITH THE VON MANGOLDT SUM / primeSide δ h T → primeSideLimit δ h / 2πi·zeroSide δ h (T_n) → primeSideLimit δ h / FOR EVERY WEIL TEST FUNCTION / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `primeSideLimit δ h`: the prime side on the line `Re s = 1 + δ` with improper
integrals over the whole line, for the weights `h(s)` and `h(1 − s)`: each is the archimedean
integral minus the von Mangoldt sum, multiplied by `i`.

[proved-derived] `integrable_decay`: `(1 + |t|)^{−k}` is integrable for `k ≥ 2`.
`integrable_mul_archimedean`, `integrable_mul_term`: for a continuous weight bounded by
`K/(1 + |t|)^5` on the line and `0 < δ < 1`, the products with the archimedean term (bounded by
`C(1 + |t|)`) and with each von Mangoldt term (of constant norm `|Λ(n)| n^{−1−δ}`) are integrable.
`tendsto_intervalIntegral`: `∫_{−T}^{T} → ∫_ℝ` for integrable integrands.
`tendsto_tsum_intervalIntegral`: Tannery's theorem with the summable bound
`K ‖term_n‖ ∫ (1 + |t|)^{−5}` exchanges the height limit with the sum over `n`.

[proved-derived] `tendsto_primeSide` (**the prime side converges**): for an entire weight with
`‖h(x + it)‖ ≤ K/(1 + |t|)^5` on the strip and `0 < δ < 1`,
`primeSide δ h T → primeSideLimit δ h` as `T → ∞`.

[proved-derived] `explicit_formula_classical` (**the explicit formula, classical form**): under
the same hypotheses there are heights `T_n ∈ [n + 2, n + 3]` with
`2πi · zeroSide δ h (T_n) → primeSideLimit δ h`: the weighted divisor sum of `ξ` over the
growing rectangles converges to the prime side at infinite height.
`explicit_formula_classical_weil`: the same for every Weil test function of the corpus with its
spectral kernel as the weight and no further hypothesis.

## Constants

[definition] The decay order `5 = 4 + 1`: four absorbs the archimedean growth `(1 + |t|)` and
leaves `(1 + |t|)^{−4}`, integrable; the von Mangoldt terms use the full `(1 + |t|)^{−5}`. All
other constants inherited.

## Holonic reading

[definition] The population ledger of `ξ` is closed: for every declared Weil chart the zero
comb, read as the divisor of `ξ` on growing rectangles, converges to the prime comb read twice
from the line `Re s = 1 + δ` together with the archimedean integrals. On the zero side there is
only the divisor of `ξ`; on the prime side only von Mangoldt and `Γ_ℝ`; between them a
rectangle whose horizontal edges vanish along the selected heights. This is the classical
explicit formula as a theorem of the corpus, with every constant an elementary product
expansion.

[established-bounded] The Riemann hypothesis is the statement that this divisor is supported on
the critical line; the explicit formula is its ledger, not its proof. The pair population (the
divisor off the line) is what remains to be shown empty, and the corpus's phase-flow ledger is
where that population's dynamics live.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PrimeSideConverges.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ArchimedeanPolynomialBound`.
- Axiom audit for `explicit_formula_classical_weil`, `explicit_formula_classical`,
  `tendsto_primeSide`: `[propext, Classical.choice, Quot.sound]`.
