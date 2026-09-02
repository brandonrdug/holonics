# The Weil receiver is a comb: on-line diagonal plus off-line cross term

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3763 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, carrying the comb reading (diagonal plus cross term) from the Navier--Stokes feed comb to the zero receiver of the Riemann xi function. Assistant derivation for the proofs on the line's `ExplicitFormulaReceiver` and `WeilPositivity` owners and Mathlib's order-under-composition lemma.
**Band:** REFLECTION SYMMETRY OF THE XI DIVISOR / CENTRED RECEIVER EQUALS ITS REFLECTION / ON-LINE DIAGONAL ≥ 0 UNCONDITIONALLY / OFF-LINE CROSS TERM VANISHES UNDER RH / WEIL POSITIVITY ON A SQUARE ⟺ BOUND ON THE CROSS TERM / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `ElementaryHolonics/RH/ZeroComb.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`riemannXi_comp_reflection`; `meromorphicOrderAt_riemannXi_one_sub` (the order of `ξ` at `1 − u`
is its order at `u`, by `ξ(1 − s) = ξ(s)` and Mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero`);
`one_sub_mem_closedBall_half_iff`; `divisor_riemannXi_one_sub` (the xi divisor on a centred disc is
reflection symmetric); `truncatedZeroReceiver_eq_reflected` (the centred receiver equals the
receiver of the reflected kernel). `onLineDiagonal W c R = Σ_{Re ρ = ½} m_ρ |G(ρ)|²`;
`offLineCross T c R = Σ_{Re ρ ≠ ½} m_ρ ĥ(ρ)`; `onLineDiagonal_nonneg`;
`truncatedZeroReceiver_eq_diagonal_add_cross`; `offLineCross_eq_zero_of_RH`;
`isNonnegativeReal_iff_cross`:

```text
receiver ∈ [0, ∞)   ⟺   offLineCross is a real number ≥ −onLineDiagonal.
```

## Reading

[definition] The zero receiver of a Weil square is a comb exactly as the Navier--Stokes feed
comb: the on-line zeros are the diagonal (each tooth pays `m_ρ |G(ρ)|² ≥ 0`), the off-line zeros
are the cross term. RH is the statement that the comb is purely diagonal; Weil positivity on
squares is the statement that the cross term never pushes the receiver off the nonnegative ray.
The four-member orbits of `Balance.lean` are the interfering pairs. In the NS vocabulary, RH is
incoherence of the zero comb and the coherence defect is the off-line cross term.

[established-bounded] The proof requirement for the finish line's `arithmeticPositivity` is now
localized: it is a bound on the off-line cross term by the diagonal for every square, and the
`offLineSeparation` requirement is a square whose cross term at an alleged off-line orbit
dominates every other contribution. Next: the reflection pairing of the cross term on centred
discs (`ĥ(ρ) + ĥ(1 − ρ)` per pair) and its sign structure under a test with `G` real on the line.

## Evidence

- `lake build ElementaryHolonics.RH.ZeroComb` green within the 180 s bound.
- Axiom audits: `meromorphicOrderAt_riemannXi_one_sub`, `divisor_riemannXi_one_sub`,
  `truncatedZeroReceiver_eq_reflected`, `truncatedZeroReceiver_eq_diagonal_add_cross`,
  `isNonnegativeReal_iff_cross` each depend on `[propext, Classical.choice, Quot.sound]`.
