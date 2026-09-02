# Statement B follows from any uniform coherence defect along a terminal tail

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4086 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, generalizing the incoherent closure to the quantitative coherence defect. Assistant derivation for the proofs.
**Band:** COHERENCE DEFECT κ AT A RECEIVER / DEFECT CONSTANT (1+κ)c / SOURCE, RICCATI, GRÖNWALL, AND TAIL BOUND CARRIED WITH κ / COHERENCE-DEFECT CONTROL ⇒ CLOSURE-DRIVE CONTROL ⇒ STATEMENT B / VELOCITY MASS DISCHARGED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesIncoherentSource.lean`, `NavierStokesIncoherentClosure.lean`,
`NavierStokesVelocityMassEnergy.lean` generalized in place (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`CoherenceDefectAt κ k`: `‖adv_k(o)‖² ≤ (1 + κ) Σ'_p ‖feed_{k,p}(o)‖²`; `IncoherentAt k` is the
abbreviation for defect zero. `sum_tsum_sq_feedTerm_le`; `sum_sq_adv_le_of_defect`;
`sum_pow_four_adv_sq_le_of_defect`: `Σ_F |k|⁴ Σ_o ‖adv_k(o)‖² ≤ (1+κ) · 3·2³ (V W₄ + W₀ W₂/(2π)²)`.
`defectConstant κ = (1 + κ) · 3³(2π)²·3·2³`; `sum_sup_sq_l1_nonlinear_sq_le_of_defect`;
`momentEnergy_riccati_incoherent` with `defectConstant κ`; `momentEnergy_cubeFamily_riccati_incoherent`
(drive `21 · defectConstant κ · V₀ / (ν(2π)²)`); `momentEnergy_cubeFamily_le_incoherent`; `moment_two_le`:

```text
W₂(τ) ≤ W₂(s) · exp( 21 (1+κ) c V₀ (τ − s) / (ν (2π)²) ).
```

`CoherenceDefectControl` (`∃ s V₀ κ`, defect at most `κ` at every nonzero receiver along the tail);
`closureDrive_of_coherenceDefect`; `statementB_of_coherenceDefect`; `CoherenceDefectTailControl`
(defect and interior finiteness only; the velocity mass is discharged by `3·2·E_kin(s)`);
`coherenceDefectControl_of_tail`; `moment_two_le_kineticEnergy`; `statementB_of_coherenceDefectTail`;
`officialProblem_of_coherenceDefectTail`.

## Reading

[definition] The conditional theorem is now quantitative: **any uniform finite coherence defect
`κ` along a terminal tail excludes blow-up.** The defect measures how far the feed comb at a
receiver is from its diagonal; `κ = 0` is incoherence, and the exponent grows linearly in `1 + κ`.
So a blow-up at `T` forces the coherence defect at some nonzero receivers to be unbounded as
`t ↑ T`: the feeds must interfere constructively without bound. That is the exact articulation of
Brandon's coherence thesis: the tail cannot grow by many-to-many any-to-any transfer; it needs an
aligned comb, and the defect is the measure of alignment.

[established-bounded] Next: express `κ` at a receiver through the barycentric spread of the feed
comb (`cross_eq_pairs_mul_mean_sq_sub_spread`, `bandFeed_eq_count_mul_barycenter`) so the defect
is a computable statistic-free geometric quantity of the comb; then the Yang--Mills pairing.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesVelocityMassEnergy` green within the 180 s bound.
- Axiom audits: `sum_pow_four_adv_sq_le_of_defect`, `momentEnergy_riccati_incoherent`, `moment_two_le`,
  `statementB_of_coherenceDefect`, `moment_two_le_kineticEnergy`, `statementB_of_coherenceDefectTail`
  each depend on `[propext, Classical.choice, Quot.sound]`.
