# The coherence defect is bounded by the participation number of the feed comb

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4089 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, reading the defect as an effective tooth count (Brandon's orbitals/shells remark). Assistant derivation for the proofs.
**Band:** ‖Σ'z‖² ≤ (Σ'‖z‖)² / PARTICIPATION NUMBER P = (Σ'‖z‖)²/Σ'‖z‖² / 1+κ ≤ P / PARTICIPATION TAIL CONTROL ⇒ COHERENCE DEFECT ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesCombParticipation.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`norm_tsum_sq_le_tsum_norm_sq`; `norm_tsum_sq_le_of_participation`; `summable_norm_feedTerm`;
`ParticipationAt κ k`: `(Σ'_p ‖feed_{k,p}(o)‖)² ≤ (1+κ) Σ'_p ‖feed_{k,p}(o)‖²`;
`coherenceDefectAt_of_participation`; `ParticipationTailControl`;
`coherenceDefectTail_of_participation`; `statementB_of_participation`;
`officialProblem_of_participation`.

## Reading

[definition] The participation number `P_k = (Σ'‖feed‖)²/Σ'‖feed‖²` is the effective number of
teeth carrying the feed into `k` (one tooth gives `P = 1`; `n` equal teeth give `P = n`). The
coherence defect is at most `P_k − 1`: a comb can only interfere constructively as far as its
effective tooth count allows. So Statement B follows from a uniform bound on the participation
number of the feed combs along a terminal tail, and a blow-up needs receivers fed by an
effectively unbounded number of aligned teeth. This is the third geometric face of the defect,
after the cross term and the barycentre.

[established-bounded] Next in the loop: RH Weil positivity on the existing finish line, with the
zero receiver read as a comb whose off-line orbits are the cross terms.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesCombParticipation` green within the 180 s bound.
- Axiom audits: `coherenceDefectAt_of_participation`, `statementB_of_participation` each depend on
  `[propext, Classical.choice, Quot.sound]`.
