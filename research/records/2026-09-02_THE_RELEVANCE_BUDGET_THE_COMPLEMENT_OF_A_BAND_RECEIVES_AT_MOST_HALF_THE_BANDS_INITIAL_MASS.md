# The relevance budget: the complement of a band receives at most half the band's initial mass

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4091 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, formalizing the quantitative face of Brandon's relevance thesis (the tail is fed only by the band) from the band budget. Assistant derivation for the proofs.
**Band:** MODE MASS CONTINUOUS ON THE OPEN LIFESPAN / CUMULATIVE CURRENT C_F(τ) = (E_F(τ)−E_F(s))/2 + ν∫D_F / C_F IS THE ANTIDERIVATIVE OF THE FRONTIER CURRENT Σ'_{k∉F} transfer / −C_F ≤ E_F(s)/2 ≤ 3·E_kin(s) / NO INTEGRABILITY OF THE TRANSFER NEEDED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesRelevanceBudget.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`modeMass_nonneg`, `bandMass_nonneg`, `bandDissipation_nonneg`; `continuousOn_modeMass`,
`continuousOn_bandDissipation` (on `Ioo 0 T`); `uIcc_subset_Ioo`; `intervalIntegrable_bandDissipation`;
`cumulativeCurrent F s τ = (E_F(τ) − E_F(s))/2 + ν ∫_s^τ D_F`; `cumulativeCurrent_self`;
`hasDerivAt_cumulativeCurrent`: `C_F' = Σ'_{k ∉ F} transfer k` at every interior time;
`neg_cumulativeCurrent_le`: `−C_F(τ) ≤ E_F(s)/2` for `s ≤ τ`; `bandMass_le_kineticEnergy`;
`neg_cumulativeCurrent_le_kineticEnergy`: `−C_F(τ) ≤ 3 E_kin(s)`.

## Reading

[definition] `−C_F` is the mass the band has handed to its complement since `s`, and its
derivative is the instantaneous frontier current. It is bounded by half the band's mass at `s`
and hence by three times the kinetic energy at `s`, for every band and every later time. This is
the relevance thesis quantified: the tail cannot be fed by anything but the band, the band's
supply is finite, and dissipation only lowers the supply. A blow-up must therefore concentrate a
bounded supply into an unbounded weighted moment: it is a coherence question, not a supply
question, which is exactly what the coherence-defect closure says from the other side.

[established-bounded] Next in the loop: the tail-side statement, `−C_F` as the cumulative gain
of the complement's mass plus its dissipation, and the pairing of the two budgets into the
conservation of total mass; then Hodge.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesRelevanceBudget` green within the 180 s bound.
- Axiom audits: `hasDerivAt_cumulativeCurrent`, `neg_cumulativeCurrent_le_kineticEnergy` each
  depend on `[propext, Classical.choice, Quot.sound]`.
