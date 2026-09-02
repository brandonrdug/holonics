# Statement B follows from incoherent feeds with bounded velocity mass

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4085 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `statementB_of_incoherence`. Brandon's coherence/relevance direction (the feed comb, cross terms, barycentric collapse) for the hypothesis; assistant derivation for the proofs.
**Band:** GENERIC-WEIGHT FAMILY RICCATI / INCOHERENCE AT A RECEIVER / FEED DIAGONAL PAID BY VELOCITY MASS TIMES MODAL ENERGY / WEIGHT-FOUR INCOHERENT SOURCE IN MOMENTS / INTERPOLATIONS W₂² ≤ W₀W₄ AND W₀² ≤ 3(2π)²VW₂ / WEIGHT-TWO CLOSURE WITH LINEAR DRIVE IN V AND ν / TERMINAL-TAIL W₂ BOUND / INCOHERENT CONTROL ⇒ CLOSURE-DRIVE CONTROL ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesIncoherentSource.lean` and
`NavierStokesIncoherentClosure.lean` (registered; axioms `[propext, Classical.choice, Quot.sound]`;
no `sorry`).

Source owner. `sup_pow_l1_nonlinear_sq_le (w)`: `|k|^w ℓ¹(N_k)² ≤ 3³(2π)²|k|^{w+2} Σ_o ‖adv_k(o)‖²`.
`momentEnergy_riccati_gen (w)`: `M_w(F)' ≤ −2ν(2π)² M_{w+2}(F) + 2√(3M_w(F)) √(Σ_F |k|^w ℓ¹(N_k)²)`.
`velPop`, `velocityMass V = Σ' velPop`, `modalEnergy_eq_velPop` (`E_q = (2π)² |q|₂² V(q)`),
`sup_pow_four_velPop_le` (`|q|⁴ V(q) ≤ momentPop 2 / (2π)²`), `sum_sq_feedTerm_le`
(`Σ_o ‖feed_{k,p}(o)‖² ≤ 3 V(p) E_{k−p}`), `IncoherentAt k` (`‖adv_k(o)‖² ≤ Σ'_p ‖feed_{k,p}(o)‖²`),
`sum_sq_adv_le_of_incoherent`, `frequencySup_pow_four_le` (`|k|⁴ ≤ 2³(|k−p|⁴ + |p|⁴)`),
`sum_shift_le_moment`, `sum_pow_four_adv_sq_le_of_incoherent`:
`Σ_F |k|⁴ Σ_o ‖adv_k(o)‖² ≤ 3·2³ (V W₄ + W₀ W₂/(2π)²)` on incoherent receivers.

Closure owner. `moment_add_two_sq_le (w)`: `W_{w+2}² ≤ W_w W_{w+4}`; `moment_two_sq_le`;
`moment_zero_sq_le`: `W₀² ≤ 3(2π)² V W₂`; `sqrt_add_le`; `incoherentConstant c = 3³(2π)²·3·2³`;
`sum_sup_sq_l1_nonlinear_sq_le_of_incoherent`; `momentEnergy_riccati_incoherent`:

```text
M₂(F)' ≤ −2ν(2π)² M₄(F) + (3/2)ν(2π)² W₄ + (3cV/(ν(2π)²)) M₂(F) + (18cV/(ν(2π)²)) W₂.
```

`moment_le_cubeFamily (w, d)`: `W_w ≤ M_w(cube N) + W₁₁/(N+1)^d` for `w + d = 11`;
`momentEnergy_cubeFamily_riccati_incoherent`: drive `21cV₀/(ν(2π)²)`, forcing `W₁₁/(N+1)⁷`;
`momentEnergy_cubeFamily_le_incoherent` (Grönwall); `moment_le_of_cubeFamily_le (w, d)` (`N → ∞`);
`moment_two_le`: on `[s, τ] ⊂ (0, T)` with incoherent nonzero receivers, `V ≤ V₀`, and `W₁₁`
finite there, `W₂(τ) ≤ W₂(s) · exp(21 c V₀ (τ − s)/(ν(2π)²))`.
`IncoherentControl`; `l1Pop_zero_le_sqrt` (`ℓ¹(û(0)) ≤ √(3V₀)`); `closureBound`;
`closureDrive_le_closureBound`; `closureDrive_of_incoherent : IncoherentControl → ClosureDriveControl`;
`statementB_of_incoherence`; `officialProblem_of_incoherence`.

## Reading

[definition] Incoherence at a receiver is the tsum form of the nonpositive cross term of the feed
comb (`bandCrossTerm_nonpos_iff`, `norm_bandFeed_le_of_crossTerm_nonpos`): the feeds into `k` from
different senders do not interfere constructively. Under it, the weight-two drive is linear with a
coefficient that carries only the velocity mass and the viscosity; the weight-four part is absorbed
by the dissipation. No smallness is needed. The sole Millennium content that remains under this
hypothesis is the velocity-mass bound `V ≤ V₀` along the tail, which is the Fourier form of the
energy inequality (Parseval plus the energy identity), and the interior finiteness of `W₁₁`.

[established-bounded] Read against the coherent case: a blow-up needs receivers whose feeds
interfere constructively at the growth weights, i.e. a coherent comb. The next owners are (i) the
Fourier energy identity discharging `V ≤ V₀`, and (ii) the quantitative coherence defect: replace
`IncoherentAt` by `‖adv_k‖² ≤ (1 + κ) Σ' ‖feed‖²` and carry `κ` through the same ladder.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesIncoherentClosure` green within the 180 s bound.
- Axiom audits: `momentEnergy_riccati_gen`, `sum_pow_four_adv_sq_le_of_incoherent`, `moment_two_sq_le`,
  `moment_zero_sq_le`, `momentEnergy_riccati_incoherent`, `moment_two_le`, `statementB_of_incoherence`
  each depend on `[propext, Classical.choice, Quot.sound]`.
