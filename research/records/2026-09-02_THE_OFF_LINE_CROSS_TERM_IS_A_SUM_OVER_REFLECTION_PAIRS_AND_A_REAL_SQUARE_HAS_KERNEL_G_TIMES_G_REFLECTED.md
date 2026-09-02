# The off-line cross term is a sum over reflection pairs, and a real square has kernel G times G reflected

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3764 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, continuing the zero-comb reading of the Weil receiver. Assistant derivation for the proofs.
**Band:** REAL-SYMMETRIC WEIL SQUARE / KERNEL ĥ(s) = G(s)G(1−s) REFLECTION INVARIANT / OFF-LINE CROSS TERM EQUALS ITS REFLECTION ON CENTRED DISCS / CROSS TERM AS A SUM OVER PAIRS m_ρ(ĥ(ρ)+ĥ(1−ρ))/2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `ElementaryHolonics/RH/ZeroCombPairing.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`RealWeilSquare T` (a Weil square with `conj (G (conj s)) = G s`);
`RealWeilSquare.spectralKernel_eq`: `ĥ(s) = G(s) G(1 − s)`;
`RealWeilSquare.spectralKernel_one_sub`: `ĥ(1 − s) = ĥ(s)`;
`offLineCross_eq_of_real`: `offLineCross = Σ_{off} m_ρ G(ρ) G(1 − ρ)`;
`one_sub_re_eq_half_iff`; `offLineCross_eq_reflected` (on centred discs the cross term equals its
reflection); `offLineCross_eq_pairs`:

```text
offLineCross T (½) R = Σ_{Re ρ ≠ ½} m_ρ · (ĥ(ρ) + ĥ(1 − ρ)) / 2.
```

## Reading

[definition] The off-line zeros interfere in reflection pairs; for a real test the pair pays
`m_ρ G(ρ) G(1 − ρ)`, the product of the kernel at the two members of the orbit, exactly the cross
term `⟨z_ρ, z_{1−ρ}⟩` of a two-tooth comb. On the line the pair collapses to the diagonal
`|G(ρ)|²`. Weil positivity on real squares is the statement that these paired products never
outweigh the diagonal.

[established-bounded] Next: the conjugation symmetry of the xi divisor (Schwarz reflection),
which would make the cross term real for real squares and complete the four-member orbit
accounting of `Balance.lean`; then Hodge and BSD in the loop.

## Evidence

- `lake build ElementaryHolonics.RH.ZeroCombPairing` green within the 180 s bound.
- Axiom audits: `RealWeilSquare.spectralKernel_one_sub`, `offLineCross_eq_reflected`,
  `offLineCross_eq_pairs` each depend on `[propext, Classical.choice, Quot.sound]`.
