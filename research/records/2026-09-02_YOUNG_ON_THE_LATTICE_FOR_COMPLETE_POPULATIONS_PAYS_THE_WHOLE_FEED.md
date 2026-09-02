# Young on the lattice for complete populations pays the whole feed

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** CAUCHY-SCHWARZ ON COMPLETE CONVOLUTIONS / YOUNG L1 TIMES L2 INTO L2 ON THE FREQUENCY LATTICE / WHOLE FEED PAID WITHOUT SPLIT / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesYoungTsum.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`). For nonnegative populations `a`
(absolutely summable) and `b` (square summable) on the integer frequency lattice:

`sq_le_tsum_sq`, `summable_conv`, `summable_conv_sq`: the convolution population at one receiver
is summable. `conv_sq_le`: Cauchy--Schwarz on the complete convolution,
`(Σ'_p a_p b_{k−p})² ≤ (Σ'_p a_p) · Σ'_p a_p b_{k−p}²`, through the supremum of nonnegative partial
sums. `young_l1_l2`: for every finite family of receivers,

```text
Σ_{k∈F} (Σ'_p a_p b_{k−p})² ≤ (Σ'_p a_p)² · Σ'_q b_q²,
```

by exchanging the finite receiver sum with the complete advecting sum and reindexing `q = k − p`.

## What it says

[interpretation] The whole feed, band and tail alike, is paid at once with no split, no count,
and no lattice weight: the `ℓ¹` mass of the advecting population squared times the `ℓ²` energy of
the transported population. With weights, the receiver's weight is shared between the two legs by
the sup-norm triangle inequality, which is the next owner, and it returns the classical product
estimate in the tree's own faces.

## What this does not establish

[open] Weights are not yet placed; the family Riccati with the Young drive is not yet written.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesYoungTsum.lean` (new; registered).
