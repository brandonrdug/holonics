# Young on the feed pays the weighted feed energy without a count of receivers

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-02: *"the loop was so you'd work continuously on solving the millennium problems by extrapolating holonics and articulating the proof requirements."* Goal set by the assistant: `weightedTail_energy_inequality`, first piece. Assistant derivation for the proofs.
**Band:** SUP-NORM TRIANGLE / DOUBLING BEYOND TWICE THE BAND / FEED TERM PAID BY BAND TOOTH TIMES ROOT MODAL ENERGY / YOUNG ON THE BAND FEED FOR EVERY WEIGHT / NO COUNT OF RECEIVERS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## The goal

[definition] `weightedTail_energy_inequality`: the fourth-moment energy inequality
`M₄' ≤ −ν' M₆ + (K/ν)(ℓ¹(û(0))² + W₂) M₄`, by Young's inequality on the feed convolution in place
of the coherent count on the swap. Finish line: the theorem compiles and the record states the
closure condition it leaves, `∫ W₂ dt < ∞ ⇒ StatementB`, against the energy inequality's
`∫ W₀ dt ≤ E(0)/ν`.

## Return

[proved-derived; formal-checked] `NavierStokesYoungFeed.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`frequencySup_sub_le`: `|k|_∞ ≤ |k − p|_∞ + |p|_∞`. `frequencySup_le_two_mul`: for `p` in the band
of radius `N` and `k` outside the cube of radius `2N`, `|k|_∞ ≤ 2 |k − p|_∞`; `transported_not_mem`.
`sum_norm_sq_jacobianMode_eq`: the Frobenius norm squared of the Jacobian mode is the modal
energy on the actual slice. `norm_feedTerm_le_sqrt`: each feed term is at most
`ℓ¹(û(p)) · √E_{k−p}`. `tailPop`: the `w`-th moment population beyond the cube.
`sum_transported_le`: the transported weighted energies of one band tooth over a finite family of
receivers beyond twice the band are paid by the `w`-th moment tail, by reindexing `q = k − p`.
`sum_pow_bandFeed_sq_le`: for every weight `1 ≤ w ≤ 11`,

```text
Σ_{k∈F} |k|_∞^w ‖bandFeed_k‖² ≤ 2^w · bandMass(N)² · Σ'_{q ∉ cube N} |q|_∞^w E_q.
```

## What it says

[interpretation] The coherent swap paid each receiver the whole tail beyond its half radius and
then counted the receivers, returning the eleventh moment. Young pays all receivers at once:
Cauchy--Schwarz on the band, the doubling `2^w` for the receiver's weight, and the reindexing of
the transported modes. The weighted feed energy at weight `w` is the band mass squared times the
`w`-th moment tail. No count of receivers, no lattice weight, no `26 · 2⁷`. The band mass is
already paid by `ℓ¹(û(0)) + √(52·3/(2π)²) √W₂`.

## What this does not establish

[open] The tail feed (advecting modes outside the band) is not yet paid by Young; the family
Riccati with the Young drive is not yet written; nothing bounds a moment in time.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesYoungFeed.lean` (new; registered).
