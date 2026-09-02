# The sign law: the functional-equation sign is the parity of the analytic rank

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3488 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the parity reading of the functional-equation sign on the BSD line. Assistant derivation for the proofs.
**Band:** REFLECTION f(2c − s) = ε f(s) / LEADING COEFFICIENT ε = (−1)^m / COMPLETED FUNCTION ORDER = ANALYTIC RANK VIA THE NONVANISHING ARCHIMEDEAN PREFACTOR / SIGN +1 ⇒ EVEN RANK / SIGN −1 ⇒ ODD RANK / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `sign_eq_neg_one_pow_of_reflection`: if `f` is analytic at `c`, satisfies
`f (2c − s) = ε · f s` for every `s`, and has finite order `m` at `c`, then `ε = (−1)^m`. The
order characterisation writes `f = (z − c)^m · g` near `c` with `g c ≠ 0`; the reflection
identity forces `(−1)^m · g (2c − z) = ε · g z` on the punctured neighbourhood, and the two
sides are continuous at `c`, so `(−1)^m · g c = ε · g c` and `g c` cancels.

[proved-derived] `archimedeanPrefactor N s = (√N / 2π)^s · Γ s` is analytic and nonvanishing at
`s = 1`; near the centre the completed function is the prefactor times `L`
(`Lambda_eventuallyEq`, from the datum's product chart away from the poles of `Γ`), so
`analyticOrderAt_Lambda_eq_analyticRank`: the central order of the completed function is the
analytic rank.

[proved-derived] `theSignIsTheParityOfTheAnalyticRank`: for an L-datum with finite analytic rank
`m`, `sign = (−1)^m`; hence `even_analyticRank_of_sign_one` and
`odd_analyticRank_of_sign_neg_one`. This sharpens the earlier parity owner, which only returned
`rank ≥ 1` from sign `−1`.

## Holonic reading

[definition] The functional equation is the reflection of the centre; the sign is the phase the
receiver acquires under that reflection. A zero of order `m` at the centre is a receiver whose
leading defect transforms with phase `(−1)^m`; the reflection phase and the leading-defect phase
must coincide, so the sign is exactly the parity of the order. Nothing about the algebraic side is
used: this is the analytic half of the parity conjecture, with the rank clause of the earlier
owner supplying the algebraic half under its declared hypothesis.

[established-bounded] The theorem needs the analytic rank to be finite, that is, `L` not
identically zero near the centre. The datum's normalisation `coeff 1 = 1` supplies this on the
half-plane of agreement; carrying it to the centre through the identity theorem is the next seam
on this line.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/BirchSwinnertonDyerSignLaw.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.BirchSwinnertonDyerParity`.

Next in the loop: NS frontier chain; on BSD, finiteness of the analytic rank from the
normalisation through the identity theorem.
