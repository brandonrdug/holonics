# The Weitzenböck evolution along the Yang–Mills direction: the curvature diffuses and interacts only through adjacent faces

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3720 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, on the Y1 covariant-lift contract. Assistant derivation for the proofs on the connection-curvature and variation owners.
**Band:** SMOOTHNESS BOOKKEEPING FOR ∂, F, D / LINEARITY OF D / YANG–MILLS DIRECTION G_j = Σ_k D_kF_kj / WEITZENBÖCK (D_A G)_ij = Σ_k(D_kD_kF_ij + 2[F_ik,F_kj]) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsFlow.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`contDiff_differential`, `contDiff_bracket`, `contDiff_curvature`, `contDiff_covariantDerivative`
(a `C^{m+1}` connection has `C^m` curvature and covariant derivatives); `covariantDerivative_neg_sub`,
`covariantDerivative_neg`, `covariantDerivative_finsetSum`; `yangMillsDirection A j = Σ_k D_k F_kj`;
`covariantVariation_yangMillsDirection`: for a `C³` connection,

```text
(D_A G)_ij = Σ_k ( D_k D_k F_ij + [F_ik, F_kj] + [F_ik, F_kj] ).
```

## Reading

[definition] With the first variation of curvature this is the evolution of the curvature under the
Yang--Mills heat flow: a covariant diffusion of the face defect plus a quadratic self-interaction
that couples only adjacent faces through the commutator. The proof spends exactly Bianchi twice,
Ricci twice, and antisymmetry: the same three facts as the Navier--Stokes join, in the
noncommutative rebase. This is the Y1 contract's "noncommutation must return the curvature
commutator" made exact.

[established-bounded] Next on Y1: the energy identity once an ad-invariant inner product on `𝔤`
and a compact base are admitted (`d/dt YM(A) = −Σ_j ‖G_j‖²`); then the pairing with the NS
vorticity Riccati under the reading `F ↔ ω`, `[F, F] ↔` the aligned strain.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsFlow` green within the 180 s bound.
- Axiom audit: `covariantVariation_yangMillsDirection` depends on `[propext, Classical.choice, Quot.sound]`.
