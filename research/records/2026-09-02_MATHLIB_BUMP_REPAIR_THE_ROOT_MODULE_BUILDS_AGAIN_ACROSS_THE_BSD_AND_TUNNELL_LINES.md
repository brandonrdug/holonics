# Mathlib bump repair: the root module builds again across the BSD and Tunnell lines

**Date:** 2026-09-02
**Truth status:** `established-bounded`
**Evidence:** `formal-checked` (Lean `v4.33.0`; `lake build ElementaryHolonics` green); `measured` (`lake` job count: 9703 jobs for the root module)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, repairing forty-six Lean owners broken by the pinned Mathlib bump, found when the root module was built for the Hodge registration. Assistant derivation for the proofs.
**Band:** ROOT MODULE RED SINCE THE 2026-08-31 CONSOLIDATION / 46 OWNERS REPAIRED / NO STATEMENT CHANGED / QUATERNION LITERALS MADE OPAQUE / INTEGER INTERVAL INSTANCE PINNED / SERIES TOPOLOGY MADE REDUCIBLE / ROOT BUILD GREEN AT 9703 JOBS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Finding

[established-bounded] Building the root module `ElementaryHolonics` for the Hodge registration
showed it red: forty-six owners on the BSD, Tunnell, Brandt, Jacobi, and Hopf lines no longer
compiled against the Mathlib pinned by the 2026-08-31 consolidation. Every failing file dates from
2026-08-22 or 2026-08-23; the breakage is the toolchain's, not the mathematics'. No theorem
statement was weakened; only proofs, definitions of literals, and lemma names changed.

## Root causes and the repair

- [established-bounded] `WeierstrassCurve.Affine.Point.some` now takes the coordinates
  explicitly: one-argument calls became `Point.some _ _ h`; the height and match patterns were
  rewritten accordingly.
- [established-bounded] `padicValRat.pow` no longer takes a nonvanishing hypothesis; `Point.some`,
  `Nat.factorization_eq_zero_of_not_prime`, `eq_zero_of_pow_eq_zero`,
  `Finset.HasAntidiagonal.mem_antidiagonal`, `AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff`,
  and `AddMonoidHom.coe_toIntLinearMap` are the renamed or reshaped lemmas.
- [established-bounded] `Finset.Icc` on `ℤ` now resolves its preorder through the noncomputable
  `Int.instConditionallyCompleteLinearOrder`, so `native_decide` over integer boxes failed.
  `heckeShell` pins the computable `Int.instLinearOrder` path explicitly; the reducible lattice
  census `SolFr`/`SFr` was made computable while the interval census `SolF`/`SF` stays
  noncomputable.
- [established-bounded] Anonymous quaternion literals now elaborate at the underlying
  `QuaternionAlgebra` type, and the `Quaternion` component simp lemmas were removed. The bridge
  owner gained an opaque constructor `hmk` with component laws, definitional component lemmas for
  add, neg, sub, star, and mul on `HamiltonInt` (the primed forms carry the structure constants
  `(-1, 0, -1)`), and one/zero/coe component lemmas. Pivot, phase-turn, Gaussian-source, Lipschitz
  unit, and order-unit literals now use `hmk`; the unit classification no longer destructures the
  quaternion.
- [established-bounded] `AddMonoidAlgebra` is now a structure with field `coeff`; the Gauss-factor
  owner reads Laurent bodies through a local `CoeFun` instance onto `AddMonoidAlgebra.coeff`, and
  the unit-theta receiver names the coefficient field.
- [established-bounded] `integerSeriesPiTop` became a reducible abbreviation so that the scoped
  `ContinuousMul` and `T2Space` instances of the coefficient topology are found through it;
  rewrites under the local `letI` use `erw` or `refine … .mpr`.
- [established-bounded] Remaining sites were simp-set widenings (`reduceTriple`,
  `Prod.mk_zero_zero`, occurrence coercions, isotropic-vector unfoldings) and `convert` instance
  goals closed by `rfl`.

## Evidence

- `lake build ElementaryHolonics` completes: 9703 jobs, no error. Every repaired owner also
  passes `lake env lean` alone. Axiom audits printed by the owners are unchanged.
- The Hodge record of the preceding commit is corrected to name its owner-cone job count.

Next in the loop: Provenance receipts for the Hodge and repair commits, then BSD sign law and the
NS frontier chain.
