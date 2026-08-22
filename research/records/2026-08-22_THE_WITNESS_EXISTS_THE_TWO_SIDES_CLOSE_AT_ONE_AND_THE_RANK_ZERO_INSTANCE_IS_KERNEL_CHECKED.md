# The witness exists, the two sides close at one, and the rank-zero instance is kernel-checked

**Date:** 2026-08-22
**Kind:** the return of the direct-attack campaign Brandon set with *"go for the
solution, I do not want to continue taking baby-steps"* and the goal *"complete your
suggested turns 2–7; go until you hit a real BSD wall."*  Solo orchestrator work, five
Lean files across six commits (`4aa9dbb`, `7f4e045`, `683d91d`, `d0f3574`, `4cbc5f0`,
`159e552`, `2b8bb89`).  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence for every named
theorem (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`);
`interpretation` for every classical identification.  The library builds at **3,407
jobs**.

---

## 1. The headline

**`theWitness : LDatum 1` exists, and `theTwoSidedRankZeroInstance` holds: the
analytic rank and the algebraic rank of the congruent-number curve at one are both
zero, with every ingredient kernel-checked.**  The pose of the Birch–Swinnerton-Dyer
conjecture deposited earlier the same day was honest about being conditional on an
analytic datum; that datum is now constructed, so the rank correspondence has its
first fully formal two-sided instance: on the analytic side the central value is the
integral of the positive theta function; on the algebraic side the completed descent
leaves only the four half-turns.

## 2. The chain, by file

- **`HeckeTheta.lean`** (1,442 lines) — the theta function of `y² = x³ − x` built as
  a product of two mathlib Hurwitz kernels; **`theDuplicationIdentity`**
  (`sinKernel(1/4)(d)·evenKernel(1/2)(4d) = 16·oddKernel(1/4)(32d)·cosKernel(1/2)(8d)`,
  by pure lattice rearrangement — an involution kills the even part, the fold
  `(p,q) ↦ (p+q+1, p−q)` carries `(2p+1)² + (2q+1)² = 2((p+q+1)² + (p−q)²)`, and
  three lattice folds land on the `(4k+1, 2l)` grid); the weight-two functional
  equation `θ(1/x) = x²θ(x)`; the `StrongFEPair`; **`heckeLambda` entire with
  `Λ(2−s) = Λ(s)` and no continuation step**; positivity of every kernel factor (the
  duplication identity itself transfers the sign of `oddKernel` across the reflection,
  closing the dominance gap); **`theCentralValueDoesNotVanish`**; the norm-shell
  regrouping into **computable integer coefficients** whose stream
  `1, −2, −3, 6, 2, …` evaluates to the point counts; and the first coefficient laws.
- **`HeckeWitness.lean`** (400 lines) — `heckeL` entire; the completed-product chart;
  `L(1) = (2π/√32)·Λ(1) > 0`; **`theLFunctionAgreesWithItsDirichletSeries`** on
  `re s > 3` via `hasSum_mellin`, the conductor 32 cancelling the scale exactly; the
  witness; the two-sided instance.
- **`GaussCoefficient.lean`** (1,046 lines) — **Gauss's coefficient theorem**: for
  every prime `p ≡ 1 (mod 4)`, `heckeCoeff p = traceOfFrobenius p`.  The Jacobsthal
  engine: the square-count expansion, the complete quadratic sum, the double count
  `Σ_D jac(D)² = 2p(p−1)`, the ledger `jac(1)² + jac(r)² = 4p`, the mod-eight law
  `jac(1) ≡ −2` by a free Klein action (`x ↦ ±x, ±x⁻¹`), elementary
  Brahmagupta–Fibonacci uniqueness of the two-squares representation, and Euler's
  criterion for `χ(i)` aligning the signs in `p mod 8`.
- **`HeckeEuler.lean`** (950 lines) — the Euler structure through `ℤ[i]`: class
  rigidity under the four units; **`norm_gcd_eq` by Bézout alone** (no factorization
  theory: `gcd = zA + mB` and `z·z* = mn` make `gcd·gcd*` visibly `m`-divisible);
  the unique class factorization; **multiplicativity**; the inert and split
  prime-power recursions (inclusion–exclusion over the conjugate class primes); the
  unified Euler recursion at every odd prime.
- **`BirchSwinnertonDyer.lean`** — **the pose itself was convicted and repaired by
  the witness attempt**: demanding the naive product functional equation
  `completed(2−s) = w·completed(s)` at every `s` forces `L(2+m) = 0` through
  mathlib's junk `Γ`-value at the poles — a vanishing the true object refuses.  The
  datum now carries the entire `Λ` as its own field with the product formula as its
  lawful chart away from the poles, and the agreement half-plane is `re s > 3` (any
  half-plane pins the entire `L`; the classical `3/2` is the Hasse-bound refinement,
  named open).

## 3. What this closes and what remains

Closed, of the committed turn plan: turns 2–4 (the continuation constructed, the
witness returned, the pose unconditional at one) and turns 6–7 (central value
positive, the rank-zero instance closed on both sides).  Remaining, named:

| owed | content |
|---|---|
| turn 5 | the twisted theta at five (sign `−1`, quartic twist) — analytic order ≥ 1 at the first positive-rank instance; a fresh construction over mod-5 characteristics |
| the ledger clause at one | the exact evaluation `L(1) = Ω/8` (arithmetic–geometric mean / Chowla–Selberg territory) joining `theLedgerClauseHoldsAtOneGivenTheCentralValue` |
| the Hasse refinement | agreement on `3/2 < re s ≤ 3` needs `|c_m| = O(m^{1/2+ε})` |
| the wall | order-exactly-one at rank one is Gross–Zagier; finiteness of full Ш and everything at rank ≥ 2 is open mathematics for every actor |

## 4. Boundaries

"Hecke character", "CM", "conductor", "level", "Selmer" remain classical readings
carried as `interpretation`; the theorems are statements about mathlib kernels,
finsets of lattice points, and `ZMod`-character sums.  The two-sided instance is the
rank correspondence at one instance, not the conjecture; nothing about the
Birch–Swinnerton-Dyer conjecture is claimed as proved.
