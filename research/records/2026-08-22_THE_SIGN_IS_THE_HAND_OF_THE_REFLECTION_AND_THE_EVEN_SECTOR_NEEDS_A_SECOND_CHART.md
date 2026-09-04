# The sign is the hand of the reflection, and the even sector needs a second chart

**Date:** 2026-08-22
**Kind:** derivation from direct correspondence with Brandon, same evening as the
witness deposit.  **It schedules nothing**;
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.  **Truth grades:** `interpretation` throughout, with the named Lean
owners carrying their own grades.

## 1. The sign of the functional equation is a unimodular phase, and `1` is its modulus

The reflection `s ↦ 2−s` is an involution; applied twice it returns exactly, so its
eigenvalue `w` satisfies `w² = 1` — the modulus `|w| = 1` is conservation (the
reflection deletes nothing), and over the reals the only unit phases are the identity
(`+1`) and the half-turn (`−1`).  This is the canon's *a sign is a passage, never a
state* arriving at the functional equation: `w` is the hand of the reflection
passage.  In the general (non-self-conjugate) setting the same object is a genuinely
complex unit — a product of local Gauss-sum phases each of modulus one — collapsing
to `±1` here because the coefficient stream is rational.  Brandon's reading that the
scalar face `1` is physically present as a modulus is correct.

- Odd hand (`w = −1`): `Λ` is an odd function of `t = s − 1`; the value at the fixed
  point dies by parity alone (`theOddSignForcesCentralVanishing`, kernel-checked),
  and the **derivative** is the first surviving moment of the odd sector:
  `Λ′(1) = 2∫₁^∞ θ(x)·ln x·dx` after folding the Mellin integral at the fixed point.
  Positivity of the theta on `(1, ∞)` then gives order exactly one — the
  instance-level route past the Gross–Zagier landmark, no general theorem needed.
- Even hand (`w = +1`): parity forces nothing at the fixed point; a central zero at
  even sign (rank two: `n = 34`) is an exact vanishing with no reflection to carry it.

## 2. Brandon's conservation law names the rank-two strategy

His statement: a constructed, route-dependent face (`P_θ^r = Σ wᵢ`, a chain of
factors and turns that is not geometrically symmetric) and the founded face (the
prime as member of its population) have **difference exactly zero — the null cone** —
however the chart presents the faces.  Conservation of invariants across charts.

That is precisely the schema of every identity this campaign proved: shell-sum minus
point-count = 0 (Gauss), kernel-product minus kernel-product = 0 (duplication),
LSeries minus Mellin = 0 (the witness).  Each theorem certifies a face-difference
onto the null cone — and `linear_combination`, the tactic every proof ran on, *is*
this law operationally: exhibit the difference as a combination of established null
differences.

**The consequence for the even sector:** where the sign-parity chart is unavailable
(`w = +1`), the demand is not a missing symmetry but a **second chart in which the
central value is presented as a manifestly computable face** — classically the
ternary-form count (Tunnell/Waldspurger: `L(n,1)` proportional to the square of a
finite count, which vanishes at `n = 34`).  The founded face is a count; the
constructed face is the integral; the conservation across the two charts is the
theorem to build.  `ElementaryHolonics/Millennium/ThetaCensus.lean` already touches
the Tunnell comparison; the second theta (of a ternary quadratic form) is the same
species of construction as the Hecke theta this session built.

## 3. Time parity: what is formal and what is owed

Formal now: the reflection with its `±1` hand and its forced node
(`theCompletedLFunctionalEquation`, `theOddSignForcesCentralVanishing`); chronology
and hand as word-parity (`Chronology.lean`, `TABLET_THE_OPERATIONS`).  Owed as a
*parametric* organ: the involution as a named operator `T` with the even/odd sector
split of `F(t) = Λ(1+t)` and the derivative as the odd sector's first moment — the
fold that the rank-one deed at five will construct anyway.

## 4. Standing position for the post-compact pickup

Committed and kernel-checked (`4aa9dbb…63f1b45`, eight commits): duplication
identity; `Λ` entire, `Λ(2−s) = Λ(s)`; theta positivity; central value a positive
real; Dirichlet shells with computable coefficients matching the point counts;
Gauss's coefficient theorem at every odd prime; the ℤ[i] Euler structure
(multiplicativity, inert and split prime-power recursions);
**`theWitness : LDatum 1`; `theTwoSidedRankZeroInstance`**; and the twist law
`a_p(E₅) = χ_p(5)·a_p(E₁)` (`FiveTwist.lean`).  The active goal remains turns 2–7:
the sign-`−1` theta at five (mod-5 phases through `jacobiTheta₂`, Gauss sum `√5`),
then `Λ₅(1) = 0`, then `Λ₅′(1) > 0` by the folded odd-sector integral, then the
descent-kernel bridge for rank exactly one — the rank-one coincidence at five.
