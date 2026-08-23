# The algebraic rank is effectively bounded at every modulus, and the rank side is a finite quantity family-wise

**Date:** 2026-08-22
**Kind:** the family rank endgame — under Brandon's goal to solve the
Birch–Swinnerton-Dyer conjecture by its Millennium statement.  Solo orchestrator
work, commits `9e388f5`, `c858f6f`, completing the day's family arc.
**It schedules nothing.**
**Truth grades:** `proved-derived` with `formal-checked` evidence
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`).

---

## 1. The headline

**`theAlgebraicRankIsBoundedAtEveryModulus`** — on every congruent-number curve
`y² = x³ − n²x` with `n ≥ 1`, no `(4n+1)²` rational points are independent modulo
torsion.  The posed conjecture's algebraic rank is therefore a **finite,
effectively bounded** quantity at every modulus, in one kernel-checked theorem with
the modulus universally quantified.

## 2. The assembly

- **The class pigeonhole** (`theClassesCollideAtEveryModulus`): any family of more
  than `(4n+1)²` points contains two differing by a double — the face image lives in
  the `(4n+1)²`-cell class box, the face is a homomorphism, the kernel is the
  doubles.
- **The torsion trio** (`theTorsionTrioDoesNotCollideAtEveryModulus`): `0`, `(0,0)`,
  `(n,0)` pairwise avoid the doubles at every modulus, with refusals uniform in the
  modulus — the signs of `−n²` and `−n³`, and two not a rational square against
  `2n²`.  (The five-instance trio used the non-squareness of five; at square moduli
  that fails, so the family refusal reroutes through `2n²` — one more instance datum
  revealed as a shadow.)
- **The endgame**: family Mordell–Weil admits the structure theorem `ℤᵐ × T`;
  independence modulo torsion transports to ℚ-linear independence of the free parts
  through the fraction-ring bridge, forcing `m ≥ (4n+1)²`; the single-coordinate
  free directions crossed with the trio give `3(4n+1)²` pairwise non-colliding
  points against the `(4n+1)²` ceiling — contradiction.

## 3. The family chart's algebraic side, complete inventory

Exactness (`ker(face) = 2E`, both directions), the face homomorphism, both height
growth laws, the halving certificates, discriminant support, Mordell–Weil finite
generation, the collision bound, the torsion trio, and now the effective rank bound
— **every theorem with `n` universally quantified, none mentioning an instance.**
The rank clause's algebraic half is family-wise machinery; what decides the exact
rank per twist is the per-twist face image (the 2-Selmer computation), now a
uniform certified computation inside a proven-finite box.

## 4. The ladder position

Rung 2's algebraic side: **closed**.  Remaining: the family theta functional
equation (analytic side; engine standing), the AGM to the lemniscatic period
(`L(1) = Ω/8`, the rank-zero ledger), the tower's first norm relation (rung 3,
where analytic rank ≤ 1 closes for the whole CM family by growth), and the
universality transport (rung 4, modularity, all curves over ℚ).  The Millennium
statement's universal quantifier continues to be approached the only way this
framework approaches a global: exact coarse graining, with today's measurement
that the entire rank machinery coarse-grains with zero remainder.
