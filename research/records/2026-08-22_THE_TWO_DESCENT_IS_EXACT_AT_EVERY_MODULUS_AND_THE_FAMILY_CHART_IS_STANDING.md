# The two-descent is exact at every modulus, and the family chart is standing

**Date:** 2026-08-22
**Kind:** the family-chart return of the coarse-graining ladder — under Brandon's goal
*"Solve the Birch Swinnerton-Dyer Conjecture by the standards of its Millennium
statement."*  Solo orchestrator work, commits `d525724`, `08082ba`, `a018094`,
`93457f6`, `c3796c1`, `f679ac5`, one day.  **It schedules nothing.**
**Truth grades:** `proved-derived` with `formal-checked` evidence
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`) throughout.

---

## 1. The headline

**`theTwoDescentIsExactAtEveryModulus`** — on every congruent-number curve
`y² = x³ − n²x` with `n > 0`, a rational point has both descent slots in the trivial
square class **exactly when it is a double**: `ker(face) = 2·E_n(ℚ)`, family-wise,
kernel-checked.  The five-instance exactness that carried the rank computation is now
one reading of a family law.

## 2. The family chart's standing inventory, after one day

| law | owner | status |
|---|---|---|
| the split-chart rotation (Gauss eigenidentity) | `FamilyGauss` | every odd modulus |
| the eigenvalue `g(χ)² = p` on split residues | `FamilyGauss` | every `p ≡ 1 (mod 4)` |
| duplication grows quartically, cancellation `∣ 16n⁶` | `FamilyHeight` | every modulus |
| translation grows quadratically, `L = α + n²β` | `FamilyHeight` | every modulus |
| the halving certificates (curve, square, ordinate) | `FamilyHalving` | every modulus |
| the face slots with vanishing conventions | `FamilyKernel` | every modulus |
| kernel ⊆ doubles (point-level, group law) | `FamilyKernel` | every `n > 0` |
| doubles ⊆ kernel (point-level, group law) | `FamilyImage` | every `n > 0` |
| the chord-landing laws | `FaceHomomorphism` | already generic |
| the doubling-chart mean step (Landen/AGM) | `LandenLattice` | every scale |

Every family certificate was verified symbolically before formalization (residual
zero), and each specializes to its five-instance form at `n = 5` — the instance
certificates were compressed shadows of family ones, which is the coarse-graining
correction paying out as construction, not doctrine.

## 3. What remains open on the family chart, named

1. **The family face homomorphism at point level** — the chord-landing laws are
   generic; their assembly into `SqCls(slot(P+Q)) ~ slot(P)·slot(Q)` over
   `FamilyFace.E n` is a port of the five-assembly with the family slots.
2. **The family theta functional equation** — the fold machinery of `FiveTheta`
   assembled over the standing family engine, with the sign law on residues mod 8.
3. **The per-twist face image** — the one genuinely twist-varying computation (the
   2-Selmer group); the family machinery makes each instance a uniform certified
   computation.
4. **The rank-zero ledger at one** — the AGM convergence from the mean step to the
   lemniscatic period, `L(1) = Ω/8`.
5. **The tower** — the norm relation at one prime step, the microscopic cell of the
   Euler system that closes analytic rank ≤ 1 for the whole CM family.

## 4. The ladder position against the Millennium statement

Rung 1 (instances, both ranks) closed.  Rung 2 (the family chart): the descent side's
exactness and both growth laws are now family law; the analytic engine is family law;
the remaining rung-2 items are the two assemblies and the per-twist computation.
Rungs 3–5 stand as laddered in the coarse-graining record, each with its microscopic
cell named.  The Millennium statement's universal quantifier is approached the only
way this framework approaches a global: by exact coarse graining with certified
remainder at every step — and the day's measurement is that the descent's entire
mechanism coarse-grains with zero remainder.
