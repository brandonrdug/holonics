# Landmarks and moduli

**Date:** 2026-08-20
**Kind:** the modulus law built, the gap theorems imported with their status, and the Möbius walk
measured on our own enumeration. No agents were used. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**No engine source is touched.**
**Truth status:** `proved-derived` for the modulus law; `proved-standard` for what is imported from
mathlib and restated; `open` for the named conjectures; `measured` for the walks.
**Cold-audit scope (2026-08-21):** the modulus, doubling, and point-count identities are exact
finite statements. Their Weil/Frobenius correspondence is `interpretation` on this genus-zero
family; no higher-genus Weil statement or named conjecture is proved here.
**Provenance.** Brandon's correction: an additive decomposition in a base is a **path** between
landmarks, the arrangement does not matter, and the modulus decides where you land. The prior
session had read it as a value decomposition and mis-applied the tautology rule.

---

## 0. The correction that occasioned this

`40 = 2⁴ + 3·2³` was graded a tautological receipt. That was the wrong reading. The object is a
**path in a base-`b` chart**, its arrangement is constrained by the partition it belongs to, and
what survives is the residue. That has exact classical statements, and one of them was already
proved in this repository.

## 1. The modulus law, proved

```lean
theorem theDepthAdmitsTheModulus (n p : ℕ) : n ∣ 2 ^ p - 1 ↔ ((2 : ZMod n) ^ p = 1)
theorem theLeastDepthIsTheOrderOfTwo (n p : ℕ) : orderOf (2 : ZMod n) ∣ p ↔ n ∣ 2 ^ p - 1
theorem theOppositeParityBranch (n p : ℕ) : ((2 : ZMod n) ^ p = -1) → orderOf (2 : ZMod n) ∣ 2 * p
theorem theLeastDepthTable   -- 3 first at depth 2, 5 at 4, 7 at 3, 9 at 6 — decided
```

**The least depth at which a modulus becomes reachable is the multiplicative order of two.** And
the moduli are exactly the ones the corpus's own sign-word family lands on: a period-`p` word with
minus-count parity `e` gives `2^p − (−1)^e`, with values `2cos(π m / (2^p ∓ 1))`. The verified
table — `−` → 3, `+−` → 5, `+−−` → 7, `++−` → 9 — is `2¹+1`, `2²+1`, `2³−1`, `2³+1`.

`crates/holonic-engine/src/winding_inertia.rs` isolates every one of those exactly by Sturm
bisection on the Dickson polynomial, and `niven_value` is the statement that the period-one words
are the only rational ones. **So the arithmetic law behind a standing organ is now stated and
proved, and the organ was built before the law was written down.**

## 2. Kummer and Bertrand, imported from mathlib and restated

```lean
theorem theMultiplicityIsTheCarryCount (hp : p.Prime) (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    (Nat.choose n k).factorization p
      = ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card
theorem theNextOctaveCarriesALandmark (n : ℕ) (hn : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n
```

**Kummer's theorem is the corrected reading as a theorem**: the multiplicity of a prime in a
binomial coefficient is *the number of carries*, so the digits do not enter and only the carry
count does. The counted condition in mathlib's `Nat.factorization_choose` **is** a carry at
position `i`. Instance decided: `3 + 3` is `11 + 11` in base two, carrying twice, and
`C(6,3) = 20 = 2²·5`.

## 3. The gap theorems, imported with their status and proved nowhere here

| named `Prop` | status |
|---|---|
| `LegendreConjecture` — a landmark between consecutive squares | **OPEN**, and **not implied by RH** |
| `CramerConjecture` — gap `≤ C(log p)²` | **OPEN**, far below what RH gives |
| `BakerHarmanPintz` — a landmark in `[x, x + x^0.525]` | theorem, imported |
| `RiemannGapBound` — gap `= O(√p log p)` | what RH buys, imported |
| `MertensSquareRootBound` — `M(x) = O(x^{1/2+ε})` | equivalent to RH, imported |
| `LucasCongruence` — the binomial factorizes over base-`p` digits | theorem; **mathlib does not carry it** |

Each is a real statement, not `True` wearing a name. **Legendre sitting outside RH's reach is the
structural point**: RH controls the oscillation of the average and not the extremes, and the gap
between `√x log x` and the conjectured `log²x` is where that shows.

## 4. The walks, measured on our own enumeration

Sieved to `2²⁰`, exact integer arithmetic:

| x | `M(x)` | `L(x)` | `√x` | `\|M\|/√x` | `\|L\|/√x` | π(x) | surplus | π(√x) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | −1 | −6 | 16 | 0.062 | 0.375 | 54 | 16 | 6 |
| 1,024 | −4 | −20 | 32 | 0.125 | 0.625 | 172 | 26 | 11 |
| 4,096 | −19 | −64 | 64 | 0.297 | **1.000** | 564 | **40** | 18 |
| 16,384 | −32 | −144 | 128 | 0.250 | 1.125 | 1,900 | 61 | 31 |
| 65,536 | 14 | −188 | 256 | 0.055 | 0.734 | 6,542 | 93 | 54 |
| 262,144 | 24 | −326 | 512 | 0.047 | 0.637 | 23,000 | 150 | 97 |
| 1,048,576 | 257 | −332 | 1,024 | 0.251 | 0.324 | 82,025 | 242 | 172 |

**The 4,096 row reproduces the 2026-07-28 experiment exactly** — π = 564, surplus = 40 — which is
the first independent check of that experiment's figures.

**The surplus's leading term is confirmed.** `surplus / π(√x)` falls `2.67 → 2.36 → 2.22 → 1.97 →
1.72 → 1.55 → 1.41`, converging toward one as the higher-order `π(x^{1/3})` terms lose weight
against `π(√x)`.

**And a control we did not go looking for.** `L(x)` is negative at every aperture we can reach.
That is Pólya's conjecture — **which is false**; Haselgrove refuted it, and the first sign change is
at `906,150,257`, three orders of magnitude above our largest aperture.

> **Our data would have confirmed a false law, and the aperture is the reason.** That is the
> project's own aperture doctrine arriving as an experimental fact on its own material: a
> measurement is evidence about the aperture before it is evidence about the subject. `|M(x)|/√x`
> stayed under `0.30` throughout, which is consistent with square-root cancellation and says nothing
> whatever about RH at this size.

## 5. Boundaries

`2²⁰` is far too small to bear on the Riemann Hypothesis and is stated here only as a reproduction
of the earlier experiment and as an aperture control. The modulus law is proved for the divisibility
criterion and the least-depth table; the full correspondence to the nested-radical values —
`2cos(π m / (2^p ∓ 1))` with the parity rule — is verified numerically to fifteen places on six
words and is **not** proved in Lean. Every named conjecture above is imported with its status. The
finite experiment does not decide one of them at this aperture; it advances the research program by
returning an exact aperture control, a counterexample to naive finite extrapolation, and a proved
period/modulus mechanism which later routes may compose. Nothing here claims a resolution of a
Millennium problem.

**Measured:** `Millennium/` is **21 files, 4,838 lines, 251 theorems**, zero `sorry`; the library
builds at 3,305 jobs; all ten theorems in `LandmarksAndModuli.lean` audit clean with six named open
`Prop`s beside them. The atlas stands at **181 equations, 166 relations**, no dangling endpoints.

---

## 6. The doubling map, proved, and where its moduli come from

`x ↦ x² − 2` on `[−2,2]` is conjugate under `x = 2cos θ` to `θ ↦ 2θ`, so a period-`p` sign word is a
periodic point of the doubling map. The gap flagged in §5 is closed:

```lean
noncomputable def dbl (k : ℕ) (x : ℝ) : ℝ := 2 * (T ℝ (2 ^ k : ℕ)).eval (x / 2)

theorem theDoublingDoublesTheAngle (k : ℕ) (θ : ℝ) :
    dbl k (2 * Real.cos θ) = 2 * Real.cos ((2 ^ k : ℕ) * θ)
theorem theSplitFamilyIsFixed (k m : ℕ) (h : (2:ℝ) ^ k - 1 ≠ 0) :
    Real.cos ((2 ^ k : ℕ) * (2 * π * m / ((2:ℝ) ^ k - 1))) = Real.cos (2 * π * m / ((2:ℝ) ^ k - 1))
theorem theTwistedFamilyIsFixed (k m : ℕ) (h : (2:ℝ) ^ k + 1 ≠ 0) :
    Real.cos ((2 ^ k : ℕ) * (2 * π * m / ((2:ℝ) ^ k + 1))) = Real.cos (2 * π * m / ((2:ℝ) ^ k + 1))
```

> **The two moduli are the two ways `cos A = cos B` can hold.** Either the angle advances by whole
> turns — `2^k θ = θ + 2πm`, giving `2^k − 1` — or it advances to the **reflection**,
> `2^k θ = 2πm − θ`, giving `2^k + 1`. The minus-count parity of the word selects the branch, and
> the reflection is the swing.

The angle-doubling half comes from mathlib's `Polynomial.Chebyshev.T_real_cos`; the reflection half
from `Real.cos_nat_mul_two_pi_sub`.

## 7. Where the moduli come from arithmetically

Periodic points of the `p`-fold doubling are the elements fixed by `Frobenius^p`, i.e.
`μ_{2^p−1} = F_{2^p}^×`, and `2cos` is the trace to the real subfield. So the moduli are point
counts:

```
2^p − 1 = #𝔾ₘ(F_{2^p})   →  1, 3, 7, 15, 31, 63
2^p + 1 = #P¹(F_{2^p})   →  3, 5, 9, 17, 33, 65
```

The radical family's `3, 5, 7, 9` is that column. `theSplitModulusIsTheUnitCount` takes the first
from mathlib's `Fintype.card_units`; `theModuliArePointCountsOfGenusZero` decides the table.

**And the family sits at the degenerate end of the Weil statement.** For a curve of genus `g` over
`F_q`,

```
#X(F_{q^p}) = q^p + 1 − Σ αᵢ^p        with 2g terms, |αᵢ| = √q
```

Here the correction term is `∓1` — `|α| = 1`, not `√q` — and `Z_{P¹}(t) = 1/((1−t)(1−qt))` has
numerator `1`, so there are no `αᵢ` at all. `theCorrectionTermIsAUnitOnThisFamily` records it.

> **The whole content of the Weil bound is the size of the term this family has set to a sign.**
> `2^p − (−1)^e` is the genus-zero case; what a higher-genus curve puts in place of `∓1` is the
> theorem. Nothing on this family bears on that, and the identity is deposited so the correspondence
> is not later read as carrying content it does not have.

**Measured after:** `Millennium/` is **21 files, 4,921 lines, 257 theorems**, zero `sorry`; the
library builds at 3,307 jobs; all sixteen theorems in `LandmarksAndModuli.lean` audit clean beside
seven named open `Prop`s. The atlas stands at **183 equations, 168 relations**, no dangling
endpoints.
