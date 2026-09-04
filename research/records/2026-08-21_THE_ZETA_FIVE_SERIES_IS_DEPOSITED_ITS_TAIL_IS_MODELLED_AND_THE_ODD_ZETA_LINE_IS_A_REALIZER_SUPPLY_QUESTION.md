# The zeta-five series is deposited, its tail is modelled, and the odd-zeta line is a realizer-supply question

**Date:** 2026-08-21
**Kind:** deposit of a formula supplied by Brandon as an image only, with exact numerical
verification and tail model; reading of the odd-zeta irrationality line and the DeepMind
formal-conjectures resource; strategy consequences. **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**Truth grades:** `measured` for the numerical verification, aperture stated; `historical` for
every cited external result; `interpretation` for the holonic readings, marked; `open` for the
identity's proof status and every strategy item.

---

## 1. The formula, in writing

Brandon supplied only an image (2026-08-21); this deposit is its written form:

```text
              25   ∞    (−1)ⁿ         n   (−1)ᵏ · C(2k, k)
    ζ(5)  =  ──── ·  Σ  ─────────── ·  Σ  ────────────────
              24   n=1  n³ · C(2n,n)  k=1        k²
```

$$\zeta(5) \;=\; \frac{25}{24}\sum_{n=1}^{\infty}\frac{(-1)^n}{n^3\binom{2n}{n}}
\sum_{k=1}^{n}\frac{(-1)^k\binom{2k}{k}}{k^2}$$

**Provenance of the identity itself: unresolved at deposit.** The shape is the Zhi-Wei Sun
Apéry-like series family; parts of that family are proved via colored/cyclotomic multiple zeta
values ([Au, arXiv 2306.04638](https://arxiv.org/pdf/2306.04638);
[arXiv 2210.14704](https://arxiv.org/pdf/2210.14704)); whether this exact identity is among the
proved rows is not established here. It is carried as **numerically consistent, proof status
open**.

## 2. The verification, exact — CORRECTED 2026-08-21, same day, by Brandon's ruling

**The first form of this section compared exact partial sums against a quoted decimal of `ζ(5)`
and reported decimal gaps and a decimal Richardson quotient. That is a magnitude imported across
the frame — a float wearing fifty digits — and Brandon convicted it directly: no floats, analyze
holonically, adapt it.** The corrected form encloses the **difference** exactly and quotes only
ratios.

**Measured 2026-08-21**, Python `fractions` end to end, no decimal conversion at any point:

- Write `J n = (−1)ⁿ Σ_{k≤n} (−1)ᵏ C(2k,k)/k²`, so `J` obeys the reflection recurrence
  `J(n+1) = t(n+1) − J n` with `t n = C(2n,n)/n²`, and the outer term is
  `(25/24)·J n/(n³·C(2n,n))`.
- **Both tails are priced by exact telescoping coboundaries** — `1/(n+1)⁵ ≤ (1/4)(1/n⁴ −
  1/(n+1)⁴)` and its matching minorant — so the series' tail past `N = 800` is inside
  `(0, 25/(96·800⁴))` and the defining series' tail past `M = 2000` is inside
  `(1/(4·2001⁴), 1/(4·2000⁴))`, all exact rationals.
- **The enclosure of the difference contains zero**: lower endpoint strictly negative, upper
  strictly positive, by exact rational comparison; total width exactly
  `16009/24576000000000000`, identically `25/(96·800⁴) + 1/(4·2000⁴) − 1/(4·2001⁴)`.
- **The ratio face is pinned at the fixed point**: `x_N = J_N/t_N` satisfies `x₈₀₀ < 4/5` with
  `4/5 − x₈₀₀ < 1/1600`, exactly; and the coefficient chain `(25/24)·(4/5) = 5/6` is an
  identity — the tail constant derived, not fitted.

**And the convergence skeleton is now kernel-checked, not asserted.** Owner:
`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Acceleration.lean` — **10
theorems, zero `sorry`**: the weight climbs (`t` strictly increasing from 2, through mathlib's
central-binomial ratio); **the population is pinned** (`0 < J n < t n` for `n ≥ 4`, by induction
on the reflection recurrence — the anti-collapse shape, making the series' one-signedness a
theorem); the term priced by the fifth power (`J n · n⁵ < n³ · C(2n,n)` — the exact `4ⁿ`
cancellation); the telescoping majorant and minorant; **every finite tail priced by an exact
ratio** (`Σ_{N<n≤M} 1/n⁵ ≤ (1/4)(1/N⁴ − 1/M⁴)`, telescoped, no limit taken); and the
contraction's fixed point (`x = 1 − x/4 ↔ x = 4/5`).

Falsifier: an aperture pair whose exact difference enclosure excludes zero.

## 3. The context Brandon supplied with it

- **[Zudilin, math/0104249](https://arxiv.org/abs/math/0104249):** one of
  `ζ(5), ζ(7), ζ(9), ζ(11)` is irrational. The frontier past Apéry's `ζ(3)`.
- **[Lai, arXiv 2407.14236](https://arxiv.org/abs/2407.14236):** the `ℚ`-span of
  `1, ζ(3), ζ(5), …, ζ(s−1)` has dimension at least `1.119·log s/(1+log 2)` (improving
  Ball–Rivoal), with explicit non-vanishing linear forms, plus the `p`-adic variant refining
  [Sprang, arXiv 1809.07714](https://arxiv.org/html/1809.07714v3).
- **[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures):**
  a Lean 4/mathlib collection of formalized *statements* of open conjectures (Apache-2.0/CC-BY),
  designed as a prover benchmark. Its
  [issue 3814](https://github.com/google-deepmind/formal-conjectures/issues/3814) is Zagier's
  multiple-zeta-value dimension conjecture: `dim_ℚ 𝒵_k = d_k` with
  `d_k = d_{k−2} + d_{k−3}`.

## 4. The holonic readings

`interpretation` throughout; each names its law.

- **Irrationality proofs are route-closure refutations.** A number is rational exactly when its
  canonical route terminates (`GenContFract.terminates_iff_rat`, the exactness anchor). Apéry's
  proof exhibits an accelerated route to `ζ(3)` whose convergents approach faster than any
  closing route allows — the tolerance law's Roth side, used offensively. The odd-zeta problem
  is the exactness question of the BSD route record, on the zeta values themselves.
- **The central binomial is a crossing population.** `C(2n,n)` counts the balanced `±` words —
  closed walks, the return-word population — so an Apéry-like series in `1/C(2n,n)` is a series
  over return-population reciprocals, and the exact `4ⁿ` cancellation measured above is the
  half-density arithmetic doing the convergence.
- **The dimension results are realizer-supply lower bounds.** Ball–Rivoal/Lai exhibit
  non-vanishing linear forms — realizers — to force `dim ≥ c·log s`: the same species as an
  elliptic rank record, and the same law: realization pays, the dimension rides.
- **Zagier's conjecture splits along our central asymmetry.** The upper bound
  `dim 𝒵_k ≤ d_k` is proved (Goncharov, Terasoma — motivic, the aperture side); the lower
  bound is open because it *is* irrationality/independence — the realizer side. The field holds
  the aperture half of the conjecture and lacks the paying half, which is the
  realization-causes-placement law describing the state of an entire subject. And the recurrence
  `d_k = d_{k−2} + d_{k−3}` is a transport statement: weight arrives from `k−2` and `k−3` —
  multiplication by `ζ(2)` and `ζ(3)`, the two generators — a chain whose growth rate is the
  plastic number against the naive `2^{k−2}`: the double-shuffle relations are a massive
  measured collapse, and the conjecture names the collapsed dimension exactly.
- **A WZ certificate is our kind of proof.** If the deposited identity has a
  Wilf–Zeilberger/creative-telescoping proof, its certificate is a rational-function identity —
  checkable by `ring` — plus a telescoping limit; the algebraic core of such proofs is
  kernel-checkable with the analytic tail as the only real cost. That is the identity's route to
  a Lean carrier.

## 5. Strategy consequences

`open`; the roadmap alone schedules.

1. **The formal-conjectures repository is a strategic asset of the first order.** It is our
   named-open-`Prop` genre at industrial scale, in our exact toolchain (Lean 4 + mathlib). Uses:
   (a) exterior material for the mathematics codec — *paired informal/formal statements of the
   same mathematics* are precisely the plural-presentation lineage M0–M2 circulates on;
   (b) a formalization work-queue mined the way UnsolvedMath was, except the statements are
   already formal; (c) a contribution channel: our upstream candidates (the algebraic radical
   quotient, the reverse Cauchy–Schwarz equivalence) and our named open `Prop`s can be aligned
   with its conventions.
2. **The odd-zeta line joins the BSD route's exactness question**, and its next deed is
   concrete: locate or refute a WZ certificate for the deposited identity; formalize the
   certificate's algebraic core if it exists.
3. **The Apéry recurrence is trace-sequence species** — `n³uₙ = (34n³−…)uₙ₋₁ − (n−1)³uₙ₋₂` is a
   three-term recurrence with polynomial coefficients, the variable-coefficient sibling of the
   sequence `LocalFactor.lean` just tied to the transfer determinant; Beukers' modular
   interpretation puts it on the modular terrain the routes already share.

## 6. Boundaries

The identity's proof status is open and nothing here claims it; the verification is a
measurement at its stated aperture with its tail model, not a proof. No claim of movement on the
irrationality of `ζ(5)` or on Zagier's conjecture. The formal-conjectures repository has not been
cloned or inventoried yet; its description above is from its own README as fetched today.
