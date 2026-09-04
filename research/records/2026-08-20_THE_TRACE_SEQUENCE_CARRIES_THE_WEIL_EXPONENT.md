# The trace sequence carries the Weil exponent

**Date:** 2026-08-20
**Kind:** the genus-one continuation of the doubling family, the general splitting law, and the gap
measurement. No agents were used. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**No engine source is touched.**
**Truth status:** `proved-derived` for the Lean; `measured` for the gap data.

**Cold-audit scope note (2026-08-21):** the exact Lean objects here are integer recurrences,
complex roots, and finite matrix identities. References to Weil, statistical mechanics, softmax,
Lee–Yang, phase transitions, and the Riemann line are `proved-standard` only where explicitly
imported, otherwise `interpretation`; none is a new proof of a named conjecture.

---

## 0. One recurrence carries the whole bound

```text
t₀ = 2,   t₁ = a,   t_{p+2} = a·t_{p+1} − q·t_p
```

```lean
theorem theRootHasSquaredModulusQ (a q : ℤ) (h : (a:ℝ)^2 ≤ 4*(q:ℝ)) :
    Complex.normSq (alpha a q) = (q : ℝ)
theorem theRootIsCharacteristic (a q : ℤ) (h) : alpha a q * alpha a q = a * alpha a q - q
theorem theTraceIsTwiceTheRealPart (a q : ℤ) (h) (p : ℕ) :
    ((trace a q p : ℤ) : ℝ) = 2 * ((alpha a q) ^ p).re
theorem theLevelOneBoundGivesEveryLevel (a q : ℤ) (h) (p : ℕ) :
    ((trace a q p : ℤ) : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ p
```

> **The level-one hypothesis `a² ≤ 4q` is the entire input. Every higher level is free**, and the
> only analytic fact used is `Re(z)² ≤ |z|²`.

## 1. The genus-zero family is the same recurrence at `q = 1`

```lean
theorem theGenusZeroFamilyIsTheRecurrenceAtOne :
    (trace 2 1 p = 2 …) ∧ (trace (-2) 1 p = 2(-1)^p …) ∧ (trace 0 1 p = 2,0,-2,0 …)
```

`a = 2` gives the constant `2`; `a = −2` gives `2(−1)^p`. **Those are the `∓1` corrections the
moduli `2^p ∓ 1` carry.** So the sign-word family and the elliptic trace sequences are one
recurrence at different `q`, and **the Weil exponent is `q`'s square root**: `|α| = 1` at `q = 1`
against `|α| = √2` at `q = 2`. The doubling family's degeneration is a value of `q`, not a different
construction.

## 2. Over the binary field the bound is forced by integrality

```lean
theorem theHasseIntervalAtTwoIsStrict (a : ℤ) (h : a ^ 2 ≤ 8) : a ^ 2 ≤ 4
```

Hasse allows `|a| ≤ 2√2 ≈ 2.828`; an integer trace therefore has `a² ≤ 4 < 8 = 4q`, **strictly**.
No elliptic curve over `F₂` sits on the boundary, and the reason is that `2√2` is irrational. The
five admissible traces and their sequences to depth four are decided in
`theFiveTracesOverTheBinaryField`.

## 3. The dichotomy, with the control

```lean
theorem theOvershootProducesARealRootBeyondTheCircle (a q : ℝ) (h : 4 * q < a ^ 2) (ha : 0 < a) :
    ∃ x : ℝ, x ^ 2 - a * x + q = 0 ∧ q < x ^ 2
```

Past the bound the characteristic polynomial acquires a real root whose square exceeds `q`, so the
trace escapes `2q^{p/2}`. **`cos` becomes `cosh`; the circle becomes a hyperbola.** That makes the
level-one hypothesis load-bearing rather than decorative — dropping it produces the escaping root
explicitly.

## 4. The splitting law, now general

```lean
theorem theSelfPairingKillsTheQuotient (q : LinearMap.BilinForm R V) (om x : V) :
    ∃ (c : R) (w : V), q om w = 0 ∧ q om om • x = c • om + w
```

Every class lands in the span of the distinguished class and its perp after multiplying by the
self-pairing, so `L / (ℤω ⊕ ω^⊥)` is annihilated by `q(ω,ω)`. The factor-4 witness was the
instance; this is the law, and it closes the limit named in the shadows record.

## 5. The gaps, measured to `2²⁴`

| quantity | value |
|---|---|
| maximal gap | **154**, after `p = 4,652,353` |
| record gaps | 86, 96, 112, 114, 118, 132, 148, 154 |
| `max g/log²p` (`p ≥ 100`) | **0.7026** at `p = 2,010,733` |
| `max g/(√p·log p)` (`p ≥ 1000`) | **0.1298** at `p = 1,327`, down from `0.2786` at `p = 113` |

**The two scales separate visibly.** The Cramér ratio sits around `0.70` and does not fall; the
ratio against what RH would deliver **shrinks by more than half across the range**. That is the
structural point recorded earlier as prose, now as data on our own sieve: RH's `√p log p` is
enormously loose against observed gaps, and `log²p` is the scale the data actually tracks.

## 6. Boundaries

The Weil conjectures are theorems and are not reproved here; what is proved is the recurrence's own
dichotomy and the propagation of the level-one bound. Nothing here touches genus above one, and no
curve, divisor or L-function appears — the object is an integer recurrence with a complex
characteristic root. `2²⁴` bears on nothing but the aperture.

**Measured:** `Millennium/` is **22 files, 5,095 lines, 267 theorems**, zero `sorry`; the library
builds at 3,308 jobs; all ten new theorems audit clean. The atlas stands at **188 equations, 171
relations**, no dangling endpoints.

---

## 7. The two gap scales, in exact charts

```text
√p · log p = log(p^{√p})        (log p)² = log(p^{log p})
```

Both are logarithms of a tower, and `log²p ≪ √p log p` is just `log p ≪ √p` in the exponent. **The
two exponents decompose exactly in disjoint charts.**

### The Riemann scale is Diophantine and alternating

```lean
theorem theConvergentDeterminantAlternates (n : ℕ) :
    hh a (n + 1) * kk a n - hh a n * kk a (n + 1) = (-1) ^ n
theorem theConvergentDifferenceIsAnAlternatingUnitFraction (n) (h0) (h1) :
    (hh a (n+1) : ℚ)/(kk a (n+1)) - (hh a n)/(kk a n) = (-1)^n / ((kk a n) * (kk a (n+1)))
```

The determinant identity is an integer induction with no analysis. So consecutive convergents differ
by an **alternating unit fraction whose modulus is the product of consecutive denominators**, and
telescoping gives the tower as an exact product of rational powers:

```text
p^{√p} = p^{h₀/k₀} · ∏ₙ p^{(−1)ⁿ /(kₙ kₙ₊₁)}
```

Computed exactly, no floats:

```text
√2 = 1 + 1/2 − 1/10 + 1/60 − 1/348 + 1/2030 − 1/11830 + …
2^{√2} = 2 · 2^{1/2} · 2^{−1/10} · 2^{1/60} · 2^{−1/348} · 2^{1/2030} · …
   determinants  1, −1, 1, −1, 1, −1        moduli  2, 10, 60, 348, 2030, 11830
√3 :  1 + 1 − 1/3 + 1/12 − 1/44 + 1/165 − 1/615    moduli  1, 3, 12, 44, 165, 615
√5 :  2 + 1/4 − 1/68 + 1/1224 − 1/21960 + …        moduli  4, 68, 1224, 21960, 394060
√7 :  2 + 1 − 1/2 + 1/6 − 1/42 + 1/238 − 1/527     moduli  1, 2, 6, 42, 238, 527
```

### The Cramér scale is arithmetic and carries no irrationality

```lean
noncomputable def vonMangoldtTwo : ArithmeticFunction ℝ := (↑μ) * logSq
theorem theDivisorSumOfTheSecondIsTheLogSquared (n : ℕ) :
    ∑ d ∈ n.divisors, vonMangoldtTwo d = (Real.log n) ^ 2
```

The logarithm decomposes over the divisor lattice — mathlib's `vonMangoldt_sum`,
`Σ_{d|n} Λ(d) = log n` — and its square has the same shape one order up, `Λ₂ = μ ∗ log²`. Selberg's
identity `Λ₂ = Λ·log + Λ∗Λ` is a further fact and is not proved here.

> **The Cramér scale decomposes over divisors; the Riemann scale over convergents.** One is a sum
> over the multiplicative structure of `p`; the other is an alternating sum with growing moduli that
> knows nothing about factorization. That is the chart-level reason the two ratios measured in
> section 5 separate.

**Measured after:** `Millennium/` is **23 files, 5,226 lines, 270 theorems**, zero `sorry`; the
library builds at 3,310 jobs. The atlas stands at **191 equations, 173 relations**, no dangling
endpoints.

---

## 8. Softmax, and where the phase transition is

Softmax has a Gibbs interpretation **after** energies and an inverse-temperature parameter are
declared: `p_i = e^{−βE_i}/Z`; only the two-state case is the sigmoid. For a specified finite chain
whose weights factor through a transfer matrix, the partition function is a transfer-matrix trace,
and at size two that trace obeys the recurrence this record is about. This does not identify a
generic neural softmax or attention map with a physical Gibbs system:

```lean
theorem theFiniteTransferTraceObeysItsRecurrence (T : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    Matrix.trace (T ^ (n + 2))
      = (Matrix.trace T) * Matrix.trace (T ^ (n + 1)) - (Matrix.det T) * Matrix.trace (T ^ n)
theorem theBaseCasesMatch (T) : Matrix.trace (T ^ 0) = 2 ∧ Matrix.trace (T ^ 1) = Matrix.trace T
```

By Cayley–Hamilton, computed rather than cited. **So `a = tr T` and `q = det T`:**

```text
statistical mechanics   Z_N = Tr(Tᴺ)      = λ₁ᴺ + λ₂ᴺ
Frobenius               #X(F_{qᴺ}) = qᴺ+1 − (α₁ᴺ + α₂ᴺ)
```

**The dichotomy is a spectral gap.** `a² > 4q` gives real roots with `|λ₁| > |λ₂|`: one eigenvalue
dominates, the correlation length `1/log|λ₁/λ₂|` is finite, the chain is ordered. `a² < 4q` gives
conjugate roots of equal modulus: the gap in modulus is **zero** and the correlation length is
infinite.

> **`interpretation` for this two-root recurrence:** the Weil-shaped condition `|α| = √q` is an
> equal-modulus (zero-modulus-gap) condition, so no root dominates. It is not a general equivalence
> between the Weil bound and a thermodynamic critical point.

And the boundary is the swing's fixed locus:

```lean
theorem theZeroDiscriminantQuadraticHasTheRepeatedRoot (a q : ℝ) (h : a ^ 2 = 4 * q) (x : ℝ)
    (hx : x ^ 2 - a * x + q = 0) : x = a / 2
```

At `a² = 4q` the two roots merge — the fixed locus of the involution that exchanges them, with the
same algebraic shape as `Re s = 1/2` being `Fix(s ↦ 1 − s̄)`. **`Interpretation`:** this is a
fixed-locus analogy, not a thermodynamic criticality theorem.

**No thermodynamic limit is taken.** A finite transfer matrix has analytic `log Z` and therefore no
phase transition; what the discriminant crossing changes is the **chart** — `cos` for `cosh` — not
the analyticity. The genuine transition needs `N → ∞` and the accumulation of the zeros of `Z_N` on
the real axis, which is not built here.

**Measured after:** `Millennium/` is **24 files, 5,316 lines, 275 theorems**, zero `sorry`; the
library builds at 3,311 jobs. The atlas stands at **194 equations, 176 relations**, no dangling
endpoints.

## 9. One involution, three fixed-locus equations

```lean
theorem theCriticalLineIsAFixedLocus (s : ℂ) : s.re = 1 / 2 ↔ s = 1 - (starRingEnd ℂ) s
theorem theWeilCircleIsAFixedLocus (q : ℝ) (al : ℂ) (hal : al ≠ 0) :
    Complex.normSq al = q ↔ al = (q : ℂ) / (starRingEnd ℂ) al
theorem theComplementaryPowersMultiplyToTheBase (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s * (q : ℂ) ^ (1 - s) = (q : ℂ)
```

| statement | locus | involution | status |
|---|---|---|---|
| Lee–Yang | `\|z\| = 1` | `z ↦ 1/z̄` | degree-two algebraic theorem here; general positivity theorem is imported |
| Weil | `\|α\| = √q` | `α ↦ q/ᾱ` | algebraic fixed-locus identity here; ample/Rosati theorem is imported |
| Riemann | `Re s = ½` | `s ↦ 1 − s̄` | open |

**The first two displayed equivalences are proved for the declared complex variables, and the third
is an algebraic chart identity** — `q^s · q^{1−s} = q` under the stated hypotheses. The statement
that these are one construction, or that the same transition “carries softmax” and the zeta
functional equation, is `interpretation`; it does not prove anything about Riemann zeros.

### And the Lee–Yang mechanism at degree two

```lean
theorem thePalindromicQuadraticPutsItsZerosOnTheCircle
    (a b : ℝ) (ha : a ≠ 0) (hdisc : b ^ 2 < 4 * a ^ 2) (z : ℂ)
    (hz : (a : ℂ) * z ^ 2 + (b : ℂ) * z + (a : ℂ) = 0) : Complex.normSq z = 1
```

A partition function **palindromic in the fugacity** — which is exactly the `z ↦ 1/z` symmetry — has
root product one, so a conjugate pair must satisfy `z z̄ = 1`. Proved by direct computation: the
imaginary part forces `2a·Re z + b = 0`, and the real part then forces `Re² + Im² = 1`. The
negative discriminant is what makes the roots non-real, and for the two-site Ising chain in fugacity
that holds exactly on the **ferromagnetic** side.

> **`interpretation`:** three fixed-locus equations share an anti-holomorphic-involution shape.
> The Lean theorem is only the degree-two palindromic quadratic and the displayed norm identities;
> it does not prove Lee–Yang in general, the Weil theorem, or any Riemann zero placement. The
> positivity/archimedean-realizer comparison remains an open synthesis.

This proves neither Lee–Yang in general nor anything about the Riemann zeros. Measured 2026-08-20:
`Lee-Yang` appears in 1 file of `research/`, `canon/`, `papers/`, `crates/`, `soma/`; `Knauf` and
`Kuzmin` in 0.

**Measured after:** `Millennium/` is **25 files, 5,421 lines, 279 theorems**, zero `sorry`; the
library builds at 3,312 jobs. The atlas stands at **196 equations, 178 relations**, no dangling.

## 10. The word is a matrix product, and the group is the modular one

```lean
theorem theProductCarriesTheConvergents (n : ℕ) :
    cfProd a (n + 1) = !![hh a (n + 1), hh a n; kk a (n + 1), kk a n]
theorem theDeterminantIsTheProductAlongTheWord (n : ℕ) : (cfProd a n).det = (-1) ^ (n + 1)
theorem theGeneratorsAreUnimodular : sbL.det = 1 ∧ sbR.det = 1
theorem theMediantConditionIsUnimodularity (h k h' k' : ℤ) :
    h * k' - h' * k = 1 ↔ (!![h, h'; k, k']).det = 1
```

The convergent identity was proved in `Towers` by integer induction. Proved again here as a
determinant, it says **where the alternating sign comes from**: the matrix of two consecutive
convergents is `∏ !![aᵢ, 1; 1, 0]`, each factor of determinant `−1`, so the product's determinant is
`(−1)^{n+1}`. **The arithmetic pathway between landmarks is a word in `GL₂(ℤ)`, and where it lands is
the product.**

`L = !![1,0;1,1]` and `R = !![1,1;0,1]` are unimodular and generate the Stern–Brocot tree; the step
matrix is `Rᵗ` composed with the exchange `!![0,1;1,0]`, whose determinant is `−1`. **The exchange is
the swing, and it is what makes the word alternate.** Two fractions are Farey neighbours exactly when
their matrix is unimodular.

> `GL₂(ℤ)` acts on the upper half plane by Möbius transformations, which **preserve the cross
> ratio**. So the sign word's modulus, the convergents, the Farey tree, the modular group and the
> cross-ratio swing are one object at five grains.

**Not built:** the Gauss map `G(x) = 1/x − ⌊1/x⌋` is the shift on these words and its transfer
operator has kernel `Σ_{n≥1}(n+x)^{−2β}`, which at the endpoint is `ζ(2β)` — the same `ζ(2s)` that
carries the squarefree correction. That identification is stated and not proved, and Knauf's Farey
spin chain with partition function `ζ(β−1)/ζ(β)` and its transition at `β = 2` is not built at all.

**Measured after:** `Millennium/` is **26 files, 5,535 lines, 285 theorems**, zero `sorry`; the
library builds at 3,313 jobs. The atlas stands at **198 equations, 180 relations**, no dangling.
