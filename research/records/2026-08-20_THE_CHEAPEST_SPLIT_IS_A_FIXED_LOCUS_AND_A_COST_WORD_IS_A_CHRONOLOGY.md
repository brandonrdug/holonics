# The cheapest split is a fixed locus, and a cost word is a chronology

**Date:** 2026-08-20
**Kind:** formal derivation deposit. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` for every Lean theorem, kernel-checked and audited free of
`sorryAx`; `proved-standard` for the classical results named as asides; `interpretation` for every
correspondence; `open` for §5.
**Companion:** [`research/equation-atlas/`](../equation-atlas) — ten equations and eight relations
appended.
**Predecessor:**
[`2026-08-20_A_TRANSPORT_IS_A_WORD_AND_THE_CHAIN_SERIES_IS_WHAT_NON_COMMUTATION_FORCES.md`](2026-08-20_A_TRANSPORT_IS_A_WORD_AND_THE_CHAIN_SERIES_IS_WHAT_NON_COMMUTATION_FORCES.md),
whose criterion this record instantiates on a real analytic object.

## Provenance

**Brandon's, directly (2026-08-20).** That rederiving the elementary operations will *seem* like
brute force, but the point is that **characteristic transport patterns become visible** — like the
edges crossing twice to complete a cross product. That a cross product of very high-dimensional
tensors, or a matrix multiplication, is expensive in one chart but **perhaps a couple of pivoting
swings integrating into a recombined system on a higher-level coarse grain.** That if such
transport mechanisms exist, the tediously founded operations can be **matched for higher-level
commonalities and characteristic properties of hypergeometric transport mechanisms** — which is
what he has meant about integral substitutions, and about polynomials → polygons → polyhedra →
polytopes traversed by Möbius objects, where orientable and non-orientable surfaces relate to how
the receiver measures contemporary geometric properties. **That this be applied to the Riemann
Hypothesis and the completed comb, since the computability of it is worth thinking about anyway.**

**Assistant, this record.** The identification of the balanced split as a fixed locus; the
parity grading and its Möbius reading; the cost alphabet and its instantiation of the chronology
criterion; and the readings in §4.

---

## 1. The cheapest split is the fixed point of the swing that relates the two charts

**`proved-derived`, and it is the centre of this deposit.**

A computation of size `T` that factors into two pieces of sizes `x` and `T/x`. The map
`x ↦ T/x` is an involution — choosing one piece chooses the other. Its fixed point is `√T`.
Separately, the total work is `x + T/x`, and its minimum is `2√T`.

```lean
theorem theCheapestSplitIsTheFixedPointOfTheSwing {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    splitSwing T x = x ↔ ∀ y : ℝ, 0 < y → splitWork T x ≤ splitWork T y
```

> **Two independent readings — the symmetric one and the cheap one — pick the same point.**
> Nothing about cost went into the involution and nothing about symmetry went into the
> minimisation, and they coincide. **This is the placement law arriving in computational cost:
> the place to cut is the fixed locus of the involution that relates the two charts.**

The whole content is one identity, `theWorkExcessIsASquare`:

```text
(x + T/x) − 2√T  =  (x − √T)² / x
```

which carries the lower bound and its equality case together — the excess *is* a square, and a
square vanishing is exactly the fixed-point condition.

### Why this is the answer to Brandon's question about the comb

**`interpretation`; the analytic statements are cited and none is formalized.**

Evaluating the comb on the seam at height `t` costs `O(t)` by the naive summation, because the
sum needs about `t` terms. The classical improvement splits it in two using the reflection
`s ↦ 1 − s` — the same involution whose fixed locus `Seam.lean` proves is the critical line:

```text
one sum of length ≈ t      →      two sums of lengths x and y with xy = t/2π
```

**The optimal cut is `x = y = √(t/2π)` — the fixed point of `x ↦ (t/2π)/x` — and the cost drops
to `O(√t)`.** That is exactly *"a couple of pivoting swings integrating into a recombined system
on a higher-level coarse grain"*, on the object he named, with the saving factor being the same
half that the seam sits at.

*Asides, cited and not formalized: the approximate functional equation and the Riemann–Siegel
formula give the `O(√t)` evaluation; Odlyzko–Schönhage amortizes many evaluations to `O(t^ε)`
each after `O(t^{1/2+ε})` precomputation; Hiary gives `O(t^{1/3})` for a single value.* **The
progression itself is the evidence for his thesis**: each step is a further chart change, not a
faster loop.

## 2. The swings are graded by parity, and the grading is the orientation class

**`proved-derived`.**

```lean
theorem theOddCircuitIsASwingAboutTheAlternatingSum (b₁ b₂ b₃ a : G) :
    swing b₁ (swing b₂ (swing b₃ a)) = swing (b₁ - b₂ + b₃) a
```

**An odd word of swings *is* a swing** — about the alternating sum of its anchors. Three crossings
do not accumulate into something new; they collapse to one crossing about a new anchor, and the
alternation is the hand. An even word is a translation, and a four-letter word is a translation
exactly as a two-letter word is, so **the grading is by parity and not by length.**

And the Möbius reading is forced rather than analogous:

```lean
theorem theOddReturningCircuitReversesTheHand (a b c : Site) {n : ℕ} (hn : Odd n)
    (hret : (swing b)^[n] a = a) :
    orientedSpan a b c = - orientedSpan a b c
```

> **The body comes home; the orientation does not.** That is what a band with one side is. And the
> corollary is sharp: such a circuit forces the span to vanish, so **an odd returning circuit is
> only available where the body already sits on the line its two constraints span.** A hand that
> reverses and stays equal is a hand that was never there.

**Three carriers of one two-element class are now in the corpus**: the address orientation on the
integers, the orientation of a band, and the parity of a swing word. The 2026-08-16 junction
record named the first two; this adds the third. Recorded as a correspondence — the carriers
differ and none is derived from another.

## 3. The cost alphabet, and the chronology criterion applied to it

**`proved-derived`, and this closes the loop opened by the predecessor record.**

Bounding a sum of the kind the split produces is done classically by moving a **pair of exponents**
through two operations. Carried here as pure arithmetic on `ℚ × ℚ`:

| move | law | what is proved |
|---|---|---|
| **frequency swing** | `B(k,l) = (l − ½, k + ½)` | **an involution** |
| **difference contraction** | `A(k,l) = (k/(2k+2), (k+l+1)/(2k+2))` | **fixes the trivial pair `(0,1)`** |

Then:

```lean
theorem theWeylCostIsOneSwingThenOneContraction :
    differenceContraction (frequencySwing trivialCost) = (1 / 6, 2 / 3)

theorem theTwoMovesDoNotCommute :
    differenceContraction (frequencySwing trivialCost)
      ≠ frequencySwing (differenceContraction trivialCost)

theorem theCostAlphabetIsNotOrderBlind : ¬ OrderBlind costAlphabet
```

> **One swing then one contraction reaches the classical pair; contracting first goes nowhere,
> because the contraction fixes the trivial pair. The order is the whole difference.** So by
> `orderBlind_iff_commute`, a cost word is a genuine chronology: the exponent a sum admits depends
> on *when* each move was made, not only on how many of each.

That is the criterion of the predecessor record instantiated on a real object from analytic number
theory — an alphabet of two moves, one of them an order-two chart transition, generating a
non-commutative word structure.

*Asides, cited and not formalized: these are the van der Corput B- and A-processes and their
exponent pairs; `(1/6, 2/3)` is the Weyl pair, from which the classical bound on the comb follows.*
**No analytic consequence is formalized here** — only the arithmetic of the alphabet.

## 4. What this establishes and what it does not

**It establishes** that in at least one concrete family, the two things Brandon asserted are true
and provable: **the cheapest chart change is located by a fixed locus**, and **the moves that
generate the useful transport patterns form a non-commuting alphabet whose words are
chronologies.**

**It does not establish** that any particular expensive computation admits such a chart change.
The split theorem is about a two-piece factorization of a size, not about tensors, matrices, or
any specific algorithm; the alphabet theorems are arithmetic on a pair of rationals and carry no
analytic content. Brandon's high-dimensional example is not touched, and the record says so rather
than gesturing at it.

**And one thing is worth naming plainly.** The progression `O(t) → O(√t) → O(t^{1/3}) → O(t^ε)`
for the comb is real and is achieved by successive chart changes. But **no chart change makes the
placement question cheaper** — every one of these evaluates the comb faster and none of them says
anything about where the zeros are. That boundary matters: navigability and placement are
different questions, and the whole record is about the first.

## 5. What is owed, with falsifiers

**`open`. None is scheduled.**

| owed | falsifier |
|---|---|
| **The general odd word.** Only the three-letter case of the alternating-sum collapse is formalized. | An odd word of length five whose composite is not a swing about the alternating sum. |
| **A second split family.** One instance of "cheapest = fixed locus" is one instance. The claim deserves a second carrier — a split into three pieces, or a split whose cost is not additive. | A split family whose cheapest cut is not a fixed locus of its own complementarity involution. |
| **The word-to-bound map.** The alphabet is formalized and its analytic consequence is not, so nothing here connects a cost word to an actual bound. | A cost word whose exponent disagrees with the classical exponent-pair theory. |
| **Brandon's high-dimensional example.** Whether a tensor contraction admits a swing-shaped chart change is untouched, and it is the case he actually cares about. | A contraction whose chart-change cost provably exceeds its direct cost in every chart. |
| **The unfrozen board and the cross-chart pin**, carried unchanged from two records back. | As recorded there. |

## 6. Boundaries

Every Lean theorem cited is kernel-checked; fifteen were audited by `#print axioms` in this pass
and none depends on `sorryAx`. The library builds at 3,285 jobs; `Millennium/` now stands at eight
files. The approximate functional equation, the Riemann–Siegel formula, the Odlyzko–Schönhage and
Hiary evaluation costs, the van der Corput processes and the exponent-pair theory are all cited as
asides and none is formalized; no theorem here depends on any of them. Nothing in this record is a
claim about any named conjecture, and §4 states explicitly that none of it touches placement.
