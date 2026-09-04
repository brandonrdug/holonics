# The remainders are positions on one chain, and a sectioning is free

**Date:** 2026-08-20
**Kind:** formal derivation deposit answering one named open question. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` for every Lean theorem, kernel-checked and audited free of
`sorryAx`; `proved-standard` for the cited classical results; `interpretation` for the readings.
**Companion:** [`research/equation-atlas/`](../equation-atlas) — six equations and six relations
appended.
**Predecessor:**
[`2026-08-20_THE_PLACEMENT_IS_A_MONODROMY_AND_THE_REMAINDER_IS_WHAT_PAYS.md`](2026-08-20_THE_PLACEMENT_IS_A_MONODROMY_AND_THE_REMAINDER_IS_WHAT_PAYS.md),
whose single open question this record answers.

## Provenance

**Brandon's, directly (2026-08-20).** That we move forward on the single question. **That "one or
four" is the wrong dichotomy** — *"even if they are still four distinct remainders they can still
be coupled."* That like Cartesian graphs, which encapsulate a portion of infinity along however
many axes are depicted, a rectangle is **further divisible into more ratios**, and **you can
section the receiver however you choose**; that *"4" often just means that you have quadrants*; and
that **divisions of turns are intrinsic to orientation and rotation**, which is why octets are
spoken of for half-turns and chains.

**Assistant, this record.** The identification of a transport chain with an additive passage; the
theorem that gluing is exactness and the obstruction group is the homology; the five-position
reading; and the sectioning computations. Graded individually.

---

## 1. The question was posed wrongly, and his correction fixes it

The predecessor record asked whether four remainders were **one object or four**. That is a false
alternative and Brandon named it as one: *distinct and coupled* is the third answer, and it is the
right one.

> **How many remainders one names is a sectioning of the receiver, and a sectioning is free.** A
> plane is not four quadrants; a plane admits a sectioning into four, and into eight, and into any
> number. What is not free is the object being sectioned.

So the useful question is not *how many* but **what couples them**, and the answer is short.

## 2. A chain is a passage, and gluing is exactness

**`proved-derived`, and it is the whole answer.**

```lean
structure TransportChain (A B C) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  into  : A →+ B
  outOf : B →+ C
  composite_zero : ∀ a, outOf (into a) = 0
```

The only hypothesis is that the composite returns nothing. From it alone:

```lean
theorem realized_le_retained : T.realized ≤ T.retained
```

**the realized population sits inside the retained one, for free.** And that containment is
*exactly* the axiom an `AdditivePassage` requires, so:

```lean
def toPassage : AdditivePassage := ⟨B, T.realized, T.retained, T.realized_le_retained⟩

theorem theChainGluesIffItIsExactAtTheMiddle : T.toPassage.Glues ↔ T.retained ≤ T.realized
theorem theCouplingRemainderIsTheHomology :
    T.toPassage.Glues ↔ Subsingleton T.toPassage.ObstructionGroup
```

> **A transport chain is an additive passage. Its obstruction group is its homology. Gluing is
> exactness.**

That is the coupling. The collapse at the source and the obstruction at the middle are not rival
objects and not the same object either — **they are two positions on one chain**, and the homology
is what neither reaches nor collapses.

### The five positions

| position | what it is | which remainder it was |
|---|---|---|
| `ker(into)` | what the incoming transport collapses | the collapsed population no receiver separates |
| `im(into)` | what it realizes | the realized population |
| `ker(outOf)` | what the outgoing transport retains | the locally admissible population |
| `ker(outOf)/im(into)` | **the homology** | **the obstruction group** |
| `coker(outOf)` | what the outgoing transport never reaches | the unreached |

**Five, not four** — and that is Brandon's point rather than a correction of it. The count came
from a sectioning, and a finer sectioning finds more. The compressed-positivity remainder and the
descent core are two further readings of `ker(outOf)`: what an aperture retains, and what a
reduction cannot reduce.

## 3. Sectioning the receiver: free, but not free of consequence

**`proved-derived`.** How many parts one divides a turn into is a choice. What the choice *returns*
is not.

```text
sectionValue n = 2 cos(2π/n)

n = 1  →   2        n = 2  →  −2        n = 3  →  −1
n = 4  →   0        n = 6  →   1
n = 5  →  (√5−1)/2  = 1/φ
n = 8  →  √2        = 2^{2^{-1}}
```

Each computed; the completeness of the rational list is Niven's theorem and is cited, not reproved.

> **The quadrant sectioning returns nothing at all — the value is flat.** Four is where two axes
> cross and the crossing costs zero, which is exactly why a quadrant decomposition can always be
> taken and why "four" is the count that shows up by default. It is not a privileged sectioning; it
> is the cheapest one.

> **The octet is the first sectioning whose value leaves the rationals, and what it lands on is the
> half exponent.** `2cos(2π/8) = √2 = 2^{2^{-1}}`, and `theOctetValueSquaresToTheWhole` proves its
> square is the whole sectioning's value. Halving the quadrant is not an arbitrary refinement — it
> is the first refinement that costs an irrationality, and the irrationality it costs is Brandon's
> own half-exponent notation.

**So the two first refusals of the rational table are the golden reciprocal at five and the half
power at eight** — one in each parity direction. Paired in the atlas as a correspondence; the two
arise by different mechanisms and neither is derived from the other.

That is why speaking in octets for half-turns and chains is structurally right rather than
conventional: **the octet is the first place a turn division becomes a genuine algebraic step.**

## 4. What this settles and what it does not

**Settles:** the coupling. Four (or five) named remainders are positions on one chain; the object
that relates them is the homology; and the condition that all of them collapse to nothing is
exactness. The question the predecessor left open — *are these one object or four* — is answered:
**neither, and the chain is why.**

**Does not settle:** whether the *specific* remainders previously built are the positions of a
*specific* chain. `CompressedPositivity`'s remainder, `DescentData`'s bounded core, and
`receiver_exact_compression`'s collapsed population are each argued here to be readings of a chain
position; **none is exhibited as one.** That construction is the next real step and it is small:
each needs its incoming and outgoing transport named.

## 5. What is owed

**`open`.**

| owed | falsifier |
|---|---|
| **Exhibit one of the standing remainders as a chain position.** The descent core is the most tractable: name the incoming transport as doubling and the outgoing one as reduction modulo the representatives, and check the composite vanishes. | A remainder that admits no pair of transports making it a chain position. |
| **The form on the homology.** `CompressedPositivity` puts a form on a retained population; a chain puts a quotient there. Whether the form descends to the quotient is the question that would weld sections 2 and 3 of `Paying.lean` together. | A compressed positivity datum whose form does not descend to the homology. |
| **The long chain.** Only two steps are formalized. Adjacent positions of a longer chain are related by connecting maps, and nothing here carries one. | A three-step chain whose homologies do not compose. |
| The monodromy reading of placement, carried unchanged from the predecessor. | As recorded there. |

## 6. Boundaries

Every Lean theorem cited is kernel-checked; ten were audited by `#print axioms` in this pass and
none depends on `sorryAx`. The library builds at 3,287 jobs; `Millennium/` stands at ten files,
2,073 lines, 115 theorems, zero occurrences of `sorry`. Niven's theorem is cited for the
completeness of the rational sectioning list; the five values are computed individually. The
identification of a chain's obstruction group with its homology is a restatement and is labelled as
one — its value is the coupling it states, not novelty. Nothing in this record is a claim about any
named conjecture.
