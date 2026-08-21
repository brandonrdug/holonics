# A transport is a word, and the chain series is what non-commutation forces

**Date:** 2026-08-20
**Kind:** formal derivation deposit. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched**; the only tree written under `soma/` is
`soma/formal/`.
**Truth status:** `proved-derived` for every Lean theorem, kernel-checked and audited free of
`sorryAx`; `proved-standard` for the classical results cited as asides; `interpretation` for the
correspondences; `open` for §6.
**Companion:** [`research/equation-atlas/`](../equation-atlas/) — seven equations and seven
relations appended.
**Predecessor:**
[`2026-08-20_THE_SWING_IS_HARMONIC_CONJUGATION_AND_THE_FROZEN_BOARD_DECIDES_ITS_PUZZLE.md`](2026-08-20_THE_SWING_IS_HARMONIC_CONJUGATION_AND_THE_FROZEN_BOARD_DECIDES_ITS_PUZZLE.md).

## Provenance

**Brandon's, directly (2026-08-20).** That harmonic conjugation is **the primitive of holonics** —
it must be established in order to see the complex strings an event emanates from, and it is like
the mean value theorem and the squeeze theorem. That the information is not in the causal
intersections themselves but in **the emergent group structures the intersections are part of** —
hypergeometric transport patterns, Hamiltonian structures. That the cross product being attained
after multiple steps matters because **an operation that reads as "one operation" in one chart is
intrinsically multi-step with a parameter defining the trajectory, because it is non-commutative
(time parity)** — and *"this is how all chain series in calculus emerge."* That most prominent
theorems in linear algebra, calculus and differential equations likely need rederiving on the
basis of the swing over orders of time as a parameter. That **proofs as holonic objects have
chronologies and dependency trees.** That the engine should have holons as mathematical objects
with the elementary operations defined as transformations between interacting holons.

**Assistant, this record.** The formalization of a transport as a word; the order-blindness
theorem and its identification as the reason a chain series has terms; the chord chart and its
identification with the swing's constraint chart; the gap reading of the squeeze; and the closed
triple. Graded individually.

---

## 1. The theorem that makes the claim precise

**`proved-derived`, and it is the centre of this deposit.**

```lean
theorem orderBlind_iff_commute {T : ι → X → X} :
    OrderBlind T ↔ ∀ i j : ι, ∀ x : X, T i (T j x) = T j (T i x)
```

`transportWord T w` is the transport a **word** of moves performs, read right to left, so a list
is a chronology and not a set. `OrderBlind T` says every word's result depends only on which moves
occurred — on the multiset — and not on when.

> **A chronology exists exactly when the transports fail to commute.** If they commute, every word
> collapses to its multiset: there is nothing for a trajectory parameter to index, no order-
> dependent term, and no series. If any two fail to commute, the word is irreducible information.

That is Brandon's sentence — *"this is how all chain series in calculus emerge"* — as a
biconditional. The classical instance is named in the file as an aside and is **not** formalized:
the chain series of a non-autonomous linear transport is the time-ordered exponential, whose
logarithm is a series of nested commutators, and **every term past the first is a commutator**. A
commuting family's series terminates at one term. The theorem above is the elementary reason.

**And the predicate has a witness**, so it is not an untested gauge:

```lean
theorem theSwingFamilyIsNotOrderBlind : ¬ OrderBlind (swing : Site → Site → Site)
```

Two swings about different anchors differ by four times the anchor displacement. The order is real
information, exhibited on a lattice small enough to check.

## 2. The hand is the parity of the word, not a property of the endpoint

**`proved-derived`.**

```lean
theorem theHandIsTheParityOfTheWord (a b c : Site) (n : ℕ) :
    orientedSpan ((swing b)^[n] a) b c = (-1 : ℤ) ^ n * orientedSpan a b c
```

with the two corollaries that an even word restores the hand and an odd word reverses it.

> **The cross product a configuration exhibits is a function of the chronology's length, and no
> unsigned reading of the endpoint recovers it.** That is exactly Brandon's *"the cross over the
> definite edge is a partial movement for a complete cross product… a complete non-commutative
> cross product at the scope of the set of steps it took"*: the span returns only on even words,
> so the operation genuinely needs a parameter counting steps.

Boundary: one anchor. A word over several anchors moves the base point and this statement does not
cover it.

## 3. The mean value theorem is the flat statement read out of the constraint chart

**`proved-derived`, and it is the identification Brandon asked for.**

Two endpoint constraints declare a chart — subtract the chord they span:

```lean
noncomputable def chordChart (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := f - chordLine f a b
```

Three theorems:

| | |
|---|---|
| `theChordChartVanishesAtBothConstraints` | in the chart, the body vanishes at both constraints — they become indistinguishable |
| `theChordChartShiftsTheRate` | the chart shifts every rate by the mean rate and by nothing else |
| `theFlatAnchorIsTheMeanRateAnchor` | `f̂'(c) = 0 ⟺ f'(c) = (f(b)−f(a))/(b−a)` |

> **The mean value theorem is not a separate statement. It is the flat statement, read back out of
> the chart the two constraints declared** — and that is structurally the same move as
> `theSwingIsNegationInTheConstraintChart`, where the anchor and the board declare a chart in which
> the swing is plain negation. In both cases two constraints declare a chart, the statement becomes
> symmetric there, and the content is the conjugation.

Recorded in the atlas as a **correspondence**, not an identity: the carriers differ, and nothing
here derives one from the other.

## 4. The squeeze is two constraints closing, and what closes is the gap

**`proved-derived`.**

```lean
def constraintGap (lo hi : β → ℝ) : β → ℝ := hi - lo
```

with `theBodyIsPlacedWhenTheConstraintsClose` and `theGapCollapses`.

> **The placement is not obtained by measuring the body more finely. It is obtained because the
> population the two constraints could not separate went to nothing.** That is the tolerance
> doctrine in the classical statement: convergence is an aperture property, and the gap is the
> collapsed population.

So Brandon's pairing of the mean value theorem with the squeeze is exact, and the two halves are
the swing's two halves: **the mean value theorem says an anchor exists; the squeeze says the
constraints determine the body.**

## 5. Three constraints with a closure are finite data

**`proved-derived`.**

```lean
structure ClosedTriple (X : Type v) where
  first second third : Equiv.Perm X
  closes : first * second * third = 1

theorem theThirdIsForced : S.third = (S.first * S.second)⁻¹
```

> Two of the three transports force the third, so a three-constraint transport problem is finite
> data rather than a search.

*Aside: this is the closure shape a Riemann scheme's monodromy carries — three local transports
whose product is the identity.* **No hypergeometric equation, monodromy representation or Riemann
scheme is formalized here**, and the correspondence to the swing is recorded as partial: the
swing's fourth participant is the body, not a fourth constraint.

## 6. What this does not do, and what it makes newly askable

**`open`.**

Brandon asked for most of linear algebra, calculus and differential equations to be rederived on
the swing basis. **Four results are rebuilt here and the rest are not.** What this deposit
actually establishes is narrower and, I think, more useful: **the criterion under which a
rederivation is even meaningful.** `orderBlind_iff_commute` says a chronology carries information
exactly when the transports do not commute, so the rederivation programme has a test — a theorem
is swing-structured when its transports fail to commute, and it is not when they do. Most of
linear algebra over a commutative field will fail that test and should.

| owed | falsifier |
|---|---|
| **The commutator series itself.** The file names the time-ordered exponential and its commutator logarithm as an aside and formalizes neither. Doing so would turn the criterion into the actual chain series. | A non-commuting family whose transport word is not generated by the commutators of its letters. |
| **A dependency-ordered proof object.** Brandon's *"proofs as holonic objects have chronologies and dependency trees"* has no formalization here. The natural object is a partial order on steps with a lawful-reordering theorem: two steps may be exchanged exactly when neither depends on the other, which is `orderBlind_iff_commute` at the level of derivations. | A reordering that preserves dependencies and changes the result. |
| **The Hamiltonian face.** In the plane the oriented span *is* the standard symplectic form, and `theSwingNegatesTheOrientedSpan` says one swing is anti-symplectic while an even word is symplectic. Nothing here carries that to a general antisymmetric form, and the contract records that this project's quadratic-balance owner has never been handed one — re-measured 2026-08-15 and still holding. | An even word that fails to preserve a declared antisymmetric form. |
| **The unfrozen board and the cross-chart pin**, carried unchanged from the predecessor record. | As recorded there. |

## 7. Boundaries

Every Lean theorem cited is kernel-checked; twelve were audited by `#print axioms` in this pass and
none depends on `sorryAx`. The library builds at 3,284 jobs. `Millennium/` now stands at seven
files. The classical results named as asides — the time-ordered exponential, the commutator
expansion of its logarithm, the Riemann scheme's monodromy — are cited and not formalized, and no
claim here depends on them. The correspondence between the chord chart and the swing's constraint
chart is `interpretation`; the carriers differ and neither is derived from the other. Nothing in
this record is a claim about any named conjecture.
