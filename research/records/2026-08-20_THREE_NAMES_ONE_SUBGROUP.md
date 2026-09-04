# Three names, one subgroup

**Date:** 2026-08-20
**Kind:** loop iteration 7. The last unplaced remainder is placed, and on one object three
vocabularies collapse to one subgroup. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *the collapsed population as a chain position*, carried unaddressed through four
iterations and named as deferred in
[`2026-08-20_THE_THETA_CARRIES_BOTH_AND_THE_PULLBACK_CANNOT_PAY.md`](2026-08-20_THE_THETA_CARRIES_BOTH_AND_THE_PULLBACK_CANNOT_PAY.md).

## What was in the way, and it was not difficulty

The collapsed population is a *relation* — pairs a receiver cannot separate — and a chain position
is a *subgroup*. That gap is what made it look like the hard one, and it closes as soon as the
readings are additive:

```lean
theorem unseparatedIffDifferenceCollapsed (a b : X) :
    (∀ i, read i a = read i b) ↔ (b - a) ∈ collapsedPopulation read
```

> **With additive readings, indistinguishability is a coset condition.** Two constructions are
> unseparated exactly when their difference lies in the intersection of the readings' kernels — and
> that intersection is a subgroup.

Then the placement is immediate:

```lean
def receiverChain (into : A →+ X) (h : ∀ a i, read i (into a) = 0) : TransportChain A X (ι → V)

theorem theCollapsedIsTheRetainedPosition :
    (receiverChain read into h).retained = collapsedPopulation read

theorem theChainGluesIffTheCollapsedWasRealized :
    (receiverChain read into h).toPassage.Glues ↔ collapsedPopulation read ≤ …realized
```

> **The collapsed population is the retained position of the chain whose outgoing transport is the
> receiver — the same position the compressed-positivity remainder occupies.** What a receiver
> cannot separate and what an aperture does not admit are one *position*, not two.

Recorded carefully in the atlas: **same position, not the same object.** Nothing here identifies a
receiver's kernel with an aperture's complement.

## And on the theta complex, three names coincide

```lean
theorem theCyclesAreRetainedRadicalAndCollapsed :
    thetaChain.retained = collapsedPopulation boundaryReading
      ∧ ∀ e, e ∈ thetaChain.retained ↔ e ∈ thetaDatum.radical

theorem theSurvivingLoopWitnessesAllThree :
    (0,1,-1) ∈ thetaChain.retained ∧ (0,1,-1) ∈ thetaDatum.radical
      ∧ (0,1,-1) ∈ collapsedPopulation boundaryReading ∧ (0,1,-1) ∉ thetaChain.realized
```

> **The cycles are at once what the chain retains, what the boundary-pullback form cannot see, and
> what the boundary reading collapses.** Three vocabularies this development built separately —
> homological, positivity-theoretic, receiver-theoretic — name one subgroup here, and the surviving
> loop inhabits all three while nothing realizes it.

That is the strongest form the weld has taken. One object, one subgroup, three descriptions, with a
witness.

## The state of the question this loop opened

The loop began from *are the remainders one object or four*. Seven iterations later:

| remainder | position | placed |
|---|---|---|
| obstruction group | the homology `ker g / im f` | iteration 1 (the coupling record) |
| descent bounded core | the chain's **target** | iteration 1 |
| compressed-positivity remainder | `ker g` — retained | iterations 2–6 |
| collapsed population | `ker g` — retained | **here** |

**All four are placed.** Two share a position; none is the same object as another; the chain is
what relates them. Brandon's correction that *"even if they are still four distinct remainders they
can still be coupled"* is what the answer turned out to be, and the coupling is the chain.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A form defined on a homology rather than pulled back to it**, carried from iteration 6 — the only remaining construction that could pay on a nonzero homology. | A boundary-pullback form that is faithful on a nonzero homology, which iteration 6 forbids. |
| **Do the two remainders at the same position ever differ on one object?** They share a position; whether a single object can carry both a receiver kernel and an aperture complement that are *different* subgroups is unexamined, and the answer decides whether the position is one object after all. | An object where the receiver's collapsed population and the datum's remainder are provably distinct subgroups. |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Eight theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,291
jobs; `Millennium/` stands at 2,965 lines and **174 theorems, zero `sorry`**. The additive-reading
requirement is real and stated: for a general receiver family the collapsed population is a relation
and cannot sit on a chain. The threefold coincidence is proved on the theta complex and asserted
nowhere else.
