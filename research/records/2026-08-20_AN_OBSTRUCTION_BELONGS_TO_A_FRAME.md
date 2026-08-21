# An obstruction belongs to a frame

**Date:** 2026-08-20
**Kind:** loop iteration 12. The corrective the previous reading named, built and witnessed. It
schedules nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *a rebasing passage*, named in
[`2026-08-20_THE_POSITIVITY_LIVES_ON_A_SUBSPACE_AND_I_AIMED_AT_A_QUOTIENT.md`](2026-08-20_THE_POSITIVITY_LIVES_ON_A_SUBSPACE_AND_I_AIMED_AT_A_QUOTIENT.md).

## What the reading required

The July authority on the arithmetic line rejects the picture every structure here assumes — an
ambient carrier held fixed while populations are compared inside it. Its words: such a picture
*"lets an observer stand outside the arithmetic process, freeze the former manifold, append a new
coordinate, and compare both inside one supposed total field."*

The minimal correction is a **rebase**:

```lean
structure PassageRebase (A B : AdditivePassage) where
  transport : A.Candidate →+ B.Candidate
  realized_maps    : AddSubgroup.map transport A.Realized ≤ B.Realized
  admissible_maps  : AddSubgroup.map transport A.LocallyAdmissible ≤ B.LocallyAdmissible
```

with composition and identity, so a lineage of foundings is a lineage of rebases rather than a
sequence of unrelated frames.

## The witness, and it needs no new carrier

```lean
def fillTheFace : PassageRebase hollowPassage filledPassage where
  transport := AddMonoidHom.id Cells   -- nothing about the carrier moves
  …

theorem gluingDoesNotTransport :
    ∃ B : PassageRebase hollowPassage filledPassage,
      ¬ hollowPassage.Glues ∧ filledPassage.Glues

theorem theObstructionIsNotAnInvariantOfTheCarrier :
    hollowPassage.Candidate = filledPassage.Candidate
      ∧ ¬ Subsingleton hollowPassage.ObstructionGroup
      ∧ Subsingleton filledPassage.ObstructionGroup
```

> **One carrier. One rebase along the identity transport. The obstruction goes from inhabited to
> empty.**

Nothing about the carrier moves — what moves is *which population is realized*. Filling the
triangle's face is the whole event, and it is exactly the change the static picture cannot
represent, because that picture holds the former block intact and asks how the new coordinate
attaches.

> **So an obstruction group is an invariant of the material together with its frame, never of the
> material alone.** Gluing is not a property a transport carries.

That is the no-absolute-frame law arriving *inside* this development rather than being quoted at
it, and it qualifies every obstruction claim in the eleven preceding iterations: each is a
statement about a passage, not about the carrier the passage sits on.

## What this does not do

**It corrects the smallest part of what the July record convicted.** That record has the receiver
rebasing — carrier, metric, projection and lineage all moving together. A `PassageRebase` moves the
carrier and its populations and **nothing else**: the form does not travel, the metric does not
change, and no notion of a receiver appears. It is the minimal correction and it is stated as such
on the structure itself.

So the static-ambient limit named last iteration is **narrowed, not lifted**. Every
`CompressedPositivity` in the tree still carries one fixed form over one fixed carrier.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A rebase that carries the form.** `PassageRebase` moves populations; a compressed positivity datum has a form, a cutoff and a sign that do not travel with it. Until they do, the correction does not reach the objects that pay. | A form-carrying rebase under which the radical is not the image of the predecessor's radical — which would show the form's data cannot be transported functorially. |
| **A form that pays on a perp**, carried from the previous reading — still the corpus's own open target since July. | A compression onto a perp that is not positive. |
| **Read more of the 292.** One file redirected four iterations; 288 remain unread. | — |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Four theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,292
jobs; `Millennium/` stands at 3,233 lines and **187 theorems, zero `sorry`**. The witness is one
pair of passages over one carrier and establishes frame dependence, not any law governing how an
obstruction varies. Nothing here is a claim about any named conjecture, and nothing here models a
changing metric or receiver.
