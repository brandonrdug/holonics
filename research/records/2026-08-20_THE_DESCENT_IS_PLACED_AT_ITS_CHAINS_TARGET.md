# The descent is placed at its chain's target

**Date:** 2026-08-20
**Kind:** loop iteration 1. One named open item closed. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` for every theorem, kernel-checked and audited free of `sorryAx`.
**Closes:** the first row of the falsifier table in
[`2026-08-20_THE_REMAINDERS_ARE_POSITIONS_ON_ONE_CHAIN_AND_A_SECTIONING_IS_FREE.md`](2026-08-20_THE_REMAINDERS_ARE_POSITIONS_ON_ONE_CHAIN_AND_A_SECTIONING_IS_FREE.md)
— *"Exhibit one of the standing remainders as a chain position. The descent core is the most
tractable."*

## What was owed and what closed it

The coupling record argued that the standing remainders are positions on a transport chain and
**exhibited none as one**. This closes it for the descent, and closes it more sharply than the row
asked: not merely *that* it is a position but **which**.

```lean
def doublingChain (G) [AddCommGroup G] : TransportChain G G (G ⧸ doubled G) where
  into  := doublingHom G
  outOf := QuotientAddGroup.mk' (doubled G)
  composite_zero := …

theorem theDoublingChainIsExact : (doublingChain G).toPassage.Glues
theorem theRepsCoverTheTarget (D : DescentData G) :
    ∀ x : G ⧸ doubled G, ∃ r ∈ D.reps, (QuotientAddGroup.mk r : G ⧸ doubled G) = x
theorem theTargetIsFinite (D : DescentData G) : Finite (G ⧸ doubled G)
```

## The placement, and why it is unambiguous

| chain position | what sits there |
|---|---|
| `ker(into)` | the two-torsion — what doubling collapses |
| `im(into)` = `ker(outOf)` | what doubling reached; **the chain is exact here** |
| the homology | **trivial** |
| the target `G ⧸ 2G` | **the descent's representative set is a transversal of it** |
| `coker(outOf)` | trivial — the reduction is onto |

> **The descent's finite data sits at the chain's target, and the middle is exact.** That is why
> the descent owes exactly one piece of finite data rather than two: were the middle inexact it
> would owe a second there, and `theDescentOwesNothingAtTheMiddle` is the proof that it does not.

And the descent theorem, restated at its position:

```lean
theorem theTransversalAndTheCoreGenerateTheSource (hfin : {x | D.size x ≤ D.bound}.Finite) :
    (∀ x : G ⧸ doubled G, ∃ r ∈ D.reps, ⟦r⟧ = x) ∧ ∃ S : Finset G, closure ↑S = ⊤
```

> **A transversal of the target, together with a bounded core, generates the source.**

The `splits` law of `DescentData` — every element is a representative plus a double — turns out to
be exactly the surjectivity of the representatives onto the target, and the finiteness of the
representative set is exactly the finiteness of the target. **Neither was assumed as a separate
hypothesis; both fall out of the placement.**

## What this does not do

One remainder, one chain, one position. **The compressed-positivity remainder and the collapsed
population are still unexhibited**, and neither placement follows from this one — each needs its
own pair of transports named.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **The compressed-positivity remainder as a chain position.** Its retained population is a kernel; what is the incoming transport whose image sits inside it? | A compressed positivity datum admitting no transport into its remainder. |
| **Does the form descend to the homology?** This is the sharper half and it is now blocked on a defect of my own: `CompressedPositivity.form` is only assumed symmetric, not additive, so its radical is not yet a subgroup. **The structure is under-specified and the next iteration should repair it before asking the question.** | A bilinear compressed positivity datum whose form does not descend to the quotient by its realized population. |
| **The collapsed population as a chain position**, with its receiver family as the outgoing transport. | A receiver quotient that is not the outgoing map of any chain whose middle is its material. |
| The long chain, and the monodromy reading of placement, carried unchanged. | As recorded in the predecessors. |

## Boundaries

Six theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,288
jobs; `Millennium/` stands at eleven files. `DescentData` is the abstract structure from
`Paying.lean` and carries no elliptic curve, height or Mordell–Weil content; the aside placing it
there is in that file and is not repeated as a claim here.
