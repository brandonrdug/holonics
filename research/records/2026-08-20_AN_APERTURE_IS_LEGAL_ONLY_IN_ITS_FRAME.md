# An aperture is legal only in its frame

**Date:** 2026-08-20
**Kind:** loop iteration 14. One named item closed, proved rather than inferred. It schedules
nothing. [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *does the cutoff travel*, named in
[`2026-08-20_THE_RADICAL_TRAVELS_AND_THE_PERP_DOES_NOT.md`](2026-08-20_THE_RADICAL_TRAVELS_AND_THE_PERP_DOES_NOT.md).

## The result

```lean
theorem theCutoffTravelsUnderCovering
    (onto : ∀ u ∈ D.remainder, ∃ v ∈ C.remainder, R.transport v = u)
    {c : V} (hc : c ∈ C.cutoff) : R.transport c ∈ D.perp

theorem theCutoffDoesNotTravel :
    ((1,0,0) : Cells) ∈ wideCutoffDatum.cutoff
      ∧ ¬ (∀ v ∈ fullRemainderDatum.remainder,
            fullRemainderDatum.form ((1,0,0) : Cells) v = 0)
```

> **The widest aperture is admissible while nothing is retained. Widen what is retained — along the
> identity transport, over one carrier, with the form unchanged — and the same aperture is no
> longer admissible at all.**

**A cutoff is admissible relative to a frame, not as a property of the material.** It is the third
derived object shown frame-relative, after the obstruction and the perp, and the radical remains
the only one that travels freely.

## On having proved it rather than inferred it

I named this item with the note that inferring it would repeat what iterations 8 through 11 kept
getting wrong, and that it would be proved or stay open. **The inference would have been correct**
— a cutoff sits inside the perp, the perp needs covering, so the cutoff needs covering.

So the discipline cost one iteration and bought nothing this time. **That is the right trade and it
is worth recording as such**, because the argument against applying it is always that the inference
looks safe, and the four occasions it was not looked equally safe from inside.

What proving it did add, which the inference would not have: **an explicit witness**. The wide
aperture over an empty remainder is a legal configuration that becomes illegal under a rebase that
changes nothing but what is retained. That configuration is now in the tree and can be pointed at.

## Where the frame-relativity now stands

| object | travels? |
|---|---|
| the **radical** | **freely** — carried by semi-definiteness alone |
| the obstruction group | **no** — witnessed, iteration 12 |
| the perp | **only under covering** — witnessed, iteration 13 |
| the cutoff | **only under covering** — witnessed, here |

One object out of four is intrinsic. **The rest belong to their frames**, which is the July
authority's position arrived at from inside rather than accepted from outside.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **Does the sign travel?** The last declared field of `CompressedPositivity` that has not been examined. It is a unit and the form travels, so it looks forced — which is exactly what the cutoff looked like. | A form-carrying rebase between data whose signs differ, or a proof that the sign is determined by the form and the remainder. |
| **A form that pays on a perp**, carried from the reading — the corpus's own open target since July. | A compression onto a perp that is not positive. |
| **Read more of the 292.** 288 remain unread. | — |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Two theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,293
jobs; `Millennium/` stands at 3,459 lines and **193 theorems, zero `sorry`**. The witness is one
pair of data over one carrier under the identity transport with the form unchanged. It establishes
that admissibility is frame-relative and says nothing about how apertures vary in general. Nothing
here is a claim about any named conjecture.
