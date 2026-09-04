# The radical travels and the perp does not

**Date:** 2026-08-20
**Kind:** loop iteration 13. One named item closed; one falsifier refuted and one confirmed. It
schedules nothing. [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *a rebase that carries the form*, named in
[`2026-08-20_AN_OBSTRUCTION_BELONGS_TO_A_FRAME.md`](2026-08-20_AN_OBSTRUCTION_BELONGS_TO_A_FRAME.md).

## The falsifier is refuted, and by an axiom already present

The item's falsifier was *a form-carrying rebase under which the radical is not the image of the
predecessor's radical — which would show the form's data cannot be transported functorially.*

**No such rebase exists.**

```lean
theorem theRadicalTransports {v : V} (hv : v ∈ C.radical) : R.transport v ∈ D.radical := by
  have hmem : R.transport v ∈ D.remainder := R.remainder_maps v hv.1
  refine D.theNullOnTheRemainderIsTheRadical hmem ?_
  rw [R.carries v v, hv.2 v hv.1, mul_zero]
```

Three lines, and **no surjectivity, no injectivity, no hypothesis beyond the two the structure
carries**. A member of the predecessor's radical lands in the successor's remainder pairing with
itself to nothing — and on a semi-definite form that already *is* membership of the radical.

> **The work is done by `theNullConeIsTheRadical` from iteration 2.** The integer Cauchy–Schwarz
> argument that removed an axiom back then is what makes the radical travel now. That is the first
> time in this loop a result has paid twice.

I had expected this to need a covering condition and said so when naming the falsifier. It does
not.

## And the perp genuinely fails

```lean
theorem thePerpTransportsWhenTheRemainderIsCovered
    (onto : ∀ u ∈ D.remainder, ∃ v ∈ C.remainder, R.transport v = u)
    {c : V} (hc : c ∈ C.perp) : R.transport c ∈ D.perp

theorem thePerpDoesNotTransport :
    ((1,0,0) : Cells) ∈ emptyRemainderDatum.perp
      ∧ widenTheRemainder.transport ((1,0,0) : Cells) ∉ fullRemainderDatum.perp
```

The witness is the identity transport between two data over one carrier that differ only in what
they retain. **With nothing retained upstream the perp condition is vacuous and every chain
satisfies it; downstream the form is definite on everything and only zero does.** A single edge
crosses the gap.

> **The form's derived data does not travel as one block. It splits.** The radical is intrinsic
> enough to move — it is a condition a member satisfies against itself, via semi-definiteness. The
> perp is a condition against a *downstream* population, and a transport that does not reach that
> population cannot certify it.

That asymmetry was not visible before the form was made to travel, and it is the substance of this
iteration.

## Where the correction now stands

| what the July record requires to rebase | state |
|---|---|
| the carrier and its populations | **done**, iteration 12 |
| the form | **done**, here |
| the radical, as a consequence | **travels freely** |
| the perp | **travels only under a covering condition**, with the failure witnessed |
| the metric | not modelled |
| the receiver | not modelled |
| the lineage | not modelled |

Four of seven. The remaining three are what the July authority actually means by a receiver
rebasing, and none of them has a definition here.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **Does the cutoff travel?** The perp bounds it and the perp needs covering, so a cutoff's admissibility is presumably frame-relative too — but that is an inference, not a theorem, and inference is what the last five iterations kept getting wrong. | A form-carrying rebase under which an admissible cutoff maps to an inadmissible one, or a proof that it cannot. |
| **A form that pays on a perp**, carried from the reading — still the corpus's own open target since July. | A compression onto a perp that is not positive. |
| **Read more of the 292.** One file redirected four iterations; 288 remain unread. | — |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Three theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,293
jobs; `Millennium/` stands at 3,393 lines and **191 theorems, zero `sorry`**. A `FormRebase` carries
the carrier, its populations and the form, and **nothing else** — the cutoff, the sign, the metric
and any notion of receiver do not travel, and the structure says so. The negative witness is one
pair of data over one carrier under the identity transport.
