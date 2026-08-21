# The form names its own quotient

**Date:** 2026-08-20
**Kind:** loop iteration 4. One named item closed — by a theorem rather than the witness it asked
for, and the theorem says why no such witness exists in the case that was being hunted. It
schedules nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** the first row of the falsifier table in
[`2026-08-20_THE_HOLLOW_TRIANGLE_CARRIES_THE_WELD.md`](2026-08-20_THE_HOLLOW_TRIANGLE_CARRIES_THE_WELD.md).

## The item asked for a witness; the structure supplies a theorem instead

The row asked for **a chain with a nonzero realized population still lying in the radical**, on the
suspicion that the hollow triangle's weld might be confined to a degenerate case. Going after a
witness was the wrong move, and one line shows why:

```lean
theorem faithfulForcesTrivialRealized (htriv : ∀ v ∈ C.radical, v = 0)
    (N : AddSubgroup V) (hN : N ≤ C.remainder)
    (hdesc : ∀ r ∈ N, ∀ w ∈ C.remainder, C.form r w = 0) :
    ∀ r ∈ N, r = 0
```

> **If the radical is trivial, anything lying in it is zero.** So a chain whose form is *faithful*
> on its retained population can satisfy the descent criterion only when it realized nothing at
> all.

**The hollow triangle's realized population was trivial because its form is faithful, not because
the object was small.** No larger object fixes that, and the witness I set out to find does not
exist in the faithful case. That is a structural answer, not a failed search.

## And the full trichotomy

```lean
theorem theFormAlwaysDescendsOnItsRadical :
    ∀ r ∈ C.radical, ∀ w ∈ C.remainder, C.form r w = 0

theorem theNullOnTheRemainderIsTheRadical {v : V} (hv : v ∈ C.remainder)
    (hnull : C.sign * C.form v v = 0) : v ∈ C.radical

theorem theQuotientIsFaithfulIffTheRealizedIsTheWholeRadical
    (N : AddSubgroup V) (hN : N ≤ C.radical) :
    (∀ v ∈ C.remainder, C.sign * C.form v v = 0 → v ∈ N) ↔ C.radical ≤ N
```

| what is quotiented out | what happens |
|---|---|
| a population **outside** the radical | the form does not descend at all |
| a population **strictly inside** the radical | the form descends, but the quotient still carries null classes |
| **the radical itself** | the form descends and the quotient is faithful |

> **There is one right quotient, and the form names it.** The question was never *which chain lets
> the form descend* — it is that the form already determines its own chain, and a chain that
> disagrees either loses the form or keeps a degeneracy.

That is the same shape as the placement law one level down: you do not choose where to cut, the
involution's fixed locus tells you; here you do not choose what to quotient, the radical tells you.

## A note on the loop's own health

**Three of these four iterations closed by repairing my own framing rather than answering the
question as posed** — a vacuous predicted test, an under-specified structure, and now a witness
hunt that the structure forecloses. That could mean the loop is self-correcting or that it is
generating errors as fast as it fixes them, and the distinguishing evidence is whether the
*theorems* accumulate.

They do: `Millennium/` has gone 101 → **145 theorems** across these four iterations, every one
kernel-checked and audited, with **zero `sorry`** and 2,511 lines. The repairs are also getting
deeper — bilinearity was a defect in a definition; this one is a theorem about which chains can
exist. **Recorded so the pattern is visible rather than asserted either way.**

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A semi-definite datum with a nonzero radical, on a real object.** The trichotomy's interesting row needs one, and constructing the form as a pullback from a quotient would be an authored partition — the form must come from the object. The natural candidate is the pullback of the vertex pairing along a boundary map, whose radical is the cycles. | A cell complex whose boundary-pullback form has trivial radical. |
| **The collapsed population as a chain position**, carried unchanged. | A receiver quotient that is not the outgoing map of any chain. |
| The long chain and the monodromy reading, carried unchanged. | As recorded in the predecessors. |

## Boundaries

Four theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,289
jobs. The trichotomy is a statement about `CompressedPositivity` data and carries nothing about any
named conjecture. The middle row of the table — a population strictly inside the radical — has no
instance in the tree, which is what the first owed row is for.
