# Faithfulness was never an axiom, and the form descends on its radical

**Date:** 2026-08-20
**Kind:** loop iteration 2. One defect of mine repaired, one named question answered. It schedules
nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** the second row of the falsifier table in
[`2026-08-20_THE_DESCENT_IS_PLACED_AT_ITS_CHAINS_TARGET.md`](2026-08-20_THE_DESCENT_IS_PLACED_AT_ITS_CHAINS_TARGET.md).

## The defect, and why it mattered

`CompressedPositivity.form` was declared as a bare function with only symmetry assumed. **That is
under-specification, not a simplification**: without additivity the radical is not a subgroup, so
the question *does the form descend to the homology* could not even be posed. I named the defect
in the previous iteration and it is repaired here — the form is now `V →+ V →+ ℚ`, bilinear by
construction.

## What the repair immediately bought

**One axiom of the structure turned out to be redundant.**

```lean
theorem theNullConeIsTheRadical {v : V} (hv : v ∈ C.remainder)
    (hnull : C.sign * C.form v v = 0) {w : V} (hw : w ∈ C.remainder) :
    C.sign * C.form v w = 0
```

> **A semi-definite form's null cone is its radical.** If a member of the remainder pairs with
> itself to nothing, it pairs with everything there to nothing.

The argument is Cauchy–Schwarz's, run **over the integers** because the carrier is an abelian group
and no rational scaling is available on it: `n•v + w` stays in the remainder for every integer `n`,
its self-pairing expands to `2n·q(v,w) + q(w,w)`, and a linear function of an integer that is never
negative has zero slope.

Consequently:

```lean
theorem theFaithfulConditionIsTheTrivialRadical :
    (∀ v ∈ C.remainder, C.sign * C.form v v = 0 → v = 0) ↔ ∀ v ∈ C.radical, v = 0
```

**So `faithful` was never an independent axiom** — it is the triviality of the radical, and
semi-definiteness alone forces the two conditions to agree. It has been removed from the structure
and is now a hypothesis on the two theorems that need it.

## And the question the previous record could not pose

```lean
theorem theFormDescendsIffTheQuotientedIsInTheRadical (N : AddSubgroup V) (hN : N ≤ C.remainder) :
    (∀ v ∈ C.remainder, ∀ r ∈ N, ∀ w ∈ C.remainder, C.form (v + r) w = C.form v w)
      ↔ (∀ r ∈ N, ∀ w ∈ C.remainder, C.form r w = 0)
```

> **The form descends to a quotient exactly when what is quotiented out lies in the radical.**

A chain puts a quotient at the middle; a compressed positivity datum puts a form on the retained
population. **The form survives the chain's quotient exactly when the realized population pairs
with everything retained to nothing.** That is the criterion, and it is now stated and proved in
general.

## What this does not settle

**No chain is exhibited whose realized population meets the condition.** The criterion says *when*
the form descends; whether it does for the doubling chain of iteration 1, or for any other, is
untouched. That is the next question and it is now well-posed, which it was not an hour ago.

`flipSign` was dropped in the rewrite and has been restored, since
[the monodromy record](2026-08-20_THE_PLACEMENT_IS_A_MONODROMY_AND_THE_REMAINDER_IS_WHAT_PAYS.md)
cites it by name.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **Does the form descend for a chain that carries one?** The criterion exists; no instance does. The doubling chain is the obvious first test, and its realized population is `2G` — so the question is whether `q(2g, w) = 0` for all retained `w`, which is false in general. **Expect a negative, and a negative here is informative: it would say the form does not descend to a doubling homology and the two structures do not weld at that chain.** | A chain whose realized population is in the radical, exhibited. |
| **The compressed-positivity remainder as a chain position**, carried unchanged. | A datum admitting no transport into its remainder. |
| **The collapsed population as a chain position**, carried unchanged. | A receiver quotient that is not the outgoing map of any chain. |
| The long chain and the monodromy reading, carried unchanged. | As recorded in the predecessors. |

## Boundaries

Five theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,288
jobs. The structure change removes one field and adds bilinearity; no instance of
`CompressedPositivity` exists in the tree, so nothing downstream broke and none of the readings
previously recorded for it is affected. The null-cone theorem holds **only under
semi-definiteness** — an indefinite form's null cone is strictly larger than its radical, and the
atlas relation records that boundary.
