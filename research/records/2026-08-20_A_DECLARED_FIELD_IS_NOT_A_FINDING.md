# A declared field is not a finding

**Date:** 2026-08-20
**Kind:** loop iteration 8. One named item closed, and a row of the previous record withdrawn. It
schedules nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *do the two remainders at the same position ever differ on one object*, from
[`2026-08-20_THREE_NAMES_ONE_SUBGROUP.md`](2026-08-20_THREE_NAMES_ONE_SUBGROUP.md).

## The answer is yes, and it convicts a row I wrote an iteration ago

The previous record tabulated the compressed-positivity **remainder** as sitting at the chain's
retained position. **That row is withdrawn.**

```lean
theorem theRemainderIsNotTheRetained : thetaDatum.remainder ≠ thetaChain.retained
```

On the theta complex the datum declares an aperture admitting nothing, so its remainder is
everything, while the chain retains only the cycles. A single edge separates them.

And on the hollow triangle they *do* coincide — `by rfl`, because I declared them equal when I
wrote the datum. **That is the tell.**

> **`CompressedPositivity.remainder` is a field. The chain's retained population, the form's
> radical, and the receiver's collapsed population are computed.** Only derived objects can
> coincide non-trivially. A declared field agreeing with a derived one is a choice I made while
> writing the structure, and carries no evidence about the object.

That is the corpus's own authored-partition rule — *a returned partition may not be the preimage of
a field the driver authored* — applied to a structure this development wrote rather than imported.
I nearly recorded my own constructor argument as a structural finding.

```lean
theorem twoDataDeclareDifferentRemainders :
    thetaDatum.remainder ≠ hollowTriangleDatum.remainder
```

Two data over one carrier declare different remainders, so no general statement relates a remainder
to any derived object at all.

## What survives, and it is the part that mattered

```lean
theorem theThreeDerivedObjectsCoincide :
    thetaChain.retained = collapsedPopulation boundaryReading
      ∧ (∀ e, e ∈ thetaChain.retained ↔ e ∈ thetaDatum.radical)
      ∧ thetaDatum.remainder ≠ thetaChain.retained
```

> **Retained, radical, and collapsed are all computed from the object, and they coincide.** That
> three-way weld stands untouched — it was always the derived triple, and the previous record's
> prose described it correctly even where its table did not.

The corrected placement table:

| remainder | position | kind |
|---|---|---|
| obstruction group | the homology `ker g / im f` | derived |
| descent bounded core | the chain's target | derived |
| **compressed-positivity radical** | `ker g` — retained | derived |
| collapsed population | `ker g` — retained | derived |
| ~~compressed-positivity remainder~~ | ~~retained~~ | **declared — withdrawn** |

## On the loop's error rate, since this is the fourth self-correction

Four of eight iterations have closed by repairing my own framing. This one is the sharpest so far:
not a defective definition or a vacuous test, but **a claim of the exact species the project's
grading discipline exists to catch**, made by me, one iteration after I had been applying that
discipline to other people's constructions all day.

The evidence that this is convergence rather than churn is unchanged and still holds: **178
theorems, zero `sorry`, and every correction has narrowed rather than widened the claim.** But the
pattern is worth Brandon seeing rather than my summarising, and the raw record is what he reads.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A form defined on a homology rather than pulled back to it**, carried from iteration 6 — still the only remaining construction that could pay on a nonzero homology. | A boundary-pullback form faithful on a nonzero homology, which iteration 6 forbids. |
| **Audit the rest of the development for declared-versus-derived confusions.** This one was found by chasing a different question. `CompressedPositivity` has three declared fields — `cutoff`, `remainder`, `sign` — and every claim about them should be re-read against this distinction. | A recorded coincidence involving `cutoff` or `sign` that is definitional rather than computed. |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Four theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,291
jobs; `Millennium/` stands at 3,020 lines and **178 theorems, zero `sorry`**. The withdrawal
concerns one table row of one record; the collapsed population's own placement, proved in that
record, stands. Nothing here is a claim about any named conjecture.
