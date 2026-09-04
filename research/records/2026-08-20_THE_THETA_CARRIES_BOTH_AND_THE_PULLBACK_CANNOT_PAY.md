# The theta carries both, and the pullback cannot pay

**Date:** 2026-08-20
**Kind:** loop iteration 6. One named item closed with a witness, and one negative result that
redirects the search. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** the first row of the falsifier table in
[`2026-08-20_THE_BOUNDARY_SUPPLIES_ITS_OWN_RADICAL.md`](2026-08-20_THE_BOUNDARY_SUPPLIES_ITS_OWN_RADICAL.md).

## The object that carries both

Every previous instance had one or the other. The hollow triangle: nonzero homology, trivial
realized population. The filled triangle: nonzero realized population, no homology. **The theta
complex has both** — two vertices joined by three edges, with one of the three loops filled.

```lean
theorem theRealizedIsNonzero : ((1,-1,0) : Edges) ∈ thetaChain.realized ∧ ((1,-1,0) : Edges) ≠ 0
theorem theSurvivingLoopIsNotRealized : ((0,1,-1) : Edges) ∉ thetaChain.realized
theorem theThetaHomologyIsNontrivial : ¬ Subsingleton thetaChain.toPassage.ObstructionGroup
```

The filled cell's boundary is a real edge chain; the second and third edges close a loop no face
fills. So:

```lean
theorem theNonzeroRealizedLiesInTheRadical :
    ∀ r ∈ thetaChain.realized, ∀ w ∈ thetaDatum.remainder, thetaDatum.form r w = 0
theorem theFormDescendsOntoTheThetaHomology : …
```

> **The descent criterion holds with a nonzero realized population, and the population is what the
> complex realizes rather than a subgroup picked by hand.**

That is the strengthening the item asked for. Iteration 5 instantiated the trichotomy's middle row
with `⟨(2,2,2)⟩`, an authored subgroup; this one uses `im ∂₂`, which the object supplies.

## And the negative that redirects the search

```lean
theorem thePullbackVanishesOnCycles {x : Edges} (hx : d1 x = 0) (y : Edges) :
    thetaDatum.form x y = 0

theorem theDescendedFormIsNotFaithful :
    thetaDatum.sign * thetaDatum.form (0,1,-1) (0,1,-1) = 0 ∧ (0,1,-1) ∉ thetaChain.realized
```

> **Every cycle is null under a boundary pullback, and a homology class is a cycle. So the
> descended form has null classes wherever the homology is nonzero — and here it is, witnessed by
> the surviving loop.**

**A form that pays on a homology cannot be a boundary pullback.** The pullback supplies the radical
and cannot supply the pay; both facts are about the same form and they are in tension by
construction.

That is a real constraint on the search rather than a failure of this object. It says where **not**
to look, and the classical answer to where one does look is a pairing defined on the homology
itself — an intersection or cup product — which is a different construction entirely and is not
built here.

## The arc across six iterations, stated once

| | object | realized | homology | form pays |
|---|---|---|---|---|
| doubling chain | any abelian group | `2G` | **trivial** | question vacuous |
| hollow triangle | 3 vertices, 3 edges | **trivial** | `ℤ` | **yes**, but degenerately |
| theta complex | 2 vertices, 3 edges, 1 face | `ℤ` | `ℤ` | **no** — pullback is blind to cycles |

The three cases are exhaustive for what has been built, and together they say: **the weld needs a
form that is neither faithful on the whole retained population (which forces triviality) nor a
boundary pullback (which forces blindness).** That is a narrow target and it is now named.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A form defined on the homology itself**, not pulled back to it — the intersection-pairing shape. This is the only remaining construction that could pay on a nonzero homology, and building it as a pullback from anything would be an authored partition. | A form on a nonzero homology that is a boundary pullback and is faithful — which the theorem above forbids, so a counterexample would refute the theorem. |
| **The collapsed population as a chain position**, carried unchanged through four iterations without being addressed. | A receiver quotient that is not the outgoing map of any chain. |
| The long chain and the monodromy reading, carried unchanged. | As recorded in the predecessors. |

## Boundaries

Eight theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,290
jobs; `Millennium/` stands at 2,822 lines and **165 theorems, zero `sorry`**. The theta complex is
a bare integer chain complex with no geometry and no claim about any named conjecture. The
"exhaustive" in the arc table means exhaustive over what this development has built, not over
possible objects.
