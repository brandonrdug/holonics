# The boundary supplies its own radical

**Date:** 2026-08-20
**Kind:** loop iteration 5. One named item closed with a witness, and all three rows of the
descent trichotomy inhabited on one object. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** the first row of the falsifier table in
[`2026-08-20_THE_FORM_NAMES_ITS_OWN_QUOTIENT.md`](2026-08-20_THE_FORM_NAMES_ITS_OWN_QUOTIENT.md).

## The constraint that shaped the construction

The item asked for a semi-definite datum with a **nonzero radical**, and named the trap: building
the form as a pullback *from the quotient* would make "the form descends to the quotient"
tautological — an authored partition, which the grading discipline refuses. **So the radical had
to come from the object.**

It does. Pair two edge chains by pairing their **boundaries**:

```lean
def pullbackForm : Cells →+ (Cells →+ ℚ) :=
  AddMonoidHom.mk' (fun e => (standardForm (boundary e)).comp boundary) …

theorem thePullbackRadicalIsTheCycles (e : Cells) :
    e ∈ pullbackDatum.radical ↔ e ∈ boundary.ker
```

> **A chain pairs with everything to nothing exactly when its own boundary vanishes.** The radical
> is the cycles — a property the complex already had. Nothing about the quotient entered the
> definition of the form.

And it is not zero: the loop is a cycle, so it is in the radical, and it is not the zero chain.

## All three rows of the trichotomy, inhabited on this one complex

| row | witness | what holds |
|---|---|---|
| **outside** the radical | a single edge `(1,0,0)` — pairs with itself to `2` | the form does not descend |
| **strictly inside** | twice the loop, `⟨(2,2,2)⟩` | the form descends; the loop class is null and survives |
| **the radical itself** | the cycles | the form descends and the null-cone criterion required for a faithful quotient holds |

```lean
theorem theTopIsNotInTheRadical : ¬ (∀ r ∈ (⊤ : AddSubgroup Cells), … = 0)
theorem theDoubledLoopIsStrictlyInside : (∀ r ∈ AddSubgroup.zmultiples (2,2,2), …) ∧ (1,1,1) ∉ …
theorem theCyclesHaveTheRadicalNullCriterion : ∀ v ∈ …remainder, … → v ∈ …radical
```

The middle row was the one with no instance anywhere in the tree after iteration 4. It has one
now, and the witness is arithmetic: **`(1,1,1)` is null and is not an integer multiple of
`(2,2,2)`**, so quotienting by the doubled loop leaves a null class standing.

> **Together with iteration 4's theorem, the picture is complete: the faithful case forces the
> degenerate row, the semi-definite case admits all three, and the radical is the only quotient
> that lands in the good one.**

## What this does not do

One complex, one form. The trichotomy is general; the instance is not, and nothing here says which
row a given problem falls in — only that none of the three is empty.

The complex is still the hollow triangle, so its **realized** population from the chain of
iteration 3 remains trivial. This iteration supplies a nonzero *radical*, not a nonzero realized
population inside one. A chain over this complex whose incoming transport has image equal to the
cycles would supply both at once, and would be the filled triangle.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **The filled triangle**, whose second boundary has image exactly the cycles — the one object where the realized population, the radical, and the faithful quotient coincide. Its homology is trivial, so the weld there is faithful on a zero group; the informative version needs a complex with both a filled cell and a surviving loop. | A complex with a filled cell and a nonzero first homology whose boundary image is not in the pullback radical. |
| **The collapsed population as a chain position**, carried unchanged. | A receiver quotient that is not the outgoing map of any chain. |
| The long chain and the monodromy reading, carried unchanged. | As recorded in the predecessors. |

## Boundaries

Five theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,289
jobs; `Millennium/` stands at 2,629 lines and **151 theorems, zero `sorry`**. The complex carries
no geometry and no claim about any named conjecture. The vertex pairing used inside the pullback is
the standard coordinate one, chosen because it is definite — a degenerate vertex pairing would make
the radical larger than the cycles and the theorem would fail, which is the stated boundary of the
form rather than a hidden assumption.
