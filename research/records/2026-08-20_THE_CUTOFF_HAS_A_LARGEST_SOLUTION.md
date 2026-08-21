# The cutoff has a largest solution

**Date:** 2026-08-20
**Kind:** loop iteration 10. The question reopened last iteration is answered, with a witness and a
negative. It schedules nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Closes:** *when can an orthogonal cutoff be chosen*, reopened in
[`2026-08-20_THREE_MORE_DECLARATIONS_WERE_WEARING_THEOREM_NAMES.md`](2026-08-20_THREE_MORE_DECLARATIONS_WERE_WEARING_THEOREM_NAMES.md)
after that iteration found the previous answer was a projection of an axiom.

## The answer

```lean
def perp : AddSubgroup V := {c | ∀ v ∈ C.remainder, C.form c v = 0}

theorem theCutoffIsAdmissibleIffInThePerp (K : AddSubgroup V) :
    (∀ c ∈ K, ∀ v ∈ C.remainder, C.form c v = 0) ↔ K ≤ C.perp
```

> **The orthogonality field is not a mystery condition. It has a largest solution — the perp of the
> remainder — and that solution is computed from the form and the remainder rather than declared.**

So the correction from last iteration lands where it should: **the cutoff stays a declared field,
but the range it may be declared within is derived.** A datum always exists (take the zero cutoff);
what the perp decides is whether a *nontrivial* one does.

## Both sides, both witnessed

```lean
theorem theFaithfulFormAdmitsOnlyTheZeroCutoff (htriv : ∀ v ∈ C.radical, v = 0)
    (hfull : C.remainder = ⊤) : C.perp = ⊥
```

> **A faithful form over a full remainder admits only the zero cutoff.** If everything is retained
> and nothing is null, nothing at all is orthogonal to what is retained. **The compression is
> vacuous exactly where the form already separates.**

And on the theta complex, where the form is semi-definite, the opposite:

```lean
theorem theThetaAdmitsANontrivialCutoff :
    ((0,1,-1) : Edges) ∈ thetaDatum.perp ∧ ((0,1,-1) : Edges) ≠ 0
```

The surviving loop can be admitted by an aperture and no positivity is lost.

> **The same radical that decides what may be quotiented decides what may be admitted.** One object,
> two roles — and that is the first time in this development that a single computed object has been
> shown to govern two different declared fields.

## And a separation, made preemptively

`perp` and `radical` are close enough to conflate, and both hypotheses of the negative result are
load-bearing. So:

```lean
theorem theHollowPerpExceedsItsRadical :
    ((1,-1,0) : Cells) ∈ hollowTriangleDatum.perp
      ∧ ((1,-1,0) : Cells) ∉ hollowTriangleDatum.radical
```

> **On the hollow triangle the radical is trivial and the perp is not**, because the remainder is
> only the cycles and plenty is orthogonal to those. A nontrivial cutoff exists where no nontrivial
> radical does.

That distinction is drawn here *before* anything was built on top of it, rather than after — which
is the first time in this loop that the declared-versus-derived discipline has been applied
forward instead of as a repair. `theRadicalIsThePerpInsideTheRemainder` is marked **DEFINITIONAL**
in its own docstring, per the rule set last iteration.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **A form defined on a homology rather than pulled back**, carried from iteration 6 — still the only construction that could pay on a nonzero homology. | A boundary-pullback form faithful on a nonzero homology, which iteration 6 forbids. |
| **Does the perp govern anything else?** It bounds the cutoff and contains the radical. Whether it has a role in the chain picture — for instance whether `perp ∩ retained` is a chain position — is unexamined. | A chain whose retained population meets the perp in something other than the radical. |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

Four theorems audited by `#print axioms`; none depends on `sorryAx`. The library builds at 3,291
jobs; `Millennium/` stands at 3,115 lines and **183 theorems, zero `sorry`**. The negative result
requires **both** a trivial radical and a full remainder — the hollow triangle satisfies the first
and not the second, and the separation theorem exhibits what that costs. Nothing here is a claim
about any named conjecture.
