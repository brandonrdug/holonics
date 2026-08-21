# Three more declarations were wearing theorem names

**Date:** 2026-08-20
**Kind:** loop iteration 9. A measured audit, three withdrawals, no new mathematics. It schedules
nothing. [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched.**
**Truth status:** `established-bounded` for the audit; `counterexample` for the three statements
whose prose exceeded their proofs.
**Closes:** *audit the rest of the development for declared-versus-derived confusions*, from
[`2026-08-20_A_DECLARED_FIELD_IS_NOT_A_FINDING.md`](2026-08-20_A_DECLARED_FIELD_IS_NOT_A_FINDING.md).

## The measurement

Run 2026-08-20 over `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/*.lean`:

~~~sh
awk '/^theorem |^@\[simp\] theorem /{name=$0} /:=[ ]*(rfl|Iff\.rfl)[ ]*$/{...}' …/Millennium/*.lean
grep -n -B3 "^  [A-Za-z_]*\.\(orthogonal\|realized_le\|composite_zero\|definite\|form_symm\|sign_unit\) " …
~~~

**Seventeen statements have a `rfl`-class proof.** Fourteen are `@[simp] *_apply` accessors —
API, named as accessors, cited as findings nowhere. **Three are not**, and all three carried
finding-language in their docstrings and in the records that quoted them.

## The three

| statement | proof | what it actually is |
|---|---|---|
| `theCutoffIsInvisibleToTheRemainder` | `C.orthogonal c hc v hv` | **projects the `orthogonal` field** |
| `theFormAlwaysDescendsOnItsRadical` | `fun _ hr w hw => hr.2 w hw` | **unfolds the definition of `radical`** |
| `theChainGluesIffItIsExactAtTheMiddle` | `Iff.rfl` | **definitional** |

Each is true. None is a finding. All three docstrings now open with **DEFINITIONAL** and say what
they project, and the prose in the records that oversold them is corrected below.

### What the records claimed, and what is true

**The cutoff.** The monodromy record said it *"proves the other half: whatever the aperture
admitted contributes nothing to the pairing, which is why the compression loses no positivity."*
It proves nothing — orthogonality of the cutoff is *assumed* when a datum is constructed.
**A real theorem here would say when such a cutoff can be chosen, and no such theorem exists in
this development.** That is now an open item rather than a settled one.

**The radical.** The trichotomy record said *"the form always descends on its own radical, whatever
that radical is. This is the canonical quotient and it needs no hypothesis."* The radical is
*defined* as what pairs to nothing with everything retained, so this is a tautology. **The content
near it is elsewhere and survives**: that the radical is a subgroup (which is why bilinearity had
to be repaired) and that it coincides with the null cone — `theNullConeIsTheRadical`, the integer
Cauchy–Schwarz argument, which is a real proof.

**Gluing and exactness.** The coupling record headlined *"Gluing is exactness."* `toPassage` was
built with `Realized := realized` and `LocallyAdmissible := retained`, so the two vocabularies were
lined up on purpose and `Iff.rfl` records that choice. **It is a naming fact.** The content of that
section is `realized_le_retained` — the containment that follows from the vanishing composite alone
— and that is proved and stands.

## What this does not touch

Every other theorem cited across the eight preceding iterations was checked by this audit and none
of them is of this species. The derived triple — retained, radical, collapsed — remains proved. The
descent trichotomy, the null-cone theorem, the order-blindness biconditional, the split fixed-point
result and the boundary-pullback radical all carry real proofs.

**178 theorems, zero `sorry`, and after this audit three of them are explicitly labelled as
accessors rather than results.** That is a better number than 178 undifferentiated ones.

## On the pattern, now that it has a shape

Five of nine iterations have closed by correcting my own work, and the last two have both been
**the same defect**: prose asserting more than the proof term supports. The first instance was a
declared field mistaken for a derived one; this is three statements whose proofs are projections.

> **The mechanism is identifiable and it is not carelessness in the mathematics.** The Lean is
> correct in every case — the kernel accepted all three. What failed is the *docstring*, written in
> the same pass as the proof and never re-read against it. **A proof term is checked by the kernel;
> a docstring is checked by nobody**, and this development had been treating them as equally
> reliable.

The cheap durable fix is the one applied here: **when a proof is `rfl`, `Iff.rfl`, or a field
projection, the docstring must say so in its first line.** That is mechanically greppable, which is
why the audit above found all three in one command.

## What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **When can an orthogonal cutoff be chosen?** The `orthogonal` field is assumed and no theorem says when a datum with it exists over a given carrier and form. This is now a genuine gap where a settled claim used to be. | A carrier and form admitting no nontrivial orthogonal cutoff, exhibited — which would show the field is not always satisfiable. |
| **A form defined on a homology rather than pulled back**, carried from iteration 6. | A boundary-pullback form faithful on a nonzero homology, which iteration 6 forbids. |
| The long chain and the monodromy reading, carried unchanged since iteration 1. | As recorded in the predecessors. |

## Boundaries

No new theorem was proved this iteration and none is claimed. The library still builds at 3,291
jobs; `Millennium/` is 3,031 lines and 178 theorems with zero `sorry`. The audit covered the eleven
`Millennium/*.lean` files and nothing else — the rest of `soma/formal/` was not read, and no claim
is made about it.
