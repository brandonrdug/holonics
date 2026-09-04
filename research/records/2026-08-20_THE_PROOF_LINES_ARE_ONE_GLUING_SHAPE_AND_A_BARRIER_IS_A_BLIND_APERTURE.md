# The proof-lines are one gluing shape, and a barrier is a blind aperture

**Date:** 2026-08-20
**Kind:** formal foundation deposit. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** This is exterior mathematical material for
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md),
whose Deed M2 names *Lean exterior testimony* as one of the mathematics codec's return faces.
**It changes no engine source, adds no owner, and proposes no driver.** The active deed remains
W1; M0–M3 remain blocked until W5 passes.
**Truth status:** `proved-derived` for every Lean theorem, each kernel-checked and audited to be
free of `sorryAx`; `established-bounded` for the survey; `interpretation` for the readings;
`open` for every named conjecture, none of which is formalized here.
**Companion:** the laws are in [`research/equation-atlas/`](../equation-atlas) — nine equations
and seven relations appended, each citing its Lean owner.

## Provenance

**Brandon's, directly (2026-08-20).** That ideas are not taken to the engine reactively — they
are theorised outside it and adapted into the mathematics first, and the Information Engine does
not cater to mathematics proofs, so prescribing mechanisms there ahead of time helps nothing.
That the previous turn proposed an engine extension **without relating it to the active
blueprints**, which is the failure. That the Lean collections in both repositories should be
reviewed. That the problems are currently *"just in your 'mind'"* and the gestures are *"not
concrete or yours to play with yet"*, so **the foundations of the proof-lines should be
established holistically** and iterated from there. That labels depending on people's names
should be avoided except as an aside, and that **word composition** for theorems and transport
mechanisms makes it easier to cut through imposed semantics. That the task cannot be failed:
what is being done is chipping away at potential configurations, and breadth outranks
self-doubt.

**Assistant, this record.** The survey; the choice of the gluing passage as the shared shape; the
blind-aperture theorem and its two companions; the composed vocabulary; and every reading in §4.

---

## 1. The survey, and Brandon's assumption was wrong in the useful direction

**`established-bounded`, measured 2026-08-20.**

He expected *"we have no formalization of the Millennium problems aside from probably just RH."*
The frozen laboratory holds **eight**, at `a07ff376:src/labyrinth/mathematics/lean/`:
`App_RH`, `App_Hodge`, `App_PvsNP`, `App_NavierStokes`, `App_YangMills`, `App_TwinPrimes`,
`App_Goldbach`, `App_Collatz`, plus `Application_TEMPLATE.lean` and 87 Lean files in total.

**Their honesty is their strength and their limitation is structural.** Each carries an explicit
`★ WHAT THIS DOES NOT PROVE` block — `App_Hodge` states plainly that it has *"no variety, no de
Rham/Dolbeault cohomology, no `(p,p)` Hodge type, no intersection theory, no Lefschetz"* and that
its `founded_by` is *"an ABSTRACT span-membership predicate over our adapter, not the cycle class
map of an actual variety."* That is exactly the right disclosure. But **every one of them is
standalone Lean 4 with no mathlib**, by declared protocol, so none can reach a real object.

This repository has the opposite shape: three mathlib-backed projects under `soma/formal/`, of
which `elementary-holonics` already aliases mathlib's `RiemannHypothesis` in `RH/Statement.lean`
— **one line, connected to real mathematics, and nothing else.**

> **So the gap was not a missing formalization. It was that the eight holonic readings and the one
> real statement are in different projects and cannot see each other.** What is deposited here is
> the join: the shared shape, on mathlib, with the composed vocabulary certified against the
> standard statement rather than asserted beside it.

## 2. What was built

`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/` — 898 lines, five files, wired
into the library root. **`lake build` completes; 44 theorems; zero occurrences of `sorry`; every
audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, and none on
`sorryAx`.**

| file | what it discharges |
|---|---|
| `Gluing.lean` | the gluing passage; gluing ⟺ the obstruction population is empty; the additive case where the obstruction is a **quotient group**; a candidate reached only in multiple `k` is a torsion class of order dividing `k`; a pairing with a one-point null cone separates every nonzero object |
| `Turn.lean` | the whole turn is what the exponential deletes; the real chart has no kernel and keeps only the sign; both nested-radical branches are half-angle laws; the golden ratio is twice a cosine of the fifth turn and solves the period-two relation; the two period-two values differ by exactly one |
| `Hand.lean` | the hand as one half-turn per irreducible; it composes multiplicatively; a square is flat; the running sums; **a magnitude bound implies its order bound** |
| `Seam.lean` | both reflections are involutions; the plain one fixes only the half; **the critical line is exactly the fixed locus of the conjugate reflection**; the completed comb's reflection law; **the composed statement is mathlib's `RiemannHypothesis`** |
| `Lines.lean` | **a blind family carries no verdict**; a separating family is not blind; adjoining a reading breaks blindness; the index of eight lines, with its counts checked by `decide` |

**Seven open statements are named `Prop`s that are never discharged**, following the laboratory's
own protocol: an open thing is stated and not claimed. One candidate `Prop` was **removed during
the build** because it could not have failed — a vacuously true proposition reads as an open
statement while carrying nothing, which is worse than saying nothing.

## 3. The three results worth carrying

### 3.1 The dialect is certified, not asserted

```lean
theorem theSeamIsTheFixedLocusOfTheConjugateReflection (s : ℂ) :
    conjugateReflection s = s ↔ s.re = 1 / 2

theorem theComposedStatementIsTheStandardOne :
    EveryModeSitsOnTheSelfConjugateSeam ↔ RiemannHypothesis
```

**The critical line is not chosen; it is the fixed locus of an involution the comb already
carries** — and the involution is the *conjugate* reflection `s ↦ 1 − s̄`, not the plain one,
which fixes only the single point. The placement doctrine — *placement is the fixed locus of the
involution a realizer induced* — is discharged rather than restated.

And the second theorem is what makes the renaming legitimate. **A composed vocabulary is only
worth having if the renamed statement is provably the same statement**, and here that is a
kernel-checked biconditional against mathlib rather than a claim in prose.

### 3.2 A barrier is a blind aperture, and that is now a theorem

```lean
theorem blindFamilyCarriesNoVerdict (P : X → Prop) (h : R.Blind P) :
    ¬ ∃ verdict : (R.Index → V) → Prop, ∀ x : X, P x ↔ verdict (fun i => R.read i x)
```

A **receiver family** is a declared indexed set of readings. It is **blind** to a property when
some pair differs in the property and no reading separates them. The theorem: *nothing computed
from a blind family's readings decides the property.*

> **This is the general form of every modern barrier result, and the field has no vocabulary that
> makes them one class.** Relativization, the large-and-constructive barrier, the sieve's parity
> obstruction, and the averaged-equation construction are all statements that a declared aperture
> is blind — never that a question is hard. Each is currently read as a local disappointment.

Two companions are also discharged, and they keep the frame from being an excuse: a family that
separates every distinguished pair **is not blind**, so "the aperture is blind" is a claim
someone has to earn; and **adjoining one separating reading breaks blindness**, which is what a
historical break actually did.

### 3.3 The refuted claim was strictly stronger, and that is typed

```lean
theorem theMagnitudeClaimIsStrictlyStronger :
    TheOrientationSumStaysUnderItsRoot → TheOrientationCancelsToSquareRoot
```

The magnitude claim (*the running orientation sum never leaves its own root*) is **false** —
refuted 1985. The order claim is **open** and is equivalent to the placement. The implication
runs one way, so **the refutation costs the open statement nothing.** The split-and-hand
discipline is a typed implication here rather than a caution in prose.

The same pattern holds for the hand's running sum: the magnitude form (*never turns positive*) is
false, least counterexample 906150257; the order form is open. Both are named in `Hand.lean`.

## 4. The reading the index encodes

**`interpretation`.** `Lines.lean` carries the eight lines as data, and its cold-audited
`theIndexCountsFourOpenLinesWithNoObstructionGroup` checks by computation that **six are open and
four of those have no obstruction-group flag** — the Riemann, Navier–Stokes, Yang–Mills, and
verify-to-search rows. This is a count of declared booleans, not evidence that the named problems
have or lack mathematical obstruction groups.

> Where an obstruction group exists, "how much does the gluing fail" is a question that can be
> posed, and the line can be chipped at. Where none does, only "does it" can be posed, and there
> is nothing to chip. **That is the difference this framework is pointing at, and it is why the
> most developed attack on the verify-to-search gap is an attempt to supply the missing group.**

The two closed rows are the ones where a realizer was built: a flow that exhibits what it cut,
and an ample class whose pairing has a one-point null cone. The function-field row is marked
*closed where the shape degenerates*, because what makes it closed is the **absence of a place**
— every local factor there is algebraic and the argument runs in finite dimensions.

## 5. What is not here

**No named conjecture is formalized.** `Seam.lean` carries the only genuine statement, because
mathlib supplies the comb; the other seven rows name shapes and carry no mathematics about their
subjects. A row in the index is not evidence and may not be cited as movement on anything.

The abstract structures are **faithful to the shape and empty of the content**, which is the same
disclosure the laboratory's own application files make and the reason they were worth reading.

**Nothing here touches the engine.** No owner was added, no driver proposed, no `crates/` or
`soma/{body,membrane,abi,surface,mount,life}` source changed. The only tree touched under
`soma/` is `soma/formal/`, which is exterior formal material.

## 6. What is owed next, with falsifiers

**`open`. None is scheduled.**

| owed | falsifier |
|---|---|
| **The bridge in `Seam.lean`** — the classical equivalence between the placement of the modes and the cancellation of the hand. It is a real theorem, absent from mathlib, and formalizing it would make the two charts one object here. | A formalization whose two sides are not interderivable. |
| **An honest passage instance for a real object.** Every additive-passage theorem is discharged in the abstract and instantiated nowhere. The first real instance available is a finite simplicial one — the hollow tetrahedron the engine already computes — and it would exercise `ReachedOnlyInMultiple` on material rather than on a hypothesis. | An instance whose computed obstruction group disagrees with the engine's returned obstruction species. |
| **The archimedean condensation's remainder.** Recorded in `Seam.lean` as an observation with no `Prop`, because the regularized product has no definition in scope and a `Prop` that could not fail is worse than none. | A definition of the regularized product under which the discarded part is exhibited. |
| **The parity obstruction as an instance of the blind-aperture theorem.** Named as a relation in the atlas and `interpretation` only; the classical sieve theorem is not derived from the general one. | A derivation, or a demonstration that the sieve family is not blind in this frame's sense. |

## 7. Boundaries

Every Lean theorem cited here is kernel-checked and was audited by `#print axioms`; the audit
block is committed inside `Gluing.lean` so it reruns on every build. `theLines` is data and
carries no mathematical claim. The laboratory survey is a measurement of one commit, `a07ff376`,
and its application files are read for provenance only — none is authority. The composed names
are this record's and Brandon's naming ruling; the classical labels are carried as asides on
every declaration so that nothing here becomes unreadable to someone outside this project.
