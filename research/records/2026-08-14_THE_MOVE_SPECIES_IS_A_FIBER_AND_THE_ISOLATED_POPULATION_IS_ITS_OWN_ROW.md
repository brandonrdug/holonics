# The move species is a fiber, and the isolated population is its own row

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `established-bounded [implemented-exact]` for the owner and its returns, every
figure taken this day by running it; `measured` for the two apertures; `interpretation` for reading
a block as an atlas row.
**Occasion:** Brandon ratified the design that transposes Sol's pseudo-autocorrect experiment from
tokens to proof moves, after correcting a plan that had drifted onto kernel verdicts. The objective
it serves is his, 2026-08-14: *"an atlas of computational structures physically required for
algorithms that enable mathematics proofs, so they'd be like invariant transport patterns…
characteristic properties of group structures and transport dynamics between them, like chemistry."*

**Owner:** `crates/holonic-engine/src/move_species.rs`.
**Driver:** `crates/holonic-engine/examples/the_move_species_is_a_fiber.rs`.
**Prior art it transposes:** `soma/life/src/reconstruction_fiber.rs` and
`soma/life/examples/the_token_reconstruction_remains_a_fiber.rs`, and the taxonomy it lands on is
**Information Chemistry**, `research/records/2026-08-12_THE_RECONSTRUCTION_REMAINS_A_FIBER…` §8 —
Brandon's, and its definition is exactly what is built here: *a species is not an immutable lexical
tag; it is a recurring phase distribution of how occurrences enter vertices, transport current,
alter continuations, and couple to other species.*

---

## 0. No new engine, and that is the finding that ordered the build

`receiver_exact_compression::compress` takes `&dyn ObservedSystem`. `ReconstructionSystem` is one
instance of that trait over a token stream: items are a window around each candidate root, inputs
are the left and right step, and **every root observes the same value** so nothing about a
candidate's own spelling can separate it and only its context can.

`MoveSystem` is a **sibling instance** over the arrival graph. The finger-trap rule is satisfied
without exception — the composition was attempted end to end and returned no absent type in the
compression machinery. What it did return is that the token system's successor is a *stream offset*
and a move's must be a *causal arrival*, which is a second implementation of a standing interface
rather than a second engine.

| pseudo-autocorrect (tokens) | this (moves) |
|---|---|
| occurrence = a token at a position in a whole | occurrence = a `ProofStep` in a declaration |
| conduct = stream predecessor and successor | conduct = `DeclaredForm::internal_arrivals`, a step recruiting a name an earlier step founded |
| receiver family `{kind}` → `{kind,weight}` | `{ascribed}` → the five causal axes |
| fiber = block of the stable quotient | fiber = **the species** |
| reflection deposits departed candidates + witnesses | refinement deposits the same |
| `selected correction NONE` | **no canonical method is named** |

Formally the blocks are the Nerode congruence of the declared family over this transition system,
and `compress` already returns the collapsed pairs with their shortest separating words.

---

## 1. What returned, on `Mathlib/Geometry/Euclidean/Triangle.lean`

```text
  moves 78 · arrivals 25 · branch aperture 3 · founding tactics 7
  isolated 45 · connected 33
  focus  declaration 1 step 1, founded by `obtain`, downstream 1 upstream 0
  demand at horizon 1: roots 78 · slots 7 · items 546 · pair chart 148,785

  {ascribed}                                    species 10   conduct blocks 16
  {ascribed,cohort,focus-depth,arrivals-*}      species  2   conduct blocks 23
  {former}                                      species  7   conduct blocks 21
  {former,ascribed,cohort,focus-depth,arrivals-*} species 2  conduct blocks 26
```

**The refinement is the atlas row.** The ascription-only reading holds ten moves together; the
causal panel departs eight and leaves a species of two, with 1,997 collapsed pairs carrying
witnesses. The departed are named with what founded them:

```text
  declaration  1 step 5   obtain
  declaration  1 step 7   have
  declaration  4 step 1   by_cases
  declaration  7 step 4   obtain
  declaration 23 step 0   have
  declaration 24 step 3   intro
  declaration 28 step 0   by_cases
  declaration 30 step 0   by_cases
```

**Four different founding tactics were held in one block and then departed by causal axes alone.**
That is the reading doing the thing it was built for: the class is not the tactic's name, and the
axis that split it is exhibited rather than asserted.

---

## 2. The isolated population is a row, not a filter

**45 of 78 moves in a real geometry file are founded and never used.** They neither feed a later
step nor arrive from an earlier one, so at any horizon they present only the common exposed face and
**no family can separate them**.

This was found the honest way. The first run took the focus as *"the first move in canonical
order"* — deliberately not hand-picked — and landed on an isolated one. Every family then returned
an identical species of 45, and the declared control *the causal panel is not the spelling panel*
**failed**.

> **The reading was right and the focus was uninformative.** A focus with no conduct is a question
> no receiver can answer, and a family returning one block there is reporting the focus rather than
> failing.

The repair is a stated rule, not a hand-pick: the focus is the first move **in the connected
population**, and `MoveComplex::{connected, isolated, reach}` return both populations so the
isolated one is exhibited rather than silently dropped. Its block is a genuine row — *the moves this
body founds and never uses* — and it is the largest single class in the file.

---

## 3. The binder aperture, declared because its orbit is 41% of the material

`lean_development.rs` dropped every **single-character** binder from the step population, with a
stated reason: single-character binders *"are dropped from every recruitment population, so a step
for one could never be arrived at."*

**The conclusion holds; the premise is not what the code does.** The recruitment loop says of
itself that *"the length is not consulted at all"* — the exclusion works because a name that never
becomes a step can never be an arrival *source*, not because recruitment drops it.

**What it costs, measured over all 7,516 mathlib files by an outside scan:**

```text
  binding-tactic lines                     107,502
  binders founded, one character            87,525
  binders founded, longer                  126,856
  share the filter dropped              87,525 / 214,381

  by former (single / longer)
    intro    18,634 / 12,403     <- the majority are single-character
    obtain   15,921 / 24,786
    rintro   13,438 / 14,520
    let      12,506 / 25,685
    suffices  8,701 /  9,692
    rcases    6,918 / 13,016
    have      6,529 / 18,146
    cases     2,799 /  4,147
    by_cases  1,122 /  3,283
    set         957 /  1,178
```

So it is now `BinderGrain::{MultiCharacter, EveryBinder}`, threaded through a new
`read_development_at`. **`MultiCharacter` is the default and `read_development` delegates to it**, so
every figure taken before today still reproduces — the same discipline `ReachOrientation` used when
the orientation axis was recovered. The orbit is exhibited by the driver rather than assumed:

```text
  geometry     MultiCharacter  moves  60 arrivals 16     EveryBinder  moves  78 arrivals 25
  set theory   MultiCharacter  moves  60 arrivals  3     EveryBinder  moves 164 arrivals 42
```

**On the set-theory file the arrival graph is fourteen times larger at the wider grain.** A filter
whose orbit is that size is an aperture, and an aperture must be declared.

**One thing said aloud during the build and withdrawn here:** the fixture's failure was first read
as a nested `by` inside a `have` founding no step. That is false — measured directly, `have uno : T
:= by exact e` founds its step exactly as the plain form does. The single-character binder filter
was the whole cause.

---

## 4. The controls, and which one can fail

| control | verdict | why it is in the list |
|---|---|---|
| the common exposed face collapses every candidate at horizon zero | **holds** | a split there means the reading consumed something it was not handed |
| a refinement is a subset of what it refines | **holds** | a member appearing only under the richer family is not a refinement of anything |
| relabelling every founding tactic moves no block | **holds** | it *cannot* fail — observations enter the quotient by equality — and it is run because the centrifuge failed exactly this at 11 of 13 boundaries when its transport was `popcount(tail ⊕ head)`, a function of bytes rather than identity |
| **the causal panel is not the spelling panel** | **holds**, and **failed once** | if they agree, the causal axes added nothing and the species is the tactic's name in other clothes |

**The crossing arm is reported and graded by nothing**, and the reason is a property of the object
rather than caution: an atlas of *invariant* transport patterns predicts that species **recur**
across subjects, so agreement between two disjoint areas would be evidence for the atlas and not
against it. Measured anyway, since a later reading may want it: geometry returns profile
`(1, 23, 1)` over 78 candidates and set theory `(1, 38, 1)` over 164 — they differ.

---

## 5. What this does not claim

It names no method, ranks nothing, and selects no canonical representative — the species **is** the
block, and its identity is its population together with the family that could not separate it. It is
bounded to one file per reading, and the pair chart is quadratic in the item count, so the scale
route is a fiber per focus with a declared population rather than one compression of the library.
The axes are six and are not asserted complete; the two named panels exist so a reading can be taken
at both and their disagreement measured. Nothing here is graded by a Millennium row, no kernel is in
the loop, and no claim is made that these blocks correspond to the classical method names — the
three built atlas entries (the recognition test for closed-form integration, the residue-preserving
move, the alternation test) remain the ground truth against which a later reading may be compared,
and that comparison has not been run.
