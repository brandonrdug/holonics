# The typed transport atlas

**Date:** 2026-08-14
**Status:** the active construction plan. Nothing in it is built. It supersedes the sequencing in
`THE_ROADMAP.md` §"THE TRANSPORT ATLAS" and regrades what that section reports.
**Occasion:** Brandon: *"this sounds like a malformed/failed implementation state and you're
identifying the parts of our theories that were neglected. Review and audit, correct the design plan
so that we can implement the correct construction and experiment."*

**The objective it serves is his, 2026-08-14:** *"an atlas of computational structures physically
required for algorithms that enable mathematics proofs, so they'd be like invariant transport
patterns… characteristic properties of group structures and transport dynamics between them, like
chemistry."* Mathematics is the material; Lean is a codec.

Two audits were run. Every figure below is a reader return measured over all 7,516 mathlib files, or
a line re-read at the source by this session — the latter marked **(verified)**. The audits corrected
the assistant on its own account of the emission and on work deposited the same day; those
corrections are §1 and they are why the movements are ordered as they are.

---

## 0. The object, and why both halves of 2026-08-14 failed identically

`H.0362` — registered, `definition`, in this tree before today — already states the object:

> A formulation node is `(D, E, ℋ, v, ρ)`: parameter domain, exact expression or algorithm,
> hypotheses and branch data, denoted invariant, receiver. **An atlas edge is a proved transformation
> carrying one node to another while preserving `v`.**
> *Boundary: shared output does not supply an edge.*

| component | proof emission (`lean_mathematics`) | move species (`move_species`) |
|---|---|---|
| `D` parameter domain | names and explicitness only; **types discarded** | absent |
| `v` denoted invariant | **absent** | absent |
| `ℋ` hypotheses / branch | partial — goal scope only | `focus`, partly |
| `ρ` receiver | implicit | the declared family — the one component both carry |
| **edges** | attempted untyped | **none built** |

> **The two defects are one defect: neither carries `(D, v)`.** An application cannot be typed
> without `D`; a rewrite cannot be typed without `v`.

And the species blocks are **identical observation vectors** — precisely *shared output*, which the
entry's boundary says does not supply an edge. **The atlas rows were built as the one construction
`H.0362` excludes.** The rows are the edges; the blocks are a coarsening over nodes.

**No Rust owner for the node/edge structure exists** (verified). **No registry entry for a
proof-transport atlas exists** (verified). Both are owed; the second is the last movement.

---

## 1. What the audits overturned, including deposits of the same day

### 1.1 The emission's mechanism is not what was reported

The argument list is **not** the goal's binders sprayed at each lemma. It is the *organ's own*
explicit binders **filtered by string membership in the target's binder-name set**
(`lean_mathematics/syntax.rs:343-358`), with unmatched explicit binders **silently skipped rather
than filled with `_`** — so every application carrying an unmatched binder is positionally
misaligned by construction. Arguments appear at all only because corpus and posed theorem share one
`variable` block; rename the corpus's section variables and the generator emits bare declaration
names with **zero** arguments. There are seven argument spellings, not six.

The 213 is closed-form rather than a property of the material:
`3 + 2D + 2DC + 2D + HD + D(D−1)C`, with `D=7, C=3, H=2`. **The 105 rewrite refusals are fully forced
at formation time by information the reader had and discarded.**

### 1.2 Both loss sites are exact, and only one of them is small (verified)

- **`v`:** `result_constructors` (`lean_mathematics/syntax.rs:307-331`) already isolates the
  conclusion via `first_top_level_colon` and walks it at bracket depth zero — and matches exactly one
  character, `'∧'`. `LeanResultConstructor` has one variant. Every `=`, `↔`, `≤`, `<`, `→`, `¬` falls
  into `_ => {}`.
- **`D`:** `syntax.rs:272` is `content.split_once(':')` bound as `(names, _)` — the type discarded by
  name — and `LeanBinderChart` is `{name, explicit}`. Instance binders `[…]` are not parsed at all.

### 1.3 The `D` repair is not small, and the claim that it was is withdrawn

A consumer **cannot** type an application from `DeclaredForm`, for three independent measured
reasons over all 232,037 declarations:

- **93.7% (217,420) inherit binders from a `variable` line** consumed as preamble and absent from
  `statement`.
- `header_terminator` cuts at the first `:=` with **no bracket awareness**, so **5,014 statements
  (2.2%) have unbalanced brackets** and a default-valued parameter swallows the conclusion.
- Only **108,916 (46.9%)** expose exactly one depth-zero relation symbol; 95,149 expose none and
  27,972 expose several. **13,623 (5.9%)** cannot be split into binders-and-conclusion at all.

The one structural reader over `statement`, `statement_grammar.rs`, **refuses this material by
type** — `StatementIsNotAscii`, and **195,292 of 231,056 non-empty statements (84.5%) are
non-ASCII**.

### 1.4 The move-species deed ran on a contaminated reader

This is the reversal that reorders the plan.

- **`MoveAxis::Ascribed` is 31.7% contaminated.** `with`-form tactics take the **scrutinee** as the
  binder and hand the un-cut text to `statement_of`, so the statement becomes the `with` clause.
  10,543 of 33,222 `ascribed = true` records come from tactics carrying no ascription. `rcases` is
  **97.3%** of its own lines.
- **The arrival graph is missing edges by construction.** A destructuring cohort's recruitment goes
  to the **last** binder only — `open_steps.last()` (verified) — contradicting the field's own doc
  (verified). **38,041 of 97,696 steps (38.9%) carry an empty `recruited` map, and such a step can
  never be the target of an arrival.** The `isolated`/`connected` split is therefore inflated.
- **`ProofStep.line` is wrong for 10,261 of 97,696 steps (10.5%)** — `line: form.line + offset`
  (verified) adds an index into a line vector that skips blank, preamble and scoping lines
  (verified). The ablation driver deletes raw source line `step.line`, so roughly one ablation in ten
  deleted the wrong line.
- **`terminally_consumed`, added the same day, is wrong for `with`-form steps**, because it reads
  `local_bindings` for a binder that is a scrutinee.
- **Only 19.6% of statements are the intended shape**; of the non-empty ones, **42.3% are wrong**.
- The parametrised-binder defect founds **one** step at the default grain, not three, and its
  statement is corrupt at the **head**, not truncated at the tail.

---

## 2. The movements, in dependency order

**Named by mechanism, never by ordinal.** Each carries what it builds, what it must return, and the
condition under which it is complete. A movement is complete when its condition holds and its return
is deposited — not when its code compiles.

### THE BINDING IS READ WHERE IT IS WRITTEN — **COMPLETE 2026-08-14**

*The gate for everything that reads through `lean_development`, which is every consumer.*

**Returned.** All four repairs hold; the orbit is
[the record](../research/records/2026-08-14_THE_BINDING_IS_READ_WHERE_IT_IS_WRITTEN_AND_THE_ARRIVAL_GRAPH_NEARLY_DOUBLED.md).

```text
                                                  before        after
  empty recruitment — cannot be an arrival target  99,040        5,098
  statement opens with `with`                      17,147            0
  line does not carry its own former               17,283           26
  statement is bracket-unbalanced                   5,234          192
  arrivals on the geometry file                        25           48
```

**The falsifier passed**: the species populations moved — arrivals nearly doubled. Two consequences
are carried in the record: the earlier species class of ten **does not exist** on the repaired reader
(the canonical focus's species is now a singleton and the honest statement is the partition, 27
blocks against 36), and a control in the species driver was itself malformed — it asked a partition
question of one focus's fiber — and is repaired to compare partitions.

**Build.** Four repairs, each with a measured population behind it:

1. **`with` is a cut, not a pattern.** Found the names *after* `with`; the scrutinee is not a binder
   and the step carries no ascription, so its statement is empty.
2. **A cohort shares its recruitment**, as `ProofStep::recruited`'s own doc already says.
3. **`line` is the true source line**, carried rather than derived from an offset into a filtered
   vector.
4. **The binder pattern respects bracket depth**, which repairs the parametrised-binder statement.

**Must return.** The orbit of each repair on the species deed — before and after, exhibited by name.
Specifically: the **833 declaration names** currently sunk into `local_bindings` reappearing in the
term population; the 38,041 empty `recruited` maps falling; the 10,261 mis-pointed lines resolving to
lines that carry their own former.

**Complete when** all four hold on mathlib and the orbit is deposited.

**Falsifier.** The `isolated`/`connected` populations must move. If they do not, these defects were
not load-bearing for the species reading, and the movement must say so rather than presenting a green
suite as evidence.

### THE CONCLUSION CARRIES ITS RELATION

*`v`. Small, independent of the gate below it, and it alone decides 105 of the 213.*

**Build.** Widen `LeanResultConstructor` and the walk at `syntax.rs:307-331` to return the relation
species the material actually exposes at depth zero. The species are read off the corpus, not
authored: a conclusion the walker cannot classify returns **`Unclassified`** and is counted, never
silently defaulted.

**Must return.** The census of relation species over mathlib's 232,037 declarations, with the
`Unclassified` population named and its size stated.

**Complete when** on the declared corpus the two equational declarations return an equality species
and the five non-equational ones do not, and the `Unclassified` population is returned rather than
absorbed.

**Falsifier.** A conclusion classified as an equality that the kernel then refuses to rewrite by is a
misread `v` and must be exhibited.

### THE DECLARATION IS A FORMULATION NODE

*`D`, and this is the plan's real gate. It was previously sequenced last.*

**Build.** A `FormulationNode` carrying `(D, E, ℋ, v, ρ)` over a Lean declaration, where `D` is the
binder list **with types**, including `variable`-inherited and instance binders. This needs a typed
reader; §1.3 is why no existing carrier suffices.

**Must return.** For a declared sample of mathlib declarations, the node's `D` beside what **Lean
itself** reports for the same declaration, with every disagreement returned by name.

**Complete when** the sample's disagreement population is returned and named. **Not** when it is
empty — an honest partial `D` with its failures exhibited is a completion; a silent one is not.

**Falsifier, and it stops the plan rather than bending it.** If `D` cannot be recovered for a
majority of the declared sample, this movement returns the population it cannot type and the plan
halts here. Proceeding to typed admissibility on a `D` that is mostly absent would produce a green
recognition law over material it never read.

**The instrument is already standing.** The kernel is the second instrument, and using Lean as the
oracle for the reader is the same move as using it to grade a move's load.

### RECOGNITION BEFORE THE RUN

*Admissibility decided from `(D, v)` alone, graded exactly as `elementary_chart` grades its own.*

**Build.** For each candidate edge, decide from the node types whether it is admissible, then grade
what the kernel says:

```text
Decisive          the node types settled it and the kernel agreed
OpenedAndFound    the types admitted the edge and the kernel proved it   -> AN ATLAS EDGE
OpenedAndRefused  the types admitted it and the kernel refused on the mathematics
                                                                          -> a genuine obstruction
Contradicted      the types admitted it and the kernel refused it STRUCTURALLY
                                                                          -> THE NODE MODEL IS WRONG
```

`rw` is the largest edge species in the material — **68,710 of 495,827 tactic-position heads**, the
most-used tactic in mathlib — and is admissible only where `v` is `=` or `↔`.

**Must return.** The four-way population, and for every `Contradicted` the node component that was
read wrong.

**Complete when** `Contradicted` is empty on the declared corpus, or every member of it names its
component.

**Falsifier.** `Contradicted` non-empty and unexplained means the node model is wrong, which is the
outcome this arm exists to make reachable.

### THE ADMITTED PATH IS AN EDGE

*The atlas stops being a partition.*

**Build.** Return the atlas as a graph: nodes are formulation nodes, edges are kernel-proved
transformations with their species named. `H.0362`'s edge species map onto the tactic family and the
mapping types the tactics — `rw` is substitution, `exact`/`apply` are conjugacy, `induction` is
recurrence, and **`linarith`/`ring` are faces, not edges**: they read an ordering and carry no node to
another.

**Must return.** The graph, with the species partition retained as a **coarsening over nodes** and no
longer named as the atlas row.

**Complete when** an edge population exists whose members each name their transformation species and
the invariant they preserve.

### THE ROW IS REGISTERED

**Build.** A registry entry for the proof-transport atlas as a specialisation of `H.0362`, with its
own boundary and falsifier.

**Complete when** it renders and `validate-registry()` passes.

---

## 3. The experiment, and what refutes the whole design

Two arms, one corpus, one theorem, one kernel, run together.

- **the untyped arm:** the inherited cartesian product. Known: 213 paths, 105 rewrite-by-non-equation,
  42 application type mismatch, 4 admitted.
- **the typed arm:** only edges `(D, v)` admit.

**Declared before the run:**

1. The typed arm's **structural** refusals are zero. Any survivor is a `Contradicted` and names its
   component.
2. The typed arm admits **everything the untyped arm admitted**. Typing removes malformed paths; it
   may not remove a working one.
3. The typed arm emits far fewer paths and admits at least as many. Reported as a pair, never as a
   percentage.
4. The typed arm's surviving refusals are **mathematical**, and those are the atlas's genuine
   obstructions.

**What refutes the design:** the typed arm admitting nothing the untyped arm did not, with refusals of
the same species. Then the typing changed nothing and the node model is decoration. This is a real
possible outcome and is why the arms run on one material.

---

## 4. What this plan regrades

- **`THE_ROADMAP.md` §"THE TRANSPORT ATLAS"** — its species figures stand as *what the code returned*
  and no longer as a reading of the material.
- **`2026-08-14_THE_MOVE_SPECIES_IS_A_FIBER…`** — its `isolated`/`unconsumed` correction is itself
  wrong for `with`-form steps.
- **`2026-08-14_THE_KERNEL_IS_THE_SECOND_INSTRUMENT…`** — the ablation deleted the wrong line about
  one time in ten; the `UNDETERMINED` verdict stands with two reasons rather than one.
- **The claim that both `(D, v)` repairs are small** — `v` is; `D` is a typed reader.

## What this plan does not claim

It schedules no capability beyond what the position record admits, grades nothing by a Millennium
row, and asserts no result about mathematics. The audits' figures are agent returns; those marked
verified were re-read at the source, and the rest are evidence for the movement that consumes them to
re-measure. Whether a typed emission changes what the machine can prove is the experiment's question
and is not assumed by the plan.
