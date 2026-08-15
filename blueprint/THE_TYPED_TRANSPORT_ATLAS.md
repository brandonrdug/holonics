# The typed transport atlas — the corrected construction plan

**Date:** 2026-08-14
**Status:** plan, not a return. Nothing here is built. It supersedes the sequencing in
`THE_ROADMAP.md` §"THE TRANSPORT ATLAS" and regrades what that section reports.
**Occasion:** Brandon: *"this sounds like a malformed/failed implementation state and you're
identifying the parts of our theories that were neglected. Review and audit, correct the design plan
so that we can implement the correct construction and experiment."*

Two audits were run and both corrected the assistant. Every figure below is either a reader return
measured by an audit over all 7,516 mathlib files, or a line this session verified directly; the
verified ones are marked.

---

## 0. The neglected theory, and why both halves failed identically

`H.0362` — **registered, `definition`, in this tree since before today** — states the object:

> A formulation node is `(D, E, ℋ, v, ρ)`: parameter domain, exact expression or algorithm,
> hypotheses and branch data, denoted invariant, receiver. **An atlas edge is a proved
> transformation carrying one node to another while preserving `v`.**
> *Boundary: shared output does not supply an edge.*

Measured against what was built on 2026-08-14:

| component | proof emission (`lean_mathematics`) | move species (`move_species`) |
|---|---|---|
| `D` parameter domain | names and explicitness only; **types discarded** | absent |
| `v` denoted invariant | **absent** | absent |
| `ℋ` hypotheses / branch | partial (goal-scope only) | `focus`, partly |
| `ρ` receiver | implicit | the declared family — the one component both carry |
| **edges** | attempted untyped | **none built** |

> **The two defects are one defect: neither carries `(D, v)`.** The emission cannot type an
> application without `D` and cannot type a rewrite without `v`; the species reading classifies moves
> by situation alone and denotes no invariant at all.

And the species blocks are **identical observation vectors** — which is precisely *shared output*,
the thing `H.0362`'s boundary says does not supply an edge. **The atlas rows were built as the one
construction the entry excludes.** The rows are the edges; the blocks are a coarsening over nodes.

**No Rust owner for `H.0362`'s node/edge structure exists** (verified). **No registry entry for a
proof-transport atlas exists** (verified). Both are owed.

---

## 1. What the audits overturned, including today's deposits

**These correct claims this session deposited. They are listed first because the plan below is a
consequence of them.**

### 1.1 The emission's mechanism is not what was reported

The argument list is **not** the goal's binders sprayed at each lemma. It is the *organ's own*
explicit binders **filtered by string membership in the target's binder-name set**
(`lean_mathematics/syntax.rs:343-358`), with unmatched explicit binders **silently skipped rather
than filled with `_`** — so every application carrying an unmatched binder is *positionally
misaligned by construction*. Arguments are produced at all only because corpus and posed theorem
share one `variable` block; rename the corpus's section variables and the generator emits bare
declaration names with **zero** arguments.

The 213 is closed-form, not an accident of material:
`3 + 2D + 2DC + 2D + HD + D(D−1)C` with `D=7, C=3, H=2`. There are **seven** argument spellings, not
six. **The 105 rewrite refusals are fully forced at formation time by information the reader had and
discarded.**

### 1.2 The two loss sites are exact — and only one of them is small (verified)

- **`v`:** `result_constructors` (`lean_mathematics/syntax.rs:307-331`) already isolates the
  conclusion via `first_top_level_colon` and walks it at bracket depth zero — and matches exactly
  one character, `'∧'`. `LeanResultConstructor` has a single variant. Every `=`, `↔`, `≤`, `<`, `→`,
  `¬` falls into `_ => {}`. **Widening this is a match arm.**
- **`D`:** `syntax.rs:272` is `content.split_once(':')` bound as `(names, _)` — the type is discarded
  by name — and `LeanBinderChart` is `{name, explicit}`. Instance binders `[…]` are not parsed at
  all, so any arity computed from `binders` is wrong for a declaration carrying instances.

### 1.3 The `D` half is **not** a small repair, and the earlier claim that it was is withdrawn

The reader audit answers the deciding question directly: **a consumer cannot type an application
from `DeclaredForm`.** Three independent reasons, each measured over all 232,037 declarations:

- **93.7% of declarations (217,420) inherit binders from a `variable` line** that is consumed as
  preamble and appears in `statement` nowhere.
- `header_terminator` cuts at the first `:=` with **no bracket awareness**, so **5,014 statements
  (2.2%) have unbalanced brackets** and default-valued parameters swallow the conclusion.
- Only **108,916 of 232,037 (46.9%)** expose exactly one depth-zero relation symbol in their
  conclusion; 95,149 expose none and 27,972 expose several. And **13,623 (5.9%) cannot even be split
  into binders-and-conclusion** by a depth-zero colon scan.

The one structural reader over `statement` — `statement_grammar.rs` — **refuses this material by
type**: `StatementIsNotAscii`, and **195,292 of 231,056 non-empty mathlib statements (84.5%) are
non-ASCII**.

> **A typed reader is genuinely owed. It is the plan's real gate, and it was previously mis-scoped as
> a side item.**

### 1.4 Today's move-species deed ran on a contaminated reader

This is the reversal that reorders the plan.

- **`MoveAxis::Ascribed` is contaminated.** `with`-form tactics take the **scrutinee** as the binder
  and hand `statement_of` the un-cut text, so the statement becomes the `with` clause. **10,543 of
  the 33,222 `ascribed = true` records (31.7%) come from tactics that carry no ascription at all.**
  `rcases` is **97.3%** of its own lines.
- **The arrival graph is missing edges by construction.** A destructuring cohort's recruitment is
  given to the **last** binder only — `open_steps.last()` (verified) — contradicting the field doc's
  *"each becomes its own step sharing one statement and one recruitment"* (verified). **38,041 of
  97,696 steps (38.9%) carry an empty `recruited` map, and a step with an empty map can never be the
  target of an arrival.** So the `isolated`/`connected` split the species reading is built on is
  inflated by a reader defect.
- **This session's `terminally_consumed` repair is itself wrong for the `with`-form steps**, because
  it reads `local_bindings` for a binder that is a scrutinee, whose count reflects the hypothesis's
  uses.
- **`ProofStep.line` is wrong for 10,261 of 97,696 steps (10.5%)** — `line: form.line + offset`
  (verified) adds an index into a line vector that `continue`s past blank, preamble and scoping lines
  (verified), so it assumes a contiguity the material does not have. **`the_kernel_decides_which_moves_are_load_bearing.rs`
  deletes raw source line `step.line`, so roughly one ablation in ten deleted the wrong line.**
- **Only 19.6% of the 97,696 statements are the intended shape**; of the 33,222 non-empty ones,
  **42.3% are wrong**.
- And the parametrised-binder defect this session reported founds **one** step at the default grain,
  not three — `MultiCharacter` drops the single-character parameters — and the recorded statement is
  corrupt at the **head**, not truncated at the tail.

---

## 2. The plan, in dependency order

**Stage 0 was previously Stage 5. That is the correction.**

### Stage 0 — repair the reader, because everything reads through it

Each item is a measured population, not a tidy-up.

1. **`with` is a cut, not a pattern.** Found the names *after* `with`, not the scrutinee before it;
   the ascription is absent, so the statement is empty. Removes 10,543 mis-bound steps and returns
   **833 declaration-to-declaration edges** currently deleted into `local_bindings`.
2. **The cohort shares its recruitment**, as its own doc already says. Removes 38,041 structurally
   unreachable steps.
3. **`line` is the true source line.** Carry it rather than deriving it from a filtered offset.
4. **The binder pattern respects bracket depth**, which repairs the parametrised-binder statement.
5. **Every repair is graded by its orbit**: re-run the species deed before and after and exhibit what
   moved. A repair wave reporting no movement has done bookkeeping and must say so.

**Falsifier for Stage 0:** the `isolated`/`connected` populations must move. If they do not, the
reader defects were not load-bearing for the species reading and this stage is bookkeeping.

### Stage 1 — the node, `(D, E, ℋ, v, ρ)`, as an owner

A `FormulationNode` over a Lean declaration:

| component | source | state |
|---|---|---|
| `D` | binder list **with types**, including `variable`-inherited and instance binders | **owed — the gate** |
| `E` | the term or tactic realising it | present |
| `ℋ` | premises and branch/goal-scope | partial |
| `v` | the conclusion **and its relation species** | one match arm (`§1.2`) |
| `ρ` | the declared receiver family | present |

`v` first — it is small, it is independent of the `D` gate, and it alone decides 105 of the 213.

### Stage 2 — admissibility, recognised before the kernel runs

Mirror `elementary_chart`'s discipline exactly: decide from `(D, v)` which edge species a declaration
can carry, and grade the recognition against what the kernel then says.

```text
Decisive          the node types settled it, the kernel agreed
OpenedAndFound    the types admitted the edge and the kernel proved it   -> AN ATLAS EDGE
OpenedAndRefused  the types admitted it, the kernel refused on the mathematics
                                                                          -> a genuine obstruction
Contradicted      the types admitted it and the kernel refused it STRUCTURALLY
                                                                          -> THE NODE MODEL IS WRONG
```

**`Contradicted` must be empty.** Every surviving `Invalid rewrite argument` or `Application type
mismatch` means a node component was read wrong, and the driver must name which. That is what makes
the recognition falsifiable rather than decorative.

`rw` is the largest edge species in the material — **68,710 of 495,827 tactic-position heads**, the
most-used tactic in mathlib — and it is admissible only where `v` is `=` or `↔`.

### Stage 3 — the atlas is a graph

Every admitted path is an **edge**: a proved transformation carrying the lemma node to the goal node
preserving `v`, with its species named. `H.0362`'s edge species — substitution with Jacobian,
continuation, functional equation, recurrence, transformation, conjugacy — map onto the tactic
family, and the mapping types the tactics: `rw` is substitution, `exact`/`apply` are conjugacy,
`induction` is recurrence, and `linarith`/`ring` are **faces, not edges** — they read an ordering,
they carry no node to another.

The species partition is retained as a **coarsening over nodes**, useful for navigation, and is no
longer called the atlas row.

---

## 3. The experiment, and what would refute the whole design

Two arms, one corpus, one theorem, one kernel.

- **A, inherited:** the untyped cartesian product. Known: 213 paths, 105 rewrite-by-non-equation, 42
  application type mismatch, 4 admitted.
- **B, typed:** only edges `(D, v)` admit.

Declared before the run:

1. **B's structural refusals are zero.** Any survivor is a `Contradicted` and names its component.
2. **B admits everything A admitted.** Typing removes malformed paths; it may not remove a working
   one.
3. **B's emitted population is far smaller and its admitted count is unchanged or larger.** Reported
   as a pair, never as a percentage.
4. **B's surviving refusals are mathematical**, and those are the atlas's genuine obstructions.

**What refutes the design:** if B admits nothing A did not and its refusals are the same species as
A's, the typing changed nothing and the node model is decoration. That is a real possible outcome and
it is the reason the arms are run together on one material.

---

## 4. What is regraded, and what is withdrawn

- **`THE_ROADMAP.md` §"THE TRANSPORT ATLAS"** — the species figures stand as *what the code returned*
  and no longer as a reading of the material. `Ascribed` is 31.7% contaminated and the
  `isolated`/`connected` split is inflated by the cohort defect.
- **`2026-08-14_THE_MOVE_SPECIES_IS_A_FIBER…`** — §2's `isolated`/`unconsumed` correction is itself
  wrong for `with`-form steps and must carry that.
- **`2026-08-14_THE_KERNEL_IS_THE_SECOND_INSTRUMENT…`** — the ablation deleted the wrong line about
  one time in ten. The `UNDETERMINED` verdict stands, and the reason it is undetermined is now two
  reasons rather than one.
- **The claim that both `(D, v)` repairs are "small and located"** is withdrawn. `v` is; `D` is a
  typed reader.

## What this plan does not claim

It schedules nothing beyond what the position record admits, grades nothing by a Millennium row, and
asserts no result about mathematics. The audits' figures are agent returns; those marked *verified*
were re-read at the source by this session, and the rest are evidence to be re-measured by the stage
that consumes them.
