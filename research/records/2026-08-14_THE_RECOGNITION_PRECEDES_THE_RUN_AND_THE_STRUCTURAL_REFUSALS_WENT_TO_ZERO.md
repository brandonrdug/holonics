# The recognition precedes the run, and the structural refusals went to zero

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured`; every verdict is a real Lean kernel return with mathlib in scope, both
arms on one corpus, one theorem, one kernel.
**Movements:** *recognition before the run*, *the admitted path is an edge*, and *the row is
registered* — the fourth, fifth and sixth of `blueprint/THE_TYPED_TRANSPORT_ATLAS.md`. **All three
complete; the plan is complete.**
**Driver:** `soma/life/examples/the_recognition_precedes_the_run.rs`.
**Registry:** `H.0481`, *Proof-transport atlas*, a specialisation of `H.0362`.

---

## 1. The experiment

```text
  inherited  emitted 213   admitted 4   structural 147   mathematical 62   placeholder  0
  typed      emitted  94   admitted 4   structural   0   mathematical 60   placeholder 30
```

**All four predictions, declared before the run, hold.**

1. **The typed arm's structural refusals are zero** — `Contradicted` is empty.
2. **It admits everything the inherited arm admitted.** Typing removed malformed paths and no
   working one.
3. **It emits fewer and admits at least as many**: 213 → 94 emitted, 4 → 4 admitted.
4. **Its surviving refusals are mathematical** — 60 of them, and those are the atlas's genuine
   obstructions.

**Not refuted.** The refutation condition was the typed arm admitting nothing new *and* refusing in
the same species; the structural population moved 147 → 0, which is what `(D, v)` is for.

**And the honest bound: the typed arm admits ZERO paths the inherited arm did not.** Typing removed
noise; it did not find new proofs on this material. What changed is that a refusal now means the
mathematics rather than the emission.

## 2. `Contradicted` did its job, twice, and neither time was the node model wrong

The arm exists so a surviving structural refusal can name the component read wrong. It surfaced
**two real defects, neither in `(D, v)`**:

**A third application builder.** With `rw` gated on `v` and the two main applications built in
frame, ten structural refusals survived — *all from the `contrapose!` family*, which builds through
`declaration_application_with_substitute`, a site the grain was never threaded into.
`congestion_exceeds_one_of_subset_load` has a positional domain of ten and was handed five
arguments. Repaired with an in-frame twin.

**Then `ℋ`, and this one is not repairable by threading.** With the arity correct the refusals
persisted, and the emitted text showed why: `… hc hc …`. **`contrapose! hc` changes the type of
`hc`**, and the emission feeds the post-contrapose hypothesis into a slot typed for the
pre-contrapose one. That is `ℋ` — hypotheses and branch data — untracked across a tactic that
rewrites a hypothesis in place.

> **A typed emission may not offer an edge it cannot type.** The family is therefore inadmissible at
> the typed grain, for a stated reason, and that is a **coverage** bound rather than a correctness
> one — the same species of exclusion as a conclusion whose `v` cannot be read.

## 3. The atlas is a graph

`H.0362`: *an atlas edge is a proved transformation carrying one node to another while preserving
`v`*, and *shared output does not supply an edge*. The admitted paths are those edges, and the kernel
is what proves them.

```text
  target node   receiver_load_under_capacity   v = ≤   positional domain 6

  from proportionalFlow_respects_capacity   conjugacy — the node applied in its own frame
       by exact proportionalFlow_respects_capacity demand capacity incident hc hcong m

  from proportionalFlow_respects_capacity   substitution composed with an exterior normalisation
       by simpa using proportionalFlow_respects_capacity demand capacity incident hc hcong m

  from proportionalFlow_respects_capacity   deposit then close — an introduced fact, then a face
       by have generated := proportionalFlow_respects_capacity … ; assumption
       by have generated := proportionalFlow_respects_capacity … ; nlinarith
```

**Four edges, three species, one source node.** That is a graph with a single source and a single
target, and it is very small — the claim is that the object is now an edge population rather than a
partition, not that this population is an atlas of anything yet.

The tactic family types itself against `H.0362`'s edge species: substitution demands `v ∈ {=, ↔}`,
conjugacy applies the node in its own frame, recurrence is induction — **and a closing tactic is a
face, not an edge.** `linarith` and `ring` read an ordering or a normal form; they carry no node to
another.

The species partition is retained as a **coarsening over nodes** and is no longer named as the atlas
row.

## 4. What the plan cost and what it did not buy

Structural refusals 147 → 0; emission 213 → 94; admitted 4 → 4. The machine proves exactly what it
proved before, and now fails for reasons about mathematics. **The 30 placeholder failures are
reported apart from both arms** — they are a consequence of writing `_` where the goal supplies no
binder, not of `(D, v)`, and folding them into either count would flatter the result.

## What this record does not claim

No Millennium row grades it. The atlas is four edges on one corpus. The typed arm's coverage bounds
are two and both are stated: an unclassified `v` is treated as carrying no relation, and a tactic
that rewrites a hypothesis is inadmissible while `ℋ` is untracked. Whether typing helps a machine
prove more than it could is not shown here and was not predicted — what is shown is that the
refusals it now returns are about the mathematics.
