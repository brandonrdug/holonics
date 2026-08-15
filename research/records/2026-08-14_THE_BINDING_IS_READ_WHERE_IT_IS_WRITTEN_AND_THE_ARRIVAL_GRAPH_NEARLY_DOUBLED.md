# The binding is read where it is written, and the arrival graph nearly doubled

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured` throughout — every figure is a reader return over all 7,516 mathlib
files, taken before and after the repair by the same instrument.
**Movement:** *the binding is read where it is written*, the first of
`blueprint/THE_TYPED_TRANSPORT_ATLAS.md`. **Complete:** the four repairs hold and the orbit is below.
**Owner:** `crates/holonic-engine/src/lean_development.rs`.
**Instrument:** `crates/holonic-engine/examples/the_binding_is_read_where_it_is_written.rs`, written
and run **before** the repair so the repair had something to move.

---

## 1. The orbit

All figures at `BinderGrain::EveryBinder`, which is the grain the consuming drivers use.

```text
                                                  before        after
  proof steps                                    174,683      190,209
  empty recruitment — cannot be an arrival target  99,040        5,098
  statement opens with `with`                      17,147            0
  line does not carry its own former               17,283           26
  statement is bracket-unbalanced                   5,234          192
```

**And the population the species reading sits on:**

```text
                    before   after
  moves                 78      89
  arrivals              25      48        <- the arrival graph nearly doubled
  connected             33      53
  isolated              45      36
  unconsumed            15      10
```

**The falsifier passed decisively.** The movement was declared complete only if these moved; had they
not, the four defects would not have been load-bearing for the species reading and the movement would
have had to say so. Arrivals went from 25 to 48 on one file — the edges were missing by construction,
exactly as the audit said.

## 2. The four repairs

**`with` is a cut, not a pattern.** `rcases hxy with ⟨a, b⟩` founds `a` and `b`; `hxy` is the
**scrutinee**, a term the step recruits and never a name it founds. Reading the scrutinee as the
binder put its head symbol into `founded`, sending later uses into `local_bindings` instead of
`recruited`, and handed the `with` clause back as the step's statement on a tactic carrying no
ascription. That population is now **zero**.

**A cohort shares its recruitment.** `open_steps.last()` gave the recruitment to the final push
alone, contradicting `ProofStep::binder`'s own doc — *"each becomes its own step sharing one statement
and one recruitment"*. Every step of the innermost cohort now receives it, and the population that
could never be an arrival **target** fell from 99,040 to 5,098.

**`line` is the true source line.** `form.line + offset` added an index into a vector that skips
blank, comment-only, preamble and scoping lines to the declaration's own line, assuming a contiguity
the material does not have. The source line is now carried. 17,283 → 26.

**The binder pattern respects bracket depth.** The ascription colon is the first `:` at depth zero
over `()`, `{}`, `[]` **and `⟨⟩`, so a binder carrying its own parameters keeps its colons inside the
group. 5,234 → 192.

Two functions the repairs superseded — `split_before_with` and `statement_of` — were **removed, not
deprecated**, per the standing rule; git history is their recovery surface.

---

## 3. What the repair did to the readings that stood on it

### The species figures were substantially artifacts, and this supersedes them

`2026-08-14_THE_MOVE_SPECIES_IS_A_FIBER…` reported a coarse class of ten departing to a causal class
of two, with eight departures named. **On the repaired reader that class does not exist.** The
canonical focus — first connected move — now has **downstream 6** where it had 1, and its species is
a **singleton under every declared family**.

What survives, and is now the honest statement, is the **partition**:

```text
  {ascribed}   22 blocks      {former}   27 blocks
  causal       36 blocks      full       36 blocks
```

The panels genuinely differ; they coincide only on this one focus's block.

### A control in the species driver was itself malformed

*The causal panel is not the spelling panel* compared **one focus's fiber**. With that fiber a
singleton under both panels the comparison returns "equal" and the control failed — while the
partitions plainly differed at 27 against 36.

> **A comparison whose material cannot vary the property under test is the defect this project
> convicts, and a fiber of one cannot vary it.** The panels are a property of the partition, and a
> partition question asked of a single focus is malformed.

Repaired: `MoveSpeciesFiber::root_partition` returns the stable partition over the candidate roots,
the control compares partitions, and the fiber-level reading is reported as **UNDETERMINED** when
both fibers are singletons rather than graded. All controls now hold.

### The ablation deed did not move, and that is an honest null

`the_kernel_decides_which_moves_are_load_bearing` returns the same populations on
`FiniteTransport.lean` — connected 0/14 removable, isolated 0/2, verdict **UNDETERMINED**. The line
repair changed nothing *there* because that file has no skipped lines inside its declarations. What
changed is the standing of the verdict: it rested on two reasons and now rests on one. The
misaiming was real library-wide (17,283 steps) and was not affecting this particular material.

---

## 4. The residue, stated rather than rounded away

- **5,098 steps still carry an empty recruitment map.** Some steps genuinely recruit nothing; this
  population is no longer dominated by the cohort defect and has not been separated further.
- **26 steps still record a line that does not carry their former**, and **192 statements are still
  bracket-unbalanced.** Both are two orders of magnitude down and neither is zero; neither has been
  diagnosed.
- **The "declared names sunk into `local_bindings`" measure moved only 7,552 → 7,228, and it is a
  weak instrument.** It counts any `local_bindings` key that is a declared name anywhere in the
  library, so a local `A` colliding with a declaration `A` is counted. The audit's specific figure —
  833 names sunk *by the `with` path* — cannot be isolated by this measure, and the 324 difference
  should not be read as that population.
- **Steps rose 174,683 → 190,209.** More binders are now founded because `with`-form names are read
  where they are written. This is a larger population, not a cleaner subset of the old one, so no
  before/after row here is a like-for-like ratio.

## What this record does not claim

The repair is to the reader alone. It changes what every consumer sees and it types nothing: `D` is
still names-and-explicitness, `v` is still one match arm away, and no edge has been built. Whether
the species partition on a repaired reader carries an atlas row remains open and is not this
movement's question.
