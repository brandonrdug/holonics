# The conclusion carries its relation, and the kernel agrees seven of seven

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured` throughout; the corpus adjudication is a real kernel verdict per
declaration with mathlib in scope.
**Movement:** *the conclusion carries its relation*, the second of
`blueprint/THE_TYPED_TRANSPORT_ATLAS.md`. **Complete.**
**Owners:** `soma/life/src/lean_mathematics/syntax.rs` (`principal_relation`),
`soma/life/src/lean_mathematics.rs` (`LeanDeclarationOrgan::{conclusion_relation, rewritable}`).
**Driver:** `soma/life/examples/the_conclusion_carries_its_relation.rs`.

---

## 1. `v`, and the two structural cuts that find it

`H.0362` names `v` as a formulation node's denoted invariant. `LeanDeclarationOrgan` carried none:
`result_constructors` already walked the conclusion at depth zero and matched **one character**,
`'∧'`, so every `=`, `↔`, `≤`, `<`, `→`, `¬` fell through. The emission therefore offered `rw [d]`
for every recruited declaration whatever it concluded.

`principal_relation` makes two cuts, both structural rather than authored:

1. the conclusion is the text after the first top-level `:`;
2. **`→` is right-associative and binds loosest**, so the text after the *last* top-level arrow is
   what the declaration concludes — everything before it is a hypothesis.

Then a conclusion carrying exactly one distinct depth-zero relation returns it. One carrying none, or
several, returns `None`. **The reader does not guess a principal connective it cannot see**, and
`None` is *not rewritable*: a reader that cannot see what a declaration concludes may not license a
transport by it.

## 2. The kernel adjudicated it, and agreed on both arms

The falsifier is not an assertion. Every declaration of the corpus was submitted as an actual
`rw [d]` against a real kernel with mathlib in scope, and the reader's prediction graded against
Lean's own words — *"Expected an equality or iff proof"*.

```text
  congestion_exceeds_one_of_subset_load   <    predicted not rewritable   kernel agrees
  proportionalFlow_column_sum             =    predicted rewritable       kernel agrees
  proportionalFlow_nonnegative            ≤    predicted not rewritable   kernel agrees
  proportionalFlow_respects_capacity      ≤    predicted not rewritable   kernel agrees
  proportionalFlow_row_sum                =    predicted rewritable       kernel agrees
  subset_normalized_load_le_congestion    ≤    predicted not rewritable   kernel agrees
  total_demand_le_total_capacity          ≤    predicted not rewritable   kernel agrees
```

**Seven of seven, and both disagreement arms were live.** A conclusion called an equality and refused
would be a *misread `v`*; one called otherwise and accepted would be a *missed edge*. Neither
occurred here, and both are reported separately rather than folded into one pass — the second costs
coverage, not correctness.

This is what makes the 105 refusals structural rather than mathematical: five of these seven cannot
carry a rewrite, the emission offered each twenty-one, and the kernel returned exactly 105.

## 3. The census, and the honest half of it

```text
  documents the reader could open  6,894      REFUSED  622
  declarations opened            127,735

    =                                    58,040
    ?  no single depth-zero relation     48,316      <- UNCLASSIFIED, counted not defaulted
    ≤                                     6,596
    ↔                                     5,480
    ∈                                     2,634
    <                                     2,094
    ⊆                                     1,708
    >                                     1,085
    ≠                                       966
    ∣                                       438
    ∧                                       259
    ∨                                        92
    ≥                                        27

  rewritable — the population `rw` may be offered for   63,520 of 127,735
```

**37.8% of conclusions cannot be resolved to a single depth-zero relation.** That population is the
reading's honest half: it is returned by name and counted, and it is treated as *not rewritable*,
which is conservative. On the corpus that conservatism cost nothing; over the library it will cost
**missed edges** — rewritable declarations the emission will not offer — and that is a coverage
bound, not a correctness one.

**And the emission's reader refuses 622 of 7,516 documents outright.** Conditioning the library whole
returns a hard parse refusal on the first declaration it cannot name, so the census runs per document
and counts what is refused. That is a property of `lean_mathematics`'s own parser — a different
reader from `lean_development` — and it bounds what any emission built on it can ever see.

## What this movement does not claim

`v` alone types a rewrite and nothing else. An application still needs `D`, which is the next
movement and the plan's gate. The relation list is the material's rather than a taxonomy, and a
symbol that never occurs costs nothing; what the list may not do is decide admissibility, which is
the single-relation condition's job. No edge has been built.
