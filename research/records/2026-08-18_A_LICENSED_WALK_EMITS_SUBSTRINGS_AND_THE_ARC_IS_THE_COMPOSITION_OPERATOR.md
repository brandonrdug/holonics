# A licensed walk emits substrings, and the arc is the composition operator

**Date:** 2026-08-18
**Truth status:** `proved-standard` for the substring theorem, which follows from what a suffix
automaton is and was measured besides; `established-bounded` for every figure.
**Evidence:** `measured`. `soma/life/examples/the_composition_joins_spans_at_forks.rs`,
`the_fork_composes_and_the_quotient_bounds_the_front.rs`,
`the_arc_is_the_composition_operator.rs`.
**Provenance:** Brandon, 2026-08-18: *"It shouldn't be a forced law causing it to recite verbatim,
that just means you're not allowing the information as a substrate to diffuse and reduce in
'training'."*

---

## 1. A licensed walk emits substrings — by construction

A suffix automaton accepts exactly the substrings of its material. `carry` along a **licensed**
transition lands in the class of a longer substring **that still occurs**. So a walk that only
follows licensed transitions emits a substring, always, and a fork is not a recombination — it is a
substring extending several ways, each of which still occurs.

**Measured, and it is total:** joining forced runs at forks over three prompts returned **0 composed
surfaces of 20 emissions.** Every one was a contiguous window of a single source.

**So recitation is not a policy failure.** It is what the organ is, and no branching discipline over
licensed transitions will ever compose.

## 2. Composition requires the arc

To compose, an emission must take a continuation licensed by a **shorter** context than the one it
carries — which is to say it must **arc**. Bounding the context to `L` tokens forces exactly that:
climbing until the class's longest substring fits merges every longer context into its `L`-token
suffix, so continuations come from every place that suffix occurred.

**Measured:** with a bound, **192,246 composed surfaces against 101 verbatim**, and the block
population falls `4,731 → 2,959` as the bound tightens. Without a bound, zero.

> **The arc is the composition operator**, and it is the same coordinate the winding lives on — the
> phase this carrier deletes. Two findings of the same day about the same missing thing.

## 3. And the front cannot be reduced without a chooser — five times over

Every attempt in this session to walk *through* the plural return reduced the front by an arbitrary
order, each time with a comment asserting it was not a selection:

1. reading the licensed set at a coarsened class while carrying from the original state;
2. `blocks.entry(..).or_insert(..)`, keeping whichever tip the iteration reached first — ordered by
   class index, which is why a low-index germ dominated;
3. coarsening by a fixed number of suffix links, which on a tree of height 8 lands nearly everything
   at the root;
4. continuing through `licensed.first()`, which is alphabetical order;
5. `members.remove(0)` after sorting by the emitted surface — again alphabetical, which is why every
   printed emission began with punctuation.

**All five are one defect.** A population needs reducing, "keep one per block" is reached for, and
*one* is decided by a sort key. A sort key is a governor with no name on it.

**The theory already says not to.** A diffused substrate returns plurally by construction; the plural
return is not a step in a sequence. `presentation_quotient::divide_junction` returns the **blocks**,
and the block is the response — 3,125 licensed continuations divided into **84 blocks**, with blocks
of 151 and 257 members, and 48 into 37 with a block of 11 sharing a face. What continues a cycle is a
receiver's further declaration, not an appended token.

## 4. What this leaves standing

- **Diffusion is the context bound.** Established and measured.
- **The arc is the composition operator.** Established and measured, both arms.
- **The block is the response.** Established; the division runs.
- **A readable single emission has not been produced by any lawful path**, and every path that
  produced one used a sort-order chooser. That is stated as the position rather than smoothed.

## 5. Falsifiers

- Any walk over licensed transitions that emits a non-substring refutes section 1.
- Any bounded-context emission that is a contiguous window of one source at every bound refutes
  section 2.
- A front reduction that is not a sort key, not a rank, and not a cap would refute section 3 — and
  none has been written here.
