# The forward plan stopped at transfer: the population memorizes families, and its standing is an index

**Date:** 2026-09-28. Refs #63, #73, #148, PR #149.

**Occasion.** Brandon: "Sol failed to complete F5 two times in a row, a total of ~4hr of work …
Audit and review and tie in what we were talking about." This audits PR #149 (`codex/f4-release`
at `e171b175`: three commits, 72 files, `+13467 / −141`) and Sol's thread, which ran in two turns:
03:17 to 04:21 UTC, then 04:21 to 07:05 UTC. It ties the result to the September 27 derivation
([the learner must move](2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md))
and to GPT-6 Astra's review within it.

## 0. Correction after the diagnosis (the same morning)

`[established-bounded; measured]` The first F0 loop re-ran F4's passage with each component read
separately. It shows that the title's first clause was **wrong**: on unseen families the population
codes the bytes *below* the flat tree. The `+1346` is the cost of structure that the flat stream
never codes.

| Validation (523,236 bytes, 916 section letters) | Population against flat, bits at `L_R = 16` |
|---|---|
| human bytes (30,841) | `−415 + 1/16 + ε` |
| agent bytes (492,395) | `−2015 + 7/16 + ε` |
| every byte | `−2430 + 8/16 + ε` |
| section letters, coded only by the curated stream | `+3333 + 10/16 + ε` |
| the request's pointer | `+402 + 0/16 + ε` |
| charges (`42 + 12/16` against the flat stream's `3`) | `+39 + 12/16` |
| **whole stream** | **`+1346 + 1/16 + ε`** |

On the choosing families the byte gain was `−4591 + 8/16 + ε`. It halves on unseen families but
stays a gain.

What stands:
- The releases are not legible text. Reading 580 of their 758 word tokens as real words shows a
  pattern-recognizing predictor at a PPM-class rate: about `1 + 12/16` bits a byte on unseen agent
  text.
- The standing is very large (the title's "index" is corrected: size shows a severe cost, not that the
  standing replays or indexes the source; a future-sufficient representation can be large and
  nonminimal). The re-run measured 11,513,530,863 bytes after 1,048,243 cells for the
  population (10,983 bytes a cell), and 1,358,603,467 bytes after 1,046,625 cells for the single
  flat tree (1,298 a cell).
- The posterior sits wholly on the admitted egg, with every other family thousands of bits behind.
  The trees beyond depth 24 add at most 20 bits. So seven of the eight families are standing
  without a predictive share.

Section 3's first reading is corrected accordingly: the byte population does transfer, weakly. F0 is
restated in THE_REBUILD as the predictor's rate on unseen families, within a standing budget.

Sol's own records are on the branch:
- [F4](https://github.com/brandonrdug/holonics/blob/e171b175/research/records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md)
- [F1](https://github.com/brandonrdug/holonics/blob/e171b175/research/records/2026-09-27_F1_WORD_ALPHABET_GATE.md)
- [F2](https://github.com/brandonrdug/holonics/blob/e171b175/research/records/2026-09-27_F2_FIELD_FAMILY_GATE.md)
- [F5](https://github.com/brandonrdug/holonics/blob/e171b175/research/records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md)
- [the F5 standing audit](https://github.com/brandonrdug/holonics/blob/e171b175/research/records/2026-09-27_F5_ATOMIC_STANDING_OWNER_AUDIT.md)

## 1. What happened

`[established-bounded; source-inspected, process-audit]`

- **Turn one (64 minutes).**
  - Pinned independent hash-seeded development-family splits for F4, F1 and F2, each with its cut
    hashes, before any measurement.
  - Ran F4's one validation passage, F1's bounded word probe and F2's bounded field exposure.
  - Stopped with "The forward plan has not reached F5."
- **Brandon asked:** "Why not continue to F5? I don't understand the halt."
- **Turn two (2 hours 44 minutes).** Sol answered "You're right. I halted too early" and built F5's
  development surface:
  - a protocol with one atomic checkpoint;
  - native standing codecs for `Landmarks`, `TreeFamily`, `BoundaryEgg`, `AdmittedEgg` and
    `Population`, with a 6,256,005,986-byte standing written and restored;
  - a blind CLI with a seed commitment;
  - a declared-context extractor;
  - 32 request-only diagnostic releases.

  It spent the F5 split on diagnostics, and said so.
- **What held.**
  - The evaluation partition was never opened.
  - Private material stayed owner-only, and only counts and hashes were published.
  - Every acceptance was pinned before its measurement, and failures were recorded as failures.
  - 991 host tests, the Lean build and 43 exterior fixtures pass.
- **Timing.** The practice of short loops and of showing output beside its control landed at 21:01
  PDT, 44 minutes after Sol began from `a4e631ff`. Sol worked without it.

## 2. What the receipts say

1. **The predictor does not transfer across families** (corrected in §0: it does, on bytes; the
   whole-stream excess is the structure's cost). `[established-bounded; measured]` (Sol's
   F4 record.) On F4's validation families the curated population coded `+1346 + 1/16 + ε` bits
   above the flat stream of the same bytes, after coding `−1477 + 5/16 + ε` below it on the
   choosing families. The earlier held-out gain, `−535 + 8/16 + ε`, came from a later tail of the
   same families.
2. **The releases are not text.** `[established-bounded; inspected by Claude on development
   diagnostics]` Of the 32 diagnostic requests:
   - 8 returned typed refusals (4 invalid UTF-8, 3 without a stop within capacity, 1 over
     aperture);
   - 24 returned candidates. Every one is broken words and fragments of the repository's
     vocabulary; none is legible, and none answers its request.

   The retrieval control returned coherent recorded replies, most of them not answers either. No
   private text is published here.
3. **The standing is very large.** `[established-bounded; measured]` (Corrected September 28: this
   item first read "an index, not a quotient"; size alone proves neither.) After 522,206
   choosing cells, the population's standing is 6,256,005,986 bytes, or 11,979 bytes kept per cell
   read, in 44,387,932 tree nodes (85 per cell). This is within the compacted tree's proved node
   bound, which counts digit arrivals. It is simply what a depth-48 context mixture's sufficient
   statistic costs.
4. **The other items were not reached.** `[established-bounded; measured]`
   - F1's exact word family takes 8,981 ms for 128 bytes, so a full passage was refused at
     preflight.
   - F2's field returns aggregate bits, not the per-cell face a population family needs.
   - F4's known-truth probes found the deterministic moiré not yet future-equivalent at tick five,
     and the stochastic tree's face apart from its source's on all 1,024 compared cells.

## 3. Reading

`[interpretation]`

- **Contexts memorize; navigators transfer** (§0 narrows this: the contexts' byte gain halves on
  unseen families but stays a gain; what fails is the rate, not the transfer). A context tree's gain lives in the contexts it has
  seen. New families present new contexts, and the charges the curated structure pays (sections,
  part clocks, the boundary egg, the request copy) stop buying anything. This is the September 27
  derivation, now measured on text: the arithmetic egg keeps a clock and codes at the truth, while
  the context tree pays for every determined cell. Transfer across families is the test that
  separates the two, and the byte population failed it.
- **The model class sets the retention.** A depth-48 context mixture's future-sufficient statistic
  is essentially every context count it has met, so its standing grows with the passage times its
  depth. The quotient the retention law asks for (the causal state, action-sufficient where the
  machine acts) is small only for a model class whose futures turn on few distinctions. At 11,979
  bytes per cell, the 20 W principle is violated by a factor we can now state.
- **Release cannot rescue its predictor.** `Q_R` reweights `P₀`. If `P₀`'s support is broken
  words, a receiver term reweights broken words. The receiver-conditioned release and the threshold
  commit wait for a predictor worth addressing.
- **The loop failed the way the workflow record predicted.**
  - Turn two's first native probe produced a candidate early. Shown beside its control, it would
    have ended the F5 build there; instead two hours went into checkpointing a standing whose
    releases are not text.
  - Turn one's halt was right, but its report named the blocker as "complete release" rather than
    by its measurement: the predictor loses to flat on new families.
  - Turn two over-corrected to a question. A failed gate is the next loop's subject.

## 4. Decisions

`[definition; agent-inferred]`

- **F0, transfer across families, now gates F4's curated release and F5** ([THE_REBUILD](../../docs/plans/THE_REBUILD.md#f0-the-predictor-on-unseen-families-the-releases-gate-73-148)).
  - Its first loop is a diagnosis from the existing run: which families and which components lose
    on the validation passage.
  - Its acceptance is on a fresh development split never used for a diagnostic: charged code
    strictly below the flat stream on the validation families, within a declared standing budget.
- **Every receipt reports standing bytes per cell read.**
- **PR #149 is split.** *(Reversed the same morning: the PR was merged whole. Its product shell is
  tested and is F5's consumer, and splitting 72 interdependent files cost more than it protected.
  F0 still gates F5. Brandon read the releases as promising: native generation without copying,
  whose broken words show pattern recognition.)*
  - **Lands:** its gate records, the family-split pins and scripts, the known-truth release probes,
    the same-face release view, face health, the word family, and the certified inverse-CDF
    theorem.
  - **Waits on its branch until F0 and F4 pass:** the F5 product shell (the protocol, the file
    checkpoint, the native standing codecs and the blind CLI). Nothing that works consumes it yet.
- **The practice gains one rule:** a failed gate is the next loop's subject, named by its
  measurement.
- **F6's chase terrain proceeds in parallel.** It is where the navigator machinery can be tested
  with known truth: birth by transport closure, action-sufficient retention, the threshold release
  and attribution. There, transfer is measured by construction: new arenas, the same constitution.
