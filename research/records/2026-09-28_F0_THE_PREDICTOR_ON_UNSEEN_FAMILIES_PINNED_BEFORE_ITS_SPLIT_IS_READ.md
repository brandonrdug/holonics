# F0: the predictor on unseen families, its acceptance run pinned before its split is read

**Date:** 2026-09-28. Refs #63, #73, #148. **Scope:** the acceptance of
[F0](../../docs/plans/THE_REBUILD.md#f0-the-predictor-on-unseen-families-the-releases-gate-73-148),
the release's gate, as [U6](../../docs/plans/THE_REBUILD.md#u6-the-text-chart)'s first loop. The
pins below were committed before the split was generated and before any of its cells was read. The
margin's rule (pin 6) and the release cap's rule (pin 9) were committed before the dry runs that read
their numbers on spent splits; the numbers were committed before the split was generated. The
receipt follows them.

The acceptance, from THE_REBUILD F0, unchanged: on a fresh development-family split never used for
a diagnostic, the conditional byte-and-stop code on the validation families is strictly below the
flat tree's by a margin pinned before the run, within the standing and passage budgets. The release
readings are reported beside it. If it fails, the byte population stays a compression result, and
F4's curated release and F5 wait.

The computational object is the helical pair interaction, read as the request's port meeting the
response's port through the egg's receiving tree. Of the winding guide's six objects the run touches
**faces and placement** (the byte faces read at their grain, and the population's weighed face: the
egg alone, named by 0 bits) and the **tube** (the passage, and each response as a clocked span that
ends at its stop); the helix, the pair, the cell holonomy and the tower thread stay attached through
the tree's owner (`compression::landmark::context`) and the egg's (`receiver::population::admitted`).

## 1. The pins

1. **A fresh development-family split.** `seed = holonics-f0-development-families-2026-09-28-v1`,
   the item `F0`, under F4's rule (`development_families.py`: the undivided family
   `(provider, record_group)` as sorted-key compact UTF-8 JSON, `SHA-256(seed ‖ NUL ‖ family)` read
   big-endian, residue zero modulo five validation, the other four choosing). The aperture is F4's:
   one tail of at most `2^19` cells of each role's stream, beginning at its first section letter at
   or after `length − 2^19` (`curated_source.py 524288 <role> F0`, `curated_incidence.py <role> F0`),
   joined by `family_passage.py F0` (choosing first, validation after; the join a declared section,
   no relation across it). Its counts and hashes are recorded with the receipt; its membership and
   cuts stay owner-only in `.local/cuts/`.
   - **Every spent split is excluded.** F4's (`holonics-f4-development-families-2026-09-27-v1`: F4's
     passage, F0's diagnosis and candidates 1–3, U2's dry run), F1's (`…-f1-…-2026-09-27-v1`), F2's
     two (`…-f2-…-2026-09-27-v1` and `…-f2-…-2026-09-28-v2`), F5's (`…-f5-…-2026-09-27-v1`, spent
     on F5's diagnostics) and U2's (`…-u2-…-2026-09-28-v1`). The fresh seed is none of them.
   - [interpretation] "Fresh" is the split. Every split draws its roles from the same 22,449
     development families, so the fresh validation role's families may have been read before in
     another split's roles, and the egg's declarations (the sweep, the hazard family, the depth cut)
     were chosen on such passages. No reading under this seed precedes the run, and nothing in the
     run is chosen on its validation role.
2. **The declared receiver: U2's conditional byte-and-stop code at `L_R = 16`** (U2's pin 2, F0's
   comparison). At each byte cell (human, agent and tool), `−log₂ q_t(x_t)`, the egg's face read
   before its deposit; at each **response's stop**, a section-letter cell whose open part is on the
   agent channel, `−log₂ Σ_(ℓ ∈ letters) q_t(ℓ)`, the face's mass on the section letters. The
   letter's identity given the stop, the human parts' closes, the request's pointer and the letter at
   the join are observed and charged to neither side. Codes are exact enclosures read at the grain;
   at each stop the face read is checked equal to the face the egg charges when the letter arrives.
3. **The egg: F0's admitted egg at `F0_BYTE_DEPTH = 12`** (`f0-egg`'s constructor since U2: the
   admitted receivers over the boundary egg on the typed tree at 12 ticks and the letter tree at
   `D_L = 12`), the hazard partition learned on the choosing cells alone, the comparison hazards
   beside it (they enter no face), read through its `Family` law directly (exact faces), as U2's
   harness read it.
4. **The comparison, like with like.** `V_egg` is the egg's code of the validation families' bytes
   and response stops; `V_flat` is the flat tree's (`D = 48`, over the flat twin, the same bytes with
   every letter removed) code of the same bytes. [agent-inferred] The flat tree predicts no stop and
   is charged none: the egg alone pays the stops, which a release must predict. F0 reads the code
   "against the flat tree on the same bytes"; a stop code for the flat tree would be a control the
   plan does not declare, and charging the stops to the egg alone can only make the clause harder to
   hold. Beside it, deciding nothing: the egg's bytes alone against the flat tree's; the whole
   curated stream on the validation families (every cell's face, the request's pointer and the
   charges) against the flat stream; the choosing families' code.
5. **The charges.** The egg: the curated harness's development sweep,
   `⌈log₂ 3⌉ + ⌈log₂ 47⌉ + ⌈log₂ 11⌉ + ⌈log₂ 8⌉ + ⌈log₂ 3⌉ = 17` bits; F0's adoption decisions
   made on choosing families before this run (candidates 1, 2 and 3 each adopted or not, candidate 5
   one of three), `⌈log₂(2·2·2·3)⌉ = 5` bits; and the learned hazard partition's description on this
   split's choosing cells. The flat tree: its recorded depth sweep, `⌈log₂ 5⌉ = 3` bits.
   [agent-inferred] Each choice made on data before the run is a hypothesis selection, and its
   `⌈log₂ k⌉` belongs to the egg's two-part code; U2 charged its own choice the same way.
6. **The margin `m`: the range of the draws already read.** For each spent split read at F0's
   aperture with a joined passage (F1's, F4's, F5's and U2's), this harness reads the uncharged
   difference `Δ_k = V_egg − V_flat` on its validation role, with the same egg, receiver and flat
   tree and the partition learned on that split's choosing cells. Then
   `m = ⌈max_k upper(Δ_k) − min_k lower(Δ_k)⌉` bits. The code clause holds when the charged
   difference `(V_egg + C_egg) − (V_flat + 3)` has its upper end strictly below `−m`; an enclosure
   that straddles `−m` is undecided and fails. [agent-inferred] F0 tests transfer to unseen
   families. Its passages differ from one another only in which development families the hash drew,
   so the range is the variation the same receiver has already shown between draws, read exactly and
   with no estimate. A fresh gain within that range cannot be told from the draw. U2's `m = 1214`
   (half of F0's byte gain) was a value margin for a trade between two eggs, read on bytes alone; it
   is not this clause's. The dry runs read spent splits only and choose nothing but `m` and the
   release cap; they also give the projection.
7. **The standing budget: 1,298 bytes a cell**, read on the whole standing (U2's pin 7: the flat
   control's standing on F4's passage; F0: "A standing budget is pinned before each run"). The
   standing is the egg's canonical checkpoint after the passage. The readings kept beside the state
   (44 bytes a byte-tree node: its two certificates, its cached stop weight and its rebase count) and
   the standing without them are reported beside it, with the flat tree's standing on this run. If
   the standing fails while the code holds, the separating term is named by its measurement.
8. **The passage budget: ten minutes and 20 GB** (THE_REBUILD's Protocol, "Budgets"; U2's pin 8;
   F2's budget (c)). The egg's reading of the validation families, its stops included and the
   releases' time apart, within 600,000 ms, and the run's resident set within 20,000,000,000 bytes.
   The choosing passage and the flat tree are guarded the same. The card is not used. **Guards in
   the run**: a passage past 600,000 ms or a resident set past 20 GB stops it, and its partial
   evidence is reported as incomplete.
9. **The release readings, reported beside the code and deciding nothing** (F0: "The release
   readings are reported beside it"; Brandon, September 28: monitored and never forced).
   - *Eligible*: each declared request→response relation of the validation role whose request lies
     in the validation role, whose response opens on the agent channel, whose request and response
     parts are both nonempty, and with room in the aperture.
   - *Selected*: the 32 lowest order keys `Draw::new(20260928 + v).next()` (`v` the response
     letter's tick in the validation role; the terrain's seeded exact draw, `holarchy::terrain::Draw`),
     or all if fewer.
   - *The egg's release*: at the response's opening letter, after the egg has received it within the
     passage (the standing that scores the response's first byte), its future is branched and
     released under the scored law (`Population::release_response`, the egg alone named by 0 bits:
     `P_release = P_scored` at every cell, the stop law, the text codec's squares), with keys from
     `Draw::new(order key)`. The cap: the largest power of two `P` of bytes with `P·c + b ≤ 60,000`
     ms, F4's warm response budget, where `c` is the F4 dry run's longest milliseconds a released
     cell (its branch apart, read at that run's cap of 2,048) and `b` its longest branch (the number
     in §2). A release that reaches its cap is the law's typed refusal.
   - *The controls*: the held-out truth continuation (the response's recorded first part, up to the
     next section letter), and the flat tree's release (its future branched at the response's first
     byte, drawing as many bytes as the truth holds, up to the cap, from the same keys: its stop is
     observed, never predicted).
   - *The readings*: `release_legibility.py` over the egg's releases, the truths, the flat releases
     and the requests, against this split's choosing vocabulary: texts and typed refusals, word
     tokens in the vocabulary (the word-shape rate), the paired delimiters and valid UTF-8; beside
     them the egg's statuses and warm times, against F4's 60-second warm response, deciding nothing.
   - *Private*: the text stays owner-only (`.local/cuts/f0-acceptance-releases.json`, mode 0600).
     The first four in the order are shown in the conversation beside their controls, shortened,
     never in the repository.
10. **The run, once** (`hnn_population f0-acceptance`, `research/notebook/hnn_design/hnn_population_f0.rs`).
    The hazard partition is learned on the choosing cells; the egg reads the choosing families, then
    the validation families once, releasing at the selected responses; the flat tree reads the flat
    twin once, releasing at the same bytes.
11. **The receipt**: the charged and uncharged differences with their exact enclosures, by channel
    and at the stops; the bytes alone and the whole stream beside; the standing a cell after the
    passage, whole, the readings line and without it, against the budget and beside the flat tree's;
    the validation passage's time and the peak resident set against the passage budget; the release
    readings.
12. **Acceptance** (F0's): the code clause holds, the whole standing a cell is within 1,298 bytes, and
    the validation passage is within 600,000 ms and 20 GB. **Failure** (F0's): the byte population
    stays a compression result, and F4's curated release and F5 wait; the failed clause is named by
    its measurement.
13. **Where it lands.** No library law changes. The harness mode `f0-acceptance`, the item `F0` in the
    split scripts, and `release_legibility.py` reading further corpora and a named vocabulary.
