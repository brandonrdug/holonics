# U2: F0's memory acceptance run, pinned before its split is read

**Date:** 2026-09-28. Refs #63, #73, #148. **Scope:** the acceptance run of
[U2](../../docs/plans/THE_REBUILD.md#u2-one-retention-contract-and-f0s-memory) ("The acceptance
run pins, before it runs"), under [F0's gate](../../docs/plans/THE_REBUILD.md#f0-the-predictor-on-unseen-families-the-releases-gate-73-148).
The pins below were committed before the split was generated and before any of its cells was read.
The receipt follows them.

The law it tests is the charged coarsening law, never retention: the tree's owner derives
(`compression::landmark::context`, "Which merges and releases are future-sufficient") that for the
declared receiver the exact merges beyond the chains are essentially empty, so each candidate below
is a declared coarser receiver priced against the finer by its code-length pair
(`Context/Merge.coarsening_within_margin_iff`: within `m` bits exactly when `P·W ≤ 2^m·P′·W′`).
The census it starts from is `hnn_population f0-census` on F4's passage
([notebook](../notebook/hnn_design/README.md#u2-the-standing-census-of-f0s-egg-september-28)).

The computational object is the helical pair interaction, read as the receiving tree's storage. Of
the winding guide's six objects the run touches **faces and placement** (the receiving face read at
its grain), the **tower thread** (a depth cut restricts every address; a release restricts a
context to its deepest kept ancestor) and the **tube** (the passage and its aeons); the helix, the
pair and the cell holonomy stay attached through the tree's owner.

## 1. The pins

1. **A fresh development-family split.** `seed = holonics-u2-development-families-2026-09-28-v1`,
   under F4's rule (`development_families.py`: the undivided family `(provider, record_group)` as
   sorted-key compact UTF-8 JSON, `SHA-256(seed ‖ NUL ‖ family)` read big-endian, residue zero
   modulo five validation, the other four choosing), the exterior scripts extended with the item
   `U2`. The aperture is F4's: one tail of at most `2^19` cells of each role's stream, beginning at
   its first section letter at or after `length − 2^19`, joined by `family_passage.py` (choosing
   first, validation after; the join a declared section, no relation across it). No reading of this
   split precedes the run. Its counts and hashes are recorded with the receipt; its membership and
   cuts stay owner-only in `.local/cuts/`.
2. **The declared receiver: the conditional byte-and-stop code at `L_R = 16`** (F0's comparison).
   At each byte cell (human, agent and tool), `−log₂ q_t(x_t)`, the egg's face read before its
   deposit; at each **response's stop**, a section-letter cell whose open part is on the agent
   channel, `−log₂ Σ_(ℓ ∈ letters) q_t(ℓ)`, the face's mass on the section letters. The letter's
   identity given the stop, the human parts' closes and the request's pointer are observed and
   charged to neither side. The letter at the join closes a choosing part and is charged to neither
   role. Codes are exact enclosures read at the grain; at each stop the face read is checked equal
   to the face the egg charges when the letter arrives.
3. **The candidates**: F0's admitted egg (`hnn_population f0-egg`'s constructor, the hazard partition
   learned on the choosing cells alone), differing only in its byte tree:
   - **(0) the unmerged tree**: the typed tree at the deepest depth its carriers admit (`D = 22`
     ticks at `n* = 2^20`);
   - **(1) once-reached leaf chains released at the aeon boundary**: at each aeon boundary the byte
     tree releases every node one arrival reached (each a leaf chain ending at `D`) and the pool
     letters only those nodes cover. A kept node keeps its counts and chart (its `β` already holds
     the released children's past); a read that reaches a released context reads the prior below the
     deepest kept node, and a later arrival founds it again. **The aeon boundaries** are each `open`
     section letter, before it is read (a conversation's aeon opens; the curated source reads
     conversations as aeons and turns as epochs), the declared join between the families, before the
     first validation cell, and the passage's close, before its standing is read. [agent-inferred] A
     `switch` letter is not a boundary: it moves between aeons already open, and nothing opens or
     closes there;
   - **(2) the depth cut at 12 ticks**: the typed tree declared at `D = 12` ticks (`Tree.release_rule`:
     no node past the admitted depth is founded).
4. **The choice, on the choosing families alone.** Each candidate reads the choosing cells. `C_k` is
   its conditional byte-and-stop code there and `S_k` its standing (the egg's canonical checkpoint,
   in bytes) after the choosing families, for (1) after the join's release. A candidate is
   admissible when `C_k + 2 − C_0 ≤ m`, decided on the enclosures (the difference's upper end); (0)
   is admissible. The chosen candidate is the admissible one with the least `S_k`, ties to the
   lower index. It is charged `⌈log₂ 3⌉ = 2` bits in every comparison; (0), F0's adopted egg, is
   charged nothing.
5. **The readings kept beside the state**, reported as their own line: each byte-tree node's chart
   carries 44 bytes that no face reads (its two certificates, 16 each; its cached stop weight, 8; its
   rebase count, 4; the census's E0). The standing is reported whole, its readings line
   (`44 · nodes`) apart, and without them: the standing of a receiver that does not read the certified
   residual. The acceptance reads the whole standing.
6. **The margin `m = 1214` bits.** F0's gain over flat on unseen bytes is `−2430 + 8/16 + ε`, so the
   gain `G` lies in `(2429 + 7/16, 2429 + 8/16]`, and `m = ⌊G/2⌋`. [agent-inferred] The standing is
   F0's measured obstruction and the gain over its control is F0's value; a coarsening may trade at
   most half of the value for memory, so a coarsened egg keeps at least the other half and stays
   below flat by at least what it gave up, on a validation passage of F0's aperture. The choosing
   census prices the other side of the trade: after the choosing families, (1) would release 1,766 of
   the tree's 2,648 bytes a cell and (2) 484. Nothing of it is read from validation.
7. **The standing budget: 1,298 bytes a cell**, the flat control's standing on F4's passage
   (1,358,603,467 bytes after 1,046,625 cells), the only standing F0 has compared the egg with.
   [agent-inferred] F0's acceptance reads "within the standing and passage budgets", and an egg
   within its control's standing removes the standing obstruction against that control. The choosing
   census says only (1) can reach it (the tree's 2,648 less 1,766, 882 a cell); (2) cannot (2,164).
   It is reported beside the acceptance, whole and without the readings, for F0's gate; it is not
   U2's acceptance, which is the plan's.
8. **Resources: ten minutes a passage and 20 GB** (20,000,000,000 bytes of resident set). A passage is
   one candidate's reading of one role's families, with its releases and its stop faces, or the flat
   tree's reading of the flat twin. Projected from F4's receipts: the egg alone reads F4's 1,048,243
   cells in about 100 s (the census's 107,150 ms includes its scans), so a role's passage is about
   60 s, and (2) reads shallower paths. (1) adds its releases: each visits every stored node and
   pool letter once and rebuilds the child table, linear in at most 27,181,970 nodes and 42,458,078
   letters (the unmerged tree's counts at the passage's end, which the rule only lowers), once at
   each boundary. The stop faces are read at under a thousand agent closes a role (F4). Memory:
   three eggs after the choosing families (each at most 1,387,905,377 bytes of tree standing), two
   after validation (each at most 2,781,355,790), the flat tree (1,358,603,467) and one encoded
   standing at a time: under 12 GB. The release's time is measured on F4's passage (already a
   diagnostic) before this run and recorded below. **Guards in the run**: a passage past 600,000 ms
   or a resident set past 20 GB stops it, and its partial evidence is reported as incomplete.
9. **The run, once.** The hazard partition is learned on the choosing cells; (0), (1) and (2) read the
   choosing families; the choice is made; the chosen candidate and (0) read the validation families
   once (if the chosen is (0), it reads them alone); the flat tree (`D = 48`) reads the flat twin
   once.
10. **The receipt**: the chosen candidate; its validation code against the unmerged tree (the
    difference `V_chosen + 2 − V_0`, exact, with its enclosure) and against flat (the bytes alone,
    and the bytes with the stops, against the flat tree's bytes); the standing a cell after the
    passage and at the join, whole, the readings line and without it, for the chosen and for (0), and
    against the budget; time and peak memory.
11. **Acceptance** (the plan's): the chosen candidate's standing after the passage lies strictly below
    (0)'s, and `V_chosen + 2 − V_0 ≤ m` is decided on the enclosures. **Failure**: the unmerged tree
    stays, and the separators are reported: the validation difference by term (human bytes, agent
    bytes, response stops) and, for (1), the nodes each release took. A chosen (0) fails the
    acceptance, having no strict fall.
12. **Where it lands.** The owner law (the release or the cut) enters `compression::landmark::context`
    only if a candidate passes and is adopted; otherwise the measurement harness mode alone. The
    release the run needs is realized on the tree with the eggs' delegation; if (1) is not adopted it
    is retired after the run with the harness's (1) path, and the run's commit is named.
