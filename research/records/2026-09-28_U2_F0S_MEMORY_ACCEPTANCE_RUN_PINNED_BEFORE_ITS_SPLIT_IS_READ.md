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

## 2. Before the run: the split and the projection

The pins are commit `d6feae7e`. Everything below was done after it.

**The split** (`development_families.py U2`, then `curated_source.py 524288 {choosing,validation} U2`,
`curated_incidence.py {choosing,validation} U2` and `family_passage.py U2`; counts and hashes only).
Source SHA-256 `e1001a7ed0dd03c583ab4ef097f3e243b12680daad05911374b8765107f2f8b2`, as F4's. Of 22,449
development families, 18,006 choose and 4,443 validate; the membership's SHA-256 is
`56e1585b6dcfe15d6940057cf1873d7eae406345180d28de299d0c5da9d4bca8`; no family was refused. The
choosing cut holds 523,671 cells (SHA-256 `27b4fcbf135328d3643f9be715a3c22ad82eb4c6178ccde13c540d59eef8ab5d`)
and 452 relations (`286d136323f7ac7b958f35125edeb437cca79773333c2f5fcc8a3d34b98e57b5`), the
validation cut 524,133 cells (`edda3cff1f40add4a0d948188b61b69c816da6bc01f19f6a3e8fb8280067985f`)
and 95 relations (`f69bde8f8f1e3e080da59f002d2675cf01b70ce71ecdb31787f92d6117c2b304`). The joined
passage holds 1,047,804 cells (`4a40516a4ae6ce75be2f092fe25a624c7427dd33494a7b87577b72f7028cd3da`,
`held_out_start` 523,671) and 547 relations (`cd5efd08c9e238b9581741ad084d61656573e6fc375a64436545941683e96e8f`);
its flat twin 1,046,167 bytes (`e66e0d7eb9e644732197dea52e25fa4385ce80750a3e294f331e619f2bcdb62f`,
held out from 522,854). The cuts' manifests count 10 `open` letters in the choosing cut and 20 in
the validation cut.

**The release and the harness.** Candidate (1)'s release is `Landmarks::release_once_reached`
(`compression::landmark::context::once_reached`, with its tests: a released context reads exactly as
one never founded, a read along kept nodes is unchanged, releases between deposits keep every face
normalized and every standing decodable, a ceiling refuses), delegated through `TreeFamily`,
`BoundaryEgg` and `AdmittedEgg`. The run is `hnn_population u2-acceptance`
(`research/notebook/hnn_design/hnn_population_u2.rs`).

**The projection, measured on F4's passage** (already a diagnostic; the whole harness run once as a
dry run of its code paths, `u2-acceptance` on `curated-f4-passage-cut.bin`). It took 269,015 ms at a
9,366,650,880-byte peak resident set: each candidate's role passage 40,458 to 48,827 ms, the flat
tree 26,478 ms, each of (1)'s ten releases on the choosing families 67 to 283 ms. Every guard held
with room (the longest passage under a tenth of ten minutes, the peak under half of 20 GB). It
reproduced F0's recorded readings on that passage: the unmerged egg's standing 2,781,355,790 bytes
(the census's) and its bytes `−2430 + 8/16 + ε` against flat. Its readings on F4's families are a
diagnostic and choose nothing here: on F4's choosing families (1) read `+16115 + 7/16 + ε` against
(0) charged (not admissible) and (2) `+129 + 13/16 + ε` (chosen); F4's validation read (2)
`+219 + 0/16 + ε` against (0) at 2,058 bytes a cell against 2,653. No pin moved.
