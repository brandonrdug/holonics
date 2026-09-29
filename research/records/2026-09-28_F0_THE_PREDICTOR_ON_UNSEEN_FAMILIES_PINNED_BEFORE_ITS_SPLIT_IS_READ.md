# F0: the predictor on unseen families, its acceptance run pinned before its split is read: the code and the standing fail

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
     passage (the standing that scores the response's first byte), its future is branched at the
     present incidence (amended before the split, §2: `AdmittedEgg::branch_at_present`, the
     passage's declared future relations withheld) and released under the scored law (`Population::release_response`, the egg alone named by 0 bits:
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
13. **Where it lands.** No law of the receiver or the tree changes. The harness mode `f0-acceptance`,
    the item `F0` in the split scripts, and `release_legibility.py` reading further corpora and a
    named vocabulary. Amended before the split (§2): the admitted egg's owner gains
    `branch_at_present`, with its test and its atlas row (`receiver.population-present-branch`).

## 2. Before the split: the dry runs, the margin, the cap, one amendment and the projection

The pins' rules are commit `33197fe2`. Everything below was read after it on spent splits only, and
committed before the fresh split was generated. Bits are read at `L_R = 16` as `n + k/16 + ε` with
`0 ≤ ε < 1/16`; the exact endpoints are in the private logs (`.local/cuts/f0-dryrun-*.log`, counts
and codes only).

**The draws and the margin.** `hnn_population f0-acceptance` on each spent joined passage, the egg
at 12 ticks, the partition learned on that split's choosing cells:

| Spent split | Validation cells | `Δ = V_egg − V_flat`, uncharged | The charged difference |
|---|---|---|---|
| F1's | 523,051 | `−279 + 10/16 + ε` | `−226 + 11/16 + ε` |
| F4's | 524,152 | `−726 + 9/16 + ε` | `−681 + 6/16 + ε` |
| F5's | 523,802 | `−672 + 15/16 + ε` | `−618 + 0/16 + ε` |
| U2's | 524,133 | `−812 + 9/16 + ε` | `−765 + 2/16 + ε` |

From F1's upper end to U2's lower end the range is exactly
`42236879361267602706533278199317/2^96` bits, `533 + 1/16 + ε`, so **`m = 534` bits**. The code
clause on the fresh split needs its charged difference's upper end below `−534`: three of the four
spent draws would meet it and F1's would not.

The run on U2's passage reproduces U2's recorded receipt of the same egg exactly: the standing
2,147,915,516 bytes after 1,047,804 cells (2,049 a cell, 21,793,273 byte-tree nodes), the flat tree's
1,359,168,091, and the bytes with the stops `−812 + 9/16 + ε` uncharged, U2's `−810 + 9/16 + ε` with
its 2 bits.

**The cap.** On F4's passage at the dry run's cap of 2,048 bytes, the longest milliseconds a released
cell were `c = 89/4` (22 rem 1 over 4, a release of four cells, its branch apart) and the longest
branch `b = 677` ms. `2048·c + b = 46,245 ≤ 60,000 < 4096·c + b = 91,813`, so **the cap is 2,048
bytes**.

**One amendment, before the split: the release branches at the present incidence.** On F4's passage,
8 of the 32 releases were refused by the population's admission, each at a tick where the passage's
declared incidence placed a later part's letter or target, 6 of them exactly at the held-out truth's
length. The branch carried the passage's declared future relations, which are the recorded future's
exterior codec information, so a release could stop at the recorded part's end. The admitted egg's
owner gains `AdmittedEgg::branch_at_present` (the relations whose reading part has not opened
withheld, their targets' counts and held spans released), with its test
(`a_branch_at_the_present_withholds_the_future_incidence_and_moves_no_face`: the same face at every
cell of the open part, and a byte at a withheld letter admitted where the full incidence refuses it)
and its atlas row (`receiver.population-present-branch`); the harness releases from it (pin 9). Read
again on F4's passage: the code unchanged, 28 releases stopped at their own stop and 4 reached the
cap, no refusal; of the 32 egg releases 24 are byte-identical to the first run's and the other 8
continue the refused ones' emitted bytes, so withholding the future moved no face; the flat
releases are identical.

**The projection.** F4's passage with the amended releases took 382,774 ms at a 7,116,886,016-byte
peak: the choosing reading 43,252 ms, the validation reading 48,637 ms, the egg's releases 203,358 ms
(the longest 29,264 ms) and the flat tree's 55,775 ms, the flat passage 26,596 ms. The three
code-only runs, made together, took 129,627 to 132,449 ms each at peaks of 6,798,041,088 to
7,022,305,280 bytes. The fresh passage is of the same aperture, so its readings are projected at
about 50,000 ms for the validation passage (against 600,000) and about 7,200,000,000 bytes (against 20 GB); the
releases are bounded by 32 releases at the cap, 32 × 46,245 ms, and the run is given 2,400,000 ms
before it is stopped as incomplete.

## 3. The receipt: the code clause fails and the standing is past its budget

The pins are commit `adc2cfbc`. Everything below was done after it.

**The split** (`development_families.py F0`, then `curated_source.py 524288 {choosing,validation} F0`,
`curated_incidence.py {choosing,validation} F0` and `family_passage.py F0`; counts and hashes only).
Source SHA-256 `e1001a7ed0dd03c583ab4ef097f3e243b12680daad05911374b8765107f2f8b2`, as F4's. Of 22,449
development families, 17,944 choose and 4,505 validate; the membership's SHA-256 is
`b1e322fe41a417de75aadc5c5bed63b5fdf8e6da49c9acc15b2d5696437eed3e`; no family was refused. The
choosing cut holds 523,747 cells (SHA-256 `960a708869995f5d0a22290733d64478b86b56f64005cdb6676042c44740a779`)
and 387 relations (`1aead00c3ef4c594c6a6809eedafedae2bc46ae5dbd1447603d312f4a78fdd98`), the
validation cut 524,005 cells (`18a80652ead7af8c32227cee1dd5a40e39dda0fd2115ad7d2e1aff4b3b8c297f`)
and 157 relations (`ea3bc70a4a5ee3a86b919bef57e2e042b7e947d81e1b6fc1de0cfa95661e8ee7`). The joined
passage holds 1,047,752 cells (`d36a63ab01dd1daf9a664885d1e7da34c45f5264fdf05bc8df7642f39faa5bbb`,
`held_out_start` 523,747) and 544 relations (`166c5d201830d8ac412cb180ef48c5242d9a99427a5cbe67cae7306fdbd28da4`);
its flat twin 1,046,085 bytes (`a8e4552a6a20cba9effb704fbf273de7bc88186d6b896ed50abcde0a561a6444`,
held out from 523,061).

**The run**, once, at commit `adc2cfbc`:

```sh
cargo run --release -p holonics --example hnn_population -- f0-acceptance .local/cuts/curated-f0-passage-cut.bin .local/cuts/curated-f0-passage-flat-cut.bin .local/cuts/f0-acceptance-releases.json
```

It took 365,812 ms at a 7,212,138,496-byte peak resident set: the choosing reading 43,793 ms, the
validation reading 48,562 ms, the egg's releases 190,966 ms apart, the flat tree 26,164 ms and its
releases 51,497 ms. Every guard held, and the run stayed within its projection. The exact
endpoints are in the private log (`.local/cuts/f0-acceptance.log`, counts and codes only).

**The charges.** The learned partition's description on this split's choosing cells is
`31 + 9/16 + ε` bits, so the egg is charged `53 + 9/16 + ε` (17 + 5 + the description) and the flat
tree 3.

**The code on the validation families** (524,005 cells: 20,990 human and 502,034 agent bytes, 936
response stops, 981 section letters).

| | The egg | The flat tree (`D = 48`) |
|---|---|---|
| Human bytes | `42882 + 7/16 + ε` | — |
| Agent bytes | `895439 + 2/16 + ε` | — |
| Every byte (523,024) | `938321 + 10/16 + ε`, `1 + 12/16 + ε` a byte | `940302 + 10/16 + ε`, `1 + 12/16 + ε` a byte |
| Response stops (936) | `1640 + 7/16 + ε`, `1 + 12/16 + ε` a stop | not coded |

- **The acceptance's comparison**: the egg's bytes and stops, charged, against the flat tree's bytes,
  charged: `−290 + 0/16 + ε` bits, exactly
  `[−11485719006832285584773538369701/2^95, −22971438013664571169547076739397/2^96]`. **Its upper end
  is not below `−m = −534`: the code clause fails.**
- Uncharged, the difference is `−341 + 7/16 + ε`, inside the spent draws' range (§2: F1's
  `−279 + 10/16 + ε` to U2's `−812 + 9/16 + ε`).
- Beside it, deciding nothing: the bytes alone `−1981 + 0/16 + ε` uncharged and `−1931 + 9/16 + ε`
  charged below the flat tree's; the whole curated stream (every cell, the request's pointer
  `518 + 12/16 + ε` and the charges) `+2122 + 14/16 + ε` above the flat stream; on the choosing
  families the bytes and stops `−3728 + 3/16 + ε` below the flat tree's bytes, uncharged.

**The standing after the passage** (1,047,752 cells): whole 2,141,915,637 bytes, **2,044 a cell
(remainder 310,549), past the budget of 1,298**; the readings beside the state 956,217,328 bytes
(21,732,212 byte-tree nodes), 912 a cell; without them 1,185,698,309 bytes, 1,131 a cell (remainder
690,797), within it. The flat tree's standing is 1,356,089,751 bytes after 1,046,085 cells, 1,296 a
cell.

**The passage**: within its budget: the validation reading 48,562 ms against 600,000, the peak
resident set 7,212,138,496 bytes against 20,000,000,000.

**Verdict: F0's acceptance fails.** The code clause fails (`−290 + 0/16 + ε` against `−534`) and the
standing is past its budget (2,044 bytes a cell against 1,298); the passage is within. Under F0's
failure branch the byte population stays a compression result, and F4's curated release and F5 wait.

- *The separating term of the code*: the response stops. On unseen families the egg's byte gain over
  the flat tree is 1,981 bits in 523,024 bytes (both `1 + 12/16 + ε` a byte), and the 936 stops it
  must predict cost it `1640 + 7/16 + ε` bits. What remains, charged, lies within the variation
  between family draws.
- *The separating term of the standing*: the readings kept beside the state, 912 bytes a cell; the
  standing without them is 1,131 a cell, within the budget.

**The release readings** (32 releases at the hash-ordered validation responses, of 152 eligible;
`release_legibility.py .local/cuts/f0-acceptance-releases.json .local/cuts/curated-f0-choosing-cut.bin`,
against the split's choosing vocabulary of 6,461 words; counts only).

| Reading | The egg's releases | The flat tree's releases | The held-out truths | The requests |
|---|---|---|---|---|
| Texts (typed refusals) | 28 (4: 3 text-codec separators, 1 at the cap) | 32 | 32 | 32 |
| Valid UTF-8 | 28 of 32 | 24 of 32 | 32 of 32 | — |
| Word tokens in the vocabulary | 1,186 of 1,513 | 1,626 of 2,096 | 3,056 of 3,232 | 1,054 of 1,182 |
| `()` balanced | 14 of 28 | 11 of 32 | 32 of 32 | 32 of 32 |
| `[]` / `{}` / `“”` balanced | 17 / 17 / 21 of 28 | 18 / 20 / 26 of 32 | 32 / 32 / 32 | 32 / 32 / 32 |
| Backticks / straight quotes / bold even | 13 / 20 / 18 of 28 | 15 / 26 / 21 of 32 | 32 / 32 / 32 | 32 / 32 / 32 |

The egg's word rate lies above the flat tree's (`1186·2096 = 2,485,856 > 1626·1513 = 2,460,138`) and
below the truths'. Its releases' warm times: the longest 27,187 ms (the one at the cap), in all
190,966 ms. The text stays owner-only (`.local/cuts/f0-acceptance-releases.json`, mode 0600); four
releases were shown in the conversation beside their controls.

**What lands.** The pins, the harness mode, the split scripts' item `F0`, `release_legibility.py`'s
further corpora and named vocabulary, and `AdmittedEgg::branch_at_present` with its test and atlas
row. No law of the receiver or the tree changes, and F0's egg is unchanged. **The split is spent.**
