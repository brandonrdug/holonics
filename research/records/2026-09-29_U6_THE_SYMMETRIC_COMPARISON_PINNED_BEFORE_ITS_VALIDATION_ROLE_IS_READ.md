# U6 item 2: the symmetric comparison, pinned before its validation role is read

**Date:** 2026-09-29. Refs #63, #73, #148. **Scope:** item 2 of
[the text chart's audit](2026-09-29_THE_TEXT_CHART_AUDITED_ONE_PREDICTOR_SEEN_CONVERSATIONS_AND_NO_ARITHMETIC.md)
(§4), under [THE_REBUILD U6](../../docs/plans/THE_REBUILD.md#u6-the-text-chart), and its one
measured run on item 1's split by conversation. The pins below (§1) were committed before either
role's stream was generated. The projection (§2) follows the streams and precedes the run. The
receipt (§3) follows the run.

The comparison replaces F0's lopsided one (the audit's finding 1). F0 gave the egg, free, the
identity of every section letter, the human parts' closes, the request's pointer and its
channel-typed contexts, and it charged no stop to the flat tree. Under full accounting the egg coded
F0's curated stream `+2122 + 14/16 + ε` bits worse than the flat tree.

The computational object is the helical pair interaction, read as a request's port meeting a
response's port through each side's receiving tree. Of the winding guide's six objects the run
touches two:
- **faces and placement**: what each side's face reads at every cell and what it is charged for;
- **the tube**: the conversation as the aeon, and a response as a clocked span that ends at its own
  letter.

The helix, the pair, the cell holonomy and the tower thread stay attached through the trees' owner
(`compression::landmark::context`) and the egg's (`receiver::population::{admitted, boundary}`).

## 1. The pins

1. **The split and its streams.** Item 1's split by conversation
   (`development_families.py U6`, seed `holonics-u6-development-conversations-2026-09-29-v1`):
   - choosing holds 61 conversations, validation 11;
   - the reserve, 15 conversations named
     `09d7ae5b86d1b34cd1f57a100fb0ec412f59902f6ec3b90924a7c80b136f8a24`, is never read, and no
     command passes `--read-reserve`.

   The streams use F0's aperture, one tail of at most `2^19` cells a role beginning at a section
   letter: `curated_source.py 524288 <role>`, `curated_incidence.py <role>` and `family_passage.py`
   (choosing first, validation after; the join a declared section; validation's aeon ordinals
   shifted past choosing's). Only counts and hashes are recorded. The cuts stay owner-only in
   `.local/cuts/`.
2. **Same context, same events.** Both sides read every cell of the joined passage once, the
   choosing role and then the validation role. Each side scores each cell by its face before that
   cell's own deposit. On the validation role every cell is an event of the comparison: every byte
   (human, agent, tool) and every section letter, the letter at the join included, over the one
   268-symbol chart (`SectionChart::curated`).
   - Each side enters every conversation's aeon at the letter that opens its part. The letter is
     read in the leaving aeon's address and then opens its part in the entered one
     (`AdmittedEgg::enter_aeon`, `TreeFamily::enter_aeon`).
   - The aeon's ordinal is exterior codec information given to both sides alike, so it cancels and
     is charged to neither.
3. **The candidate: F0's admitted egg**, unchanged (`admitted_egg_at` at `F0_BYTE_DEPTH = 12`,
   item 1's aeons and present retention):
   - the channel-typed byte tree;
   - the letter tree at `D_L = 12`;
   - the part clock and the hazard on the partition learned on the choosing cells alone, with the
     declared partition and the other stage as comparisons that enter no face;
   - the request's copy stage and its pointer.

   It is read through its `Family` law, exact faces, as F0 read it.
4. **The control: the context tree over the same stream.**
   - Its address holds the cells alone, bytes and letters, with no channel or kind slot
     (`SectionSlots::Cells`, the owner change of this loop: `TreeFamily::sectioned` with the
     cell-only family).
   - It uses the flat tree's recorded depth `D = 48`, the `½` stop prior, KT nodes, `n* = 2^20` and
     `L_R = 16`.
   - It enters the same aeons at the same letters, so each conversation's context is its own on
     both sides.

   [agent-inferred] The depth is not chosen again: it is the flat tree's recorded depth, so that
   sweep's charge is the control's whole charge. The control keeps no slot, so every typed choice
   belongs to the candidate and is charged there.
5. **Symmetric charges.** Every declared choice is charged to the side that made it.
   - *Coded by both*: every section letter. The letters' identity, the human parts' closes and the
     channel that every typed context reads are paid in the stream, by both sides.
   - *The candidate*:
     - the request's pointer on the validation role (`PointerReadout`, its code at the join
       subtracted from its code at the end): the incidence the candidate reads, which the cells do
       not carry;
     - the development sweep's 17 bits: its byte tree among 3 (the choice of channel-typed
       contexts), the hazard among 47, the letter tree among 11, the copy stage's law among 8 and
       the pointer's code among 3;
     - F0's adoption decisions' 5 bits;
     - the learned partition's description on this split's choosing cells.
   - *The control*: its recorded depth sweep, `⌈log₂ 5⌉ = 3` bits.
   - *Neither*: the aeon ordinals (pin 2). The later human return's pointer is also charged to
     neither: it is a receipt only and enters no face (`admitted`'s header). It is reported beside.
   - [agent-inferred] Why the pointer is charged and nothing more:
     - The candidate's code of the stream is two-part: the incidence is coded at each reading part's
       letter, then the cells given it. Each factor is a face given the past, so the joint code is a
       prefix code for the passage with its incidence.
     - Summed over the incidence, the stream's Kraft sum stays at most one, so the candidate's
       charged code is a prefix code for the stream alone, as the control's is.
     - Each choice made on data before the run is a hypothesis selection. Its `⌈log₂ k⌉` belongs to
       the chooser's two-part code, as in F0 and U2.
6. **The events and the stop kinds.** A byte is read by its channel. A section letter is read by its
   kind, from its section and the channel of the part it closes:
   - *a response's end*: a `turn` or `part` letter on the human channel that closes an agent part
     (a human part follows the response);
   - *a record boundary within a turn*: any other `part` letter;
   - *a turn*: any other `turn` letter;
   - *a switch*: a `switch` letter;
   - *an opening*: an `open` letter.

   Each letter's code splits exactly into its **end**, `−log₂` of the face's mass on the twelve
   letters at that tick, and the **letter given the end**. Each kind's code, its end and its letter
   are reported on both sides. The letters that close an agent part (F0's "stops") are reported
   beside, by kind. At each letter the face read is checked equal to the face the side charges.
7. **The acceptance.** The charged difference on the validation role is
   `Δ = (C_cells + C_pointer + C_charges) − (K_cells + 3)`. The acceptance holds when its upper end
   lies strictly below `−m`. An enclosure that straddles `−m` is undecided and fails.
8. **The margin: `m = 534` bits** [agent-inferred], F0's range of the spent draws, unchanged.
   - *The rule.* It is a stated rule read on spent material only: F0's pin 6 read the uncharged
     egg-against-tree difference on four spent family draws (F1's, F4's, F5's and U2's). Their range
     runs from F1's upper end to U2's lower end, `533 + 1/16 + ε`, rounded up to 534.
   - *Why not narrower.* It is the only recorded measure of how far that difference moves between
     draws of the development material. The symmetric comparison adds the letters and the pointer,
     whose draw-to-draw motion no draw has read.
   - *Why not read again.* A spent draw of the symmetric comparison cannot be read: every spent
     split holds the reserve's material.
   - *Its size.* It is not rescaled to the validation role's size, which is unknown at the pin.
     Under the resampling the spent draws measured, a sum over fewer cells moves less, so an
     unscaled margin can only be stricter. Conversation-level motion was never measured; each
     validation conversation's own difference is read beside, deciding nothing.
   - *No-hypercompression.* The control's prequential face is a probability over the validation
     stream, and the candidate's charged code is a prefix code fixed before the run. So the chance,
     under the control, that the candidate is shorter by `m` bits is at most `2^(−m)`. The margin
     also excludes the control's own draw.
9. **The budgets, reported beside the code; they do not decide it** (F0's pins 7 and 8, F4's warm
   response):
   - *the whole state*: each side's canonical checkpoint after the passage, in bytes a cell, against
     1,298, with no reading subtracted;
   - *the passage*: each side's reading of the validation role against 600,000 ms, and the run's peak
     resident set against 20,000,000,000 bytes. A reading past either stops the run (the guards),
     and its partial evidence is reported as incomplete;
   - *the complete warm response*: each release's branch and draws together, against 60,000 ms.
10. **The releases, deciding nothing.**
    - *Eligible and selected*: F0's rule. The validation role's declared request→response relations
      whose request lies in the validation role, whose response opens on the agent channel, whose
      two parts are nonempty, and with room in the aperture. The 8 lowest order keys
      `Draw::new(20260929 + v).next()` are selected, `v` the response letter's tick in the role.
    - *Each side's release*:
      - It starts from the side's standing after the response's opening letter, branched at the
        present: the candidate by `AdmittedEgg::branch_at_present`, the control by its own
        standing, which reads no incidence.
      - It is released alone in a population named by 0 bits, under the scored law
        (`Population::release_response`), with keys from `Draw::new(order key)`.
      - The cap is the least of 2,048 bytes and the aperture's room. Each side stops at its own drawn
        section letter, and a release that reaches the cap is a typed refusal.
      - Neither side is given the logged reply's length.
    - *Beside them*: the logged reply, the response's recorded first part up to the next section
      letter. It is observed conduct, never a target.
    - *Private*: the texts go to `.local/cuts/u6-symmetric-releases.json` at mode 0600. They are
      shown shortened, about 300 characters each, in the conversation only, never in the repository.
    - *In the repository*: the counts of `release_legibility.py` against the split's choosing
      vocabulary (`curated-u6-choosing-cut.bin`), for the candidate's releases, the control tree's
      and the logged replies.
11. **The run, once**:
    `cargo run --release -p holonics --example hnn_population -- u6-symmetric .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-symmetric-releases.json`
    (`research/notebook/hnn_design/hnn_population_u6.rs`). The harness was checked end to end on a
    synthetic passage of made-up conversations, with no private data, before this commit.
12. **Failure.** The candidate stays a compression result. The failure is named by its measurement:
    the kinds and terms that separate the two sides. It becomes the next loop's subject.
13. **What lands**:
    - the owner change: `SectionSlots::Cells` in `compression::landmark::context::sections`, with the
      tree family's label, declaration and checkpoint tag, its tests and its atlas rows;
    - the harness mode `u6-symmetric`;
    - the control tree's corpus in `release_legibility.py`;
    - these pins and the receipt.

    No law of the candidate changes.

## 2. The streams and the projection

The pins are commit `9b849f54`. The streams below were generated after it and before the run.
Only counts and hashes are read here.

**The streams** (`curated_source.py 524288 {choosing,validation}`, `curated_incidence.py
{choosing,validation}`, `family_passage.py`; the split's membership
`19f8b42d46e1ea96dbcaa2f8e83029ab9c9b92a5dd7cee9b138244d8207a6e75`; every manifest names the reserve
as excluded; no family refused).

| | Choosing | Validation |
|---|---|---|
| Conversations; messages | 61; 16,314 | 11; 682 |
| The role's whole stream (cells; SHA-256) | 11,682,320; `99a488a8…22393c0` | 574,447; `3a81a9ac…1605d5e0` |
| The cut (F0's aperture, a tail from the letter at or after `length − 2^19`) | 524,012 cells from 11,158,308; `2155c166…4d7d312b` | 524,009 cells from 50,438; `aad74932…9d5ef5451` |
| The cut's letters (`open`, `switch`, `turn`, `part`) | 9, 74, 355, 359 | 10, 0, 380, 215 |
| The cut's aeons (SHA-256) | `e8140caa…ea33799` | `104187ae…a33920` |
| Declared relations (SHA-256) | 434 (`367340f2…a5867c07`) | 515 (`c8d1bf85…f04aeebdb`) |

The joined passage holds 1,048,021 cells
(`c6e51a356de4c04cdbb4256fb811bf08cdce0f635f4ec4f81a544d007a0d0816`, `held_out_start` 524,012),
949 relations (`cefea3d87c7f27700783573f1b313c654babbe1f45870872cf1c24e015ca2d4e`) and its aeons
(`6a87d27224b837deab0c8c997ca39e91cf7559a9a4742d58585c48acc4c5f9f6`). The validation cut opens
inside a conversation whose opening lies before the aperture. Its 11 conversations follow one another
without interleaving: it holds no `switch` letter.

**The projection**, from F0's run on a joined passage of the same aperture (1,047,752 cells), which
took 365,812 ms at a 7,212,138,496-byte peak:
- *The candidate*: the choosing reading about 44,000 ms and the validation reading about 49,000 ms
  (F0: 43,793 and 48,562; the face at 605 letters is read where F0 read it at 936 stops).
- *The candidate's releases*: 8 at most F0's bound at the cap, `2048·(89/4) + 677 = 46,245` ms each,
  so at most 369,960 ms. F0's 32 releases took 190,966 ms in all (`5967 rem 22` ms each).
- *The control*: the flat tree read 1,046,085 bytes in 26,164 ms on an odometer of 8 digits. The
  whole-stream tree reads 1,048,021 cells on 9 digits, projected at most 40,000 ms with its 605
  letter faces.
- *The control's releases*: on the synthetic check the control's scored release cost less than a
  third of the candidate's a cell (`1487/470` against `5902/527` ms). At a third of F0's `89/4` ms
  a cell, a release at the cap takes at most about 15,000 ms, so 8 take at most 120,000 ms.
- *The setup and the two checkpoints*: at most 40,000 ms.

In all at most 655,000 ms, and about 240,000 ms when the releases stop at their own letters. The peak
resident set is at most 10,000,000,000 bytes: F0's egg pass (7,212,138,496) dominates, and the egg is
dropped before the control reads. The run is stopped at 700,000 ms and reported incomplete past it;
its own guards stop a passage past 600,000 ms or 20,000,000,000 bytes. Available memory at the launch:
24,566,611,968 bytes.
