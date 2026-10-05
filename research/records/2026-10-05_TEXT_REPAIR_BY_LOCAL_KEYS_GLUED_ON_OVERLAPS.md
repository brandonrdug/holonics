# Text repair by local keys glued on overlaps

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** B and C of U6 (THE_REBUILD, "U6's
order from October 5", the paragraph "The task is repair, not continuation", its **Text** item).
**Grade.** [definition; agent-inferred] for the pins of §0, fixed and committed before any read
(`a1a9de31`), amended after the development read and before the read (`f28373bf`); [measured] for
every count of §4–§7 (`2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS_receipts/runs.sh` at
`f28373bf`'s build).

**Occasion.** The repair by reflection released every erased cell it certified on the synthetic
terrains ([record](2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md)),
and on text the global turn menu's fibre empties within 4 windows
([record](2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md)): keys
on text are plural and local. This loop runs the repair task on development text with the keys
located per region of a declared cover, glued on the overlaps through the rotor gauge, and the
existing restriction run per glued region.

## 0. The claim and the pins, fixed before any read

**The terrain** [definition; agent-inferred].
- **The data**: the U6 conversation split's choosing role, its flat cut
  (`.local/cuts/curated-u6-choosing-flat-cut.bin`, sha256 `eab73259…5dd2`, 523,215 bytes), in its
  development range `[0, 457751)`. The validation role, the evaluation partition and the cut's
  held-out range are not read.
- **The passages**: `L = 48` bytes each, the field's window (`n + m` of step 1's shape: one span
  within one turn of the source ring, `48 < 60`). **The read, once**: 64 passages, the `i`-th at
  `8192 + 7024·i` (`7024 = ⌊(457751 − 8192)/64⌋`), disjoint from each other and from every range
  the October 5 text loop read (`[0, 6192)` and its requests in the held-out range).
  **Development (timing and checks only)**: the 4 passages at `6192 + 48·j`, `j < 4`, apart from the
  read set.
- **The alphabet** `A`: the 256 bytes. An erased cell starts at the whole of `A`, never at the
  passage's own alphabet.
- **The damage**, the same positions on every passage (cells indexed from 0), interior, the two ends
  intact: single cells `{5}`, `{20}`, `{35}`; spans `[11, 13)`, `[26, 29)`, `[39, 43)`. 12 erased, 36
  intact; the longest span `e = 4`. Whether an erased cell falls inside a word or between words is
  the content's, read only to describe the truth after the release.

**The chart and the field's grain** [definition; agent-inferred]. One cell is one tick of the source
ring. The ports are the byte chart's own, `2⁸` of them, one byte a port, and the turns are `ℤ/2⁸`
(`compression::keys::TurnMenu::open(256)`, the text record's terrain-side reading). Reason: a located
relation reads classes only where a port holds one class (`hnn::keys::LocatedPair::relation` refuses
a folded port), so the residue chart `code mod 60` can restrict no byte. A pixel's or a μ-law
sample's 8-bit codes enter the same chart.

**The cover, derived from the turn menu's certificate** [definition; agent-inferred].
- A turn menu at distance `δ` publishes its map (certifies a key) only when every port it reached has
  its consequence read, which needs at least one edge on each of the `δ` residue chains of `ℤ/δ`:
  `δ` observations, `2δ` cells. The windings law locates a key only when every read distance can
  publish.
- **Reach** `r`: the read distances are `δ ∈ [1, r]` with `r = e = 4`, the least reach at which every
  erased cell of the longest span has an intact antecedent and an intact consequent at a read
  distance.
- **Overlap** `ω = 2r = 8`: the restriction of a region's key to its overlap with a neighbour is
  itself a certified reading (each overlap holds two turns of every read distance), so two regions'
  keys are compared on a certified face.
- **Region** `ℓ = 2ω = 16`, **stride** `s = ℓ − ω = 8`: each region is its two overlaps, and every
  cell but the outer 8 at each end lies in exactly two regions. On `L = 48`: five regions
  `[0,16), [8,24), [16,32), [24,40), [32,48)` and four joins. Every pair `(t − δ, t)` with `δ ≤ r`
  lies inside one region (`ω ≥ r`), so the cover reads every intact pair of the passage.

**The path** (no erased cell's truth is read before the release; the truth is read only to score).
1. **Differentiate, locally.** In each region, one `TurnMenu` a distance `δ ∈ [1, r]` reads every
   edge `x_(t−δ) → x_t` with both cells in the region and intact, in clock order. The region's fibre
   is its surviving distances with their readings (`TurnReading`); its outcome: **unread** (no edge
   read), **empty** (no distance survives), **one** (the windings law locates a generator: the least
   survivor's map published and every other survivor its winding, the law of
   `hnn::keys::PairSurvivors::located`), or **plural** (survivors that are not one class of windings).
2. **Glue.** Two adjacent regions glue at `δ` when the joint menu over both regions' edges admits a
   turn: the rotor gauge `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)` keeps every turn, so a compatible section over
   the two regions is exactly a survivor of the joint menu. The join is read in the tower's trichotomy
   (Lean `Foundation/ContinuingTower.GluingResult`): **unique** (the joint survivors locate one
   generator), **plural** (nonempty, not one class), **obstructed** (both regions keyed, no joint
   survivor); a join with an unread or empty side is **open** (no section on that side). Glued
   regions: along the clock, a region extends the glued region before it while the joint menus over
   all of them keep a survivor; otherwise it opens a new one.
3. **Integrate by reflection.** Each glued region's members are its joint generator when it is one,
   and every joint survivor when plural, each read as a relation on `A` (the published map, or the
   read partial injection: each read port with its consequence, every other class unread). The
   existing `compression::keys::repair::restrict` runs per member over the glued region's cells, from
   both sides; a member whose restriction empties a family is refused by the passage (exact zero) and
   leaves the fibre; each surviving member's restriction is checked by its certificate
   (`Restriction::support`). A glued region's family at a cell is the union over its members of their
   certified families (the joint fibre's projection over the declared family); a glued region with no
   member restricts nothing. A cell lying in two glued regions takes the intersection of their
   families. An erased cell is released through `receiver::release` at tolerance zero when its family
   is one class and every family it read is certified; it is held with its family otherwise.
4. **The codec.** The residual, as the repair owner writes it: while an erased cell is held, the
   truth's index in the first held cell's family in `⌈log₂ |F_t|⌉` bits, that cell pinned and the
   restriction re-run with the same members; decoded by the same steps and checked to reopen the
   passage exactly. The keys are located from the damaged passage's own intact cells, so a decoder
   holding the damaged passage relocates them: the residual alone is the codec; beside it, the keys as
   the owner's `key_code` (`⌈log₂ 255⌉ + 256·⌈log₂ 257⌉ = 8 + 2304 = 2312` bits a member) for a decoder
   that does not relocate. The literal is 8 bits an erased byte, 96 a passage.

**The measures** [definition], over the 64 passages (768 erased cells, 320 regions, 256 joins):
region outcomes (unread, empty, one, plural); join outcomes (unique, plural, obstructed, open);
erased cells released and held, with the held families' sizes; certified fidelity (released bytes
equal to their truth); valid decode: whether each released byte is in the passage's own alphabet (the
bytes of its intact cells) and whether the repaired passage decodes as UTF-8 within every maximal run
of intact and released cells (an incomplete sequence at a run's two ends excused), against the same
reading of the damaged passage; the codec against the literal; the copy length (`tools/copy_length.py`)
of each maximal released span against the training text (the cut's bytes `[0, 6144)`, the October 5
text loop's training passage) and against its own passage's intact cells.

**The show.** The read set's passages 0 to 7, each as its damaged passage (erasures `▯`), its
repaired passage (a held cell `▯` with its family's size) and its truth, written only to the
worktree's `.local/text_repair/` (private) and never committed. This record carries counts only.

**The claim, fixed before the read** [agent-inferred, from the text record's measurement that every
stationary turn fails within 4 to 12 edges].
- Most regions are empty or plural; a region locates one generator only where the text is locally a
  stationary turn (a run of one byte, or of a period whose map is a turn of `ℤ/2⁸`).
- At least three quarters of the erased cells are held (at least 576 of 768).
- **Every released byte equals its truth.** A released byte that differs from its truth is a
  certificate failure of the declared local family on text, and the blocker of this loop.
- Every released byte is in its passage's own alphabet (a one-class family is read from an intact
  edge), and no released byte breaks the UTF-8 reading of its run.
- The residual is at most the literal on every passage (a held cell's family is within `A`); with the
  keys coded by `key_code`, the codec exceeds the literal on every passage that codes a key.

**Amendment, after the development read and before the read** [measured; agent-inferred]. The
development read (the 4 development passages, 48 erased cells; counts only, the bytes stay in
`.local/`) found a defect in step 3 as pinned:
- regions: 13 empty, 7 plural, 0 one; joins: 13 open, 2 plural, 1 obstructed, 0 unique;
- under step 3 as pinned, 2 cells were released and **neither equals its truth**, and one held
  family (253 classes) excluded its truth, so the codec could not reopen 2 of the 4 passages;
- both releases came from plural glued regions whose survivors' maps are unpublished (paths): the
  erased cell was restricted through a read pair at its distance, a byte seen once at that distance
  elsewhere in the region.

Restricting through an unpublished survivor's read pairs reads `x_t` from a pair seen once elsewhere
at the same distance: it is the skip-relation index THE_REBUILD's **Text** item refuses ("the context
tree under another name"), and it repeats lesson 2 (an index of contexts). The turn menu certifies a
key only by publication, and the windings law locates one only as a class of windings; an
unpublished survivor is neither. The amended step 3, **the located law**, is the library's
(`compression::keys::local`):
- a glued region restricts only through its located key: its joint fibre is one class of windings,
  and its member is the generator's published map; a plural glued region keeps its fibre and
  restricts nothing;
- a region extends the glued region before it while the joint fibre over all of them locates one
  generator (every join on the way unique), so a plural region that its neighbour resolves is glued
  into the located key.

The pinned step 3 is read once beside it, in the harness only (`pinned_arm`), as the measurement of
its certificate failure; it enters no library owner. The claim is read on the located arm, unchanged
in its counts; on the pinned arm the read measures how many of its releases are wrong (predicted:
most). The show gives the located arm's repaired passage, with the pinned arm's beside it where that
arm released a cell. Everything else is unchanged.

**The projection, fixed before the read** [measured]. The development unit (both arms on one
passage, one thread) read at most `86` ms over four reads (`86, 85, 84, 84`; the scope's peak at most
`4.4M`, the process's `VmHWM` at most `5,873,664` bytes). The read's projection is `64 · 86 = 5,504`
ms, its deadline the upper end `6,880` ms (`timeout 7`), run in the foreground (under 60 s), one
thread.

**Waiting standard.** A development read on the 4 development passages measures the unit; the read's
projection is the read count times the largest development unit, its deadline the projection's
upper end (`5/4`) under an outer `timeout`, launched in the background past 60 s; peak memory through
`systemd-run --user --wait --collect -p MemoryAccounting=yes`; one thread (the harness is serial,
within the budget of 8); stopped early past the unit bound; no limit raised.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop touched **the
pair** (the contact between crossings `δ` ticks apart, read per region), **the helix** (a distance is
a residue of the source ring's clock; a relation's chains are the residue classes of `ℤ/δ`), **the
tower thread** (the keys as sections over a cover, glued on the overlaps: unique, plural, obstructed)
and **the tube** (the restriction `F_(k+1) = T(F_k) ∩ C_k` per glued region). The cell holonomy (the
turn menu's loop law, unchanged) and faces and placement (not read) stay attached.

## 1. The recorded failures this loop could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md), the
[prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md) and the
[contamination cycles](2026-10-05_THE_CONTAMINATION_CYCLES_EVERY_COPY_PIPELINE_FOLLOWED_A_DEMAND_FOR_OUTPUT_BEFORE_THE_FIELD_COULD_RELEASE.md):
- **2, recitation or an index of contexts.** The pinned step 3 repeated it: a plural fibre's
  unpublished survivor restricts an erased cell through a pair read once elsewhere at the same
  distance, a one-occurrence skip-relation index. The development read caught it (§0 amendment); the
  library refuses it, and the read measures it once beside the located law (§4). The located law
  reads only the passage's own intact cells through a published, located map; nothing is copied from
  another passage, and each released span carries its copy length.
- **3, text as the exception.** The cover, the gluing and the restriction read a clock, a relation
  between two ticks and a class chart: a scan line of an 8-bit image, a μ-law sample stream or a
  motor word's steps enter the same owner. The byte chart (`2⁸` ports) is the boundary codec, chosen
  because the located relation refuses a folded port.
- **Lesson 3, a located cause carried into a new consumer.** The text record's located cause (every
  stationary turn fails within 4 to 12 edges) was named as this loop's expected blocker in the claim;
  §5 measures where it binds at the regions' grain.
- **1, an authored routine.** No distance, map or class is declared to the machine; the turn menus
  decide each region's fibre, and the cover is derived from the menu's certificate and the declared
  damage, not tuned.
- **6, seen graded as unseen.** Nothing carries between passages: each passage's keys are located
  from its own intact cells, and its erased cells' truths are read only after the release. The read
  positions are fresh to the October 5 loops, and the development passages lie apart.
- **7, bits read as progress.** The codec is reported beside the release, never as its success.
- **9, a larger limit.** One deadline from the development read, not raised (§7).
- **11, the programming language.** Stated as residue chains of `ℤ/δ`, turns of `ℤ/2⁸`, and
  sections of a cover glued on overlaps.

## 2. The design

As fixed in §0 and its amendment. The equations at the consumer: per glued region `G` with located
key `(δ, f)` and cells `C_G`,

```text
F_t = ⋂_(G ∋ t, keyed) proj_t { x ∈ ∏_(s ∈ C_G) F_s⁽⁰⁾ : x_s = f(x_(s−δ)) ∀ s, s − δ ∈ C_G }
release_t ⇔ |F_t| = 1, t in exactly one keyed glued region, its restriction certified   (receiver::release, tolerance 0)
reopen(damage(x), residual(x)) = x                                                       (the keys relocated from damage(x))
```

and the gluing of two regions `U, V` at `δ`: a compatible section exists exactly when the joint menu
over `E_U(δ) ∪ E_V(δ)` admits a turn, the rotor gauge keeping every turn.

## 3. What was built

- `crates/holonics/src/compression/keys/local.rs`: `Cover` (its certificate `ω ≥ 2r` and tiling
  refused otherwise), `menus`, `survivors`, `LocalKey`, `relation`, `fibre`, `Join`, `GluedRegion`,
  `LocalRepair::{families, release, residual_code, reopen}`, `locate`; its tests
  (`keys/local/tests.rs`): the cover's refusals; two local keys (an alternation and a constant) glued
  within their halves, open across the empty seam region, every erased cell released equal to its
  truth; and the brute-force check (400 drawn passages over `ℤ/4` where every key and join kind
  occurs: a glued region has a member exactly when its key is one, its family is the member's
  brute-force projection, a member is refused exactly when no completion satisfies it, every released
  cell is its projection's one class, every residual reopens its passage).
- `crates/holonics/src/compression/keys/turns.rs`: the windings law moves here as
  `compression::keys::generator` (the library spine's S2), with `TurnMenu::relation` (the relation as
  read); `hnn::keys::PairSurvivors::located` reads it, its local copy deleted.
- `crates/holonics/src/compression/keys/repair.rs`: the one release decision factored as `decide`,
  read by `Restriction::release` and `LocalRepair::release`.
- `research/notebook/hnn_design/hnn_text_repair.rs`: `executed text-repair <cut> <out> <dev|run>`,
  the located law and the pinned arm (`pinned_arm`, harness only); stdout counts only, every byte to
  the private `<out>`.

## 4. Measured: the read, once

[measured] `run_log.txt` (64 passages, 768 erased cells, 320 regions, 256 joins). The two arms read
the same keys and joins.

| | Located law (the library) | Pinned step 3 (refused, measured) |
|---|---|---|
| regions: unread / empty / one / plural | 0 / 187 / 3 / 130 | the same |
| joins: unique / plural / obstructed / open | 1 / 17 / 27 / 211 | the same |
| glued regions; members; members the passage refused | 319; 2; 0 | 303; 173; 49 |
| erased cells released | **11** (all spaces) | 40 (24 alphanumeric, 16 other) |
| released equal to the truth | **11 of 11** | 15 of 40 (outside passage 58: 4 of 29, on 22 passages) |
| held; with the whole alphabet; family holding the truth | 757; 757; 757 | 728; 446; 670 |
| released bytes in their passage's alphabet | 11 of 11 | 40 of 40 |
| passages reading as UTF-8 (damaged / repaired) | 64 / 64 | 64 / 63 |
| residual against the literal (bits) | 6,056 = 2³·757 against 6,144 = 2¹¹·3 | 2,216 on the 24 passages it reopens; 40 refused |
| keys by `key_code` (bits) | 4,624 = 2·2³·17² | 399,976 |

- **The located law.** The three located regions are one passage's (58): an indentation run of
  spaces, regions 0, 3 and 4 each the identity at `δ = 1`, the join of regions 3 and 4 the read's one
  unique join. It releases 11 of that passage's 12 erased cells, every one equal to its truth; the
  twelfth, inside a three-byte UTF-8 sequence beside the run, is held with the whole alphabet. On the
  other 63 passages nothing is located and every erased cell is held with the whole alphabet. No
  certificate failed.
- **The codec.** The residual is the literal less 8 bits for each released cell (`6144 − 8·11`); the
  64 passages reopen exactly. The keys, if coded rather than relocated, cost `2,312` bits a member,
  above the literal on passage 58 (`4,624 + 8` against 96).
- **The pinned step 3** releases 29 cells outside the indentation run, 25 of them wrong, and 58 of its
  held families exclude their truth: the certificate failure the amendment predicted (most of its
  releases wrong). Its 173 members are the plural fibres' unpublished survivors; the passage itself
  refuses 49 of them (a family emptied through an erased chain).
- **Copy lengths** (`copy_lengths.txt`). The located arm's five released spans (lengths 1, 1, 2, 3, 4)
  have copy lengths 1, 1, 2, 2, 2 against the training text and equal to their lengths against their
  own passage's intact cells (spaces). The pinned arm's 33 spans: copy length 0 at 2, 1 at 27, 2 at 4.
- **Inside words.** 584 of the 768 erased truths are alphanumeric; the located law releases none of
  them.

## 5. The show, and the blocker

The read set's passages 0 to 7, as pinned, are in `.local/text_repair/run/shown.txt` (private, not
committed), with passage 58 beside them as the read's only located release. On all eight the located
law holds every erased cell with the whole alphabet (96 cells); the pinned arm released 5 cells on
four of them, 2 equal to their truth.

**The blocker, by its measurement.** At the regions' grain (16 bytes, distances 1 to 4), no
stationary turn of `ℤ/2⁸` publishes its map on text outside a run of one byte: 187 of 320 regions
lose every distance, 130 keep only unpublished survivors (paths), and 3, all in one indentation run,
locate. The gluing does not repair it: 211 of 256 joins have an unkeyed side, and of the 45 between
keyed regions, 27 are obstructed and 17 plural. So the located law releases only inside a run of one
byte (11 of 768, all right), and the plural fibres, read through their read pairs, release mostly
wrong bytes (25 of 29 outside the run). The local stationary-turn family is not the passage's
relation on text at this grain; its plural fibres are evidence of absence of a conflict, not of a key.

## 6. Owed in #62

1. **The gluing through the rotor gauge**: two regions' turn-menu fibres at `δ` have a compatible
   section, up to the gauge, exactly when the joint menu over their edges admits a turn; with the
   tower's trichotomy (`Foundation/ContinuingTower.gluingResult_total`) over the cover's chain.
2. **The cover's certificate**: `ω ≥ 2r` puts every pair `(t − δ, t)`, `δ ≤ r`, inside one region, and
   gives each overlap an edge on every residue chain of every read distance.
3. **A located glued region's family is its member's projection**: the repair's projection law (owed
   by the repair record) on the glued region's cells; the intersection across an unglued overlap
   encloses the joint projection.

## 7. Time and memory

One thread (the harness is serial, within the budget of 8); `run_log.txt`, `run_scope.txt`,
`dev_log_{1,2,3}.txt`.

| Run | Projection / deadline (ms) | Measured (ms) | Peak resident |
|---|---|---|---|
| development (4 passages, both arms), three reads | — / guard 300,000 | 154, 152, 150 (units at most 85) | `VmHWM` at most 5,873,664 bytes; scope at most `4.4M` |
| development, the pinned arm alone (before the amendment) | — / guard 300,000 | 154 (units at most 86) | `VmHWM` 5,947,392 bytes |
| the read (64 passages, both arms) | 5,504 / 6,880 | 4,971 (scope runtime 4,993) | `VmHWM` 6,160,384 bytes; scope `7.5M` |

Measured over projected: `4971/5504`. The per-unit bound `108 = ⌈86·5/4⌉` ms was passed by 19 units
(the first, passage 2, at 121 ms; the largest, passage 12, at 487 ms), all by the pinned arm's
certificates over plural glued regions of up to 4 members (the development passages held at most 2).
The harness declared no in-run stop and no watcher applied the bound, so the read was not stopped
early: a departure from the waiting standard, reported as such. It finished inside its projection and
deadline.

## 8. Commits and gates

- `a1a9de31`: the claim and the pins, before any read. `f28373bf`: the owner, the harness, the
  development receipts and the amendment, before the read. This record's commit: the read's receipts
  (counts only: `run_log.txt`, `run_scope.txt`, `copy_lengths.txt`, `runs.sh`), §1–§8, the atlas row
  `compression.local-keys-glue` and `hnn.pair-location`'s owner, the operator contract's `local`, and
  the records README route. No byte of text is committed.
- Gates: `cargo check --workspace --all-targets` clean (the one pre-existing dead-code warning,
  `ReceivingPhases::with_rank`); `cargo test -p holonics --lib -- --test-threads=8 compression::keys
  hnn::tests::keys`, 37 passed and 0 failed (14,795 ms wall with its build); the guard lints
  (`cargo clippy -p holonics --lib -- -D clippy::disallowed_types -D clippy::disallowed_methods -D
  clippy::float_arithmetic`) report nothing in the changed files beyond `result_large_err`, which every
  `CompressionError` owner carries (the run stops at a pre-existing default-deny
  `while_immutable_condition` in `hnn/reference.rs`, untouched here); `Cover::declare`'s tiling test
  reads `is_multiple_of` after the read, the same condition. No Lean changed (§6 names the
  obligations); no card run (no kernel or card path changed).
