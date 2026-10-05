# Text repair by local keys glued on overlaps

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** B and C of U6 (THE_REBUILD, "U6's
order from October 5", the paragraph "The task is repair, not continuation", its **Text** item).
**Grade.** [definition; agent-inferred] for the pins of §0, fixed and committed before any read.

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
