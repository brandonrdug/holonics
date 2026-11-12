# A lap's card time stands in the opening's empty room, a lap line's sites are weighed domains, a stretch of a document takes one keyed state, and every extent of the declaration is given its part

Refs #404 #407 #410. Status: [measurement, review and design; November 12], by the theory thread
that holds the PC's runs and the engineering since 17:13Z (the guess file's hand-off line). The measurement is a count
ruler run on the PC's host against te7's own lap log (P47); no card was taken and nothing was
built. The design in §4 is agent-inferred and not built; its rate is fixed as G115 before its
build is read.

Owners named: `hnn::tower::field` (`ClassLists::support`, `Region`, `Port`,
`FieldDeclaration::room_window`, `FieldReceipt`, `FieldLearner::section_realized`,
`FieldDeclaration::{grown, laned}`), the trainer
(`crates/holonics/examples/solenoidal_alpha/complete_language/field_train.rs`: `FieldCodec`,
`section_regions`, `opening_region_with`, `writer_region`, `shape`, `train`), the card realization
(`crates/holonics-cuda/src/hnn/field.rs`: `region_octets`, `batches`). Atlas:
`tower.field-open-row-pairs` (new), `tower.field-support-stride`, `tower.face-lane-composition`,
`tower.field-card-realization`.

## 1. The count

**What was not known.** A lap's lines print `sites`, and the line's rate was stated from them: te7
read "16,589,049 sites" in 1,268 s. That count is `FieldReceipt.sites` (`field.rs:5733`, formed at
`:6610`): each region's weighed domain where it read an open site, the sites its code is a code
of. It is not the count of sites the card computes. Every site of every region is a receiving row
on each head and tick, whether it is compared or not.

**The ruler** (`section_regions_census.py`, the passage record's receipts). It rebuilds every
training region of a lap from the passage, the held file and the key file by the trainer's own
rules (the keyed order of sections, the lap's walk, its path problems, each mask, each path state
and each writer state, under the switches the lap ran under), and counts them by kind of state. Its
counting forms are held to a literal port of the trainer's lists (4,000 drawn cases). It reads no
state and takes no card.

**The known case, first.** te7's log prints `sites` and `length` (the longest region) for each of
its 1,535 sections. The ruler computes both for every section: 1,535 of 1,535 equal on each, and
its own count of the answer extent, the trained, withheld and held problems and the sections equals
the log's declaration line. The four kinds' domains sum to 16,589,049, the lap's printed total.

**The lap by kind of state** (te7: 24,557 problems, 16 a section, 73,671 regions; `te7_regions_census.txt`):

| kind of state | regions | sites computed | share | sites squared, share | open rows' pairs a head and tick, share | sites the lap line counts |
|---|---|---|---|---|---|---|
| mask over the whole region | 12,312 | 5,709,014 | 0.075 | 0.029 | 0.059 | 5,713,063 |
| mask over the answer | 12,245 | 5,569,543 | 0.073 | 0.028 | 0.057 | 4,064,567 |
| the opening: the question and the whole room | 24,557 | 53,739,203 | 0.704 | 0.886 | 0.732 | 294,684 |
| the writer's state given its end | 24,557 | 11,278,557 | 0.148 | 0.057 | 0.152 | 6,516,735 |
| the lap | 73,671 | 76,296,317 | 1 | 1 | 1 | 16,589,049 |

- The card computed 76,296,317 sites in the lap, 4.6 times the count on the lap's lines, and
  49,704 a section.
- An opening is its question and the codec's whole answer extent, 2,062 places (the longest
  training answer and one), every one of them open: 2,188 sites on the mean, 3,771 at the longest
  question. It compares 12 of them (the first place and one keyed place in each of the 11 octaves
  past it, at the boundary of letter and void). The openings are 0.704 of the sites the card
  computes for 294,684 compared places, 0.018 of the lap's.
- The card reserves its weights a pair of a region's sites (`region_octets`: 280 octets a pair at
  4 heads and 4 kept ticks, returning). The openings hold 0.886 of the lap's sum of sites squared: a
  mean section's regions reserve 24.3 GB, 21.5 GB of it for 16 openings, so a section is split
  into about four batches (6,447 batches over the run's 1,630 reads, its peak 8.44 GB). Without
  the openings a mean section reserves 2.8 GB a pair and 1.0 GB a site: one batch.
- An open row meets every definite site of its region once on every head and tick
  (`ClassLists::support`, the open receiver; atlas `tower.field-open-row-pairs`): open times
  definite pairs, a count that does not read the state. The lap's open rows meet 8,740,596,881
  pairs a head and tick, 0.732 of them in the openings (2,062 silent places each listening to the
  whole question). A definite row meets its near field (141,788,334 a head and tick over the lap)
  and its probed classes' definite members, which read the state, at most 6,460,981,704 more.
  Over 4 heads and 4 ticks the lap's training reads meet between 142.1 and 245.5 thousand million
  pairs; the card's own count for the whole run, its held and withheld reads included, is
  160,100,331,669. The openings' open rows alone are 102.4 thousand million of them, 0.64.

**Corrected figures** (this thread's own, written earlier the same day from the lap lines' count
and repeated in the state guide, the plan and the guess file; each is corrected where it stood):
- "13,000 sites a second" was 13,086 weighed domain sites a second. The card computed 60,180
  sites a second (76,296,317 in 1,267.8 s).
- "672 sites a region" was the lap lines' count over the lap's problems. A region is 458 sites on
  the mean where it is a mask or a writer's state and 2,188 where it is an opening.
- "about 11,700 pairs a training site" divided the card's pairs by domain sites. A computed site
  meets 116 pairs a head and tick on the least count (8,882,385,215 over 76,296,317), 1,863 over
  the 16 of a read.
- The line's rate in bytes stands: 11.6 MB of questions and answers a lap, 9.2 KB a second.

## 2. Why every opening computes its whole room

The source, read at main `8f9edb018`, and the lap's settings (`te7_lap_settings.txt`):

1. The line trains under `FIELD_PATH_OPENING`: the only path state is the fully masked one, so
   every path problem's region is its question and the room, with nothing resolved past the
   question (`opening_region_with`, `k = 0`). Its reason stands on the record of November 6: the
   length is decided at the release's first read, where the void's mass at each place is the
   length's distribution.
2. Under `FIELD_PATH_FAR_KEYED` it compares the first place and one keyed place an octave. The
   places between are read and not compared.
3. `FIELD_ROOM_CUT` is exported too: the opening would compute only its question and the windows
   of its compared places, `(NEAR − 1) · ticks` places on either side, about a sixth of the room.
   Since the carry circles entered (November 11) `FieldDeclaration::room_window` returns none where
   the declaration holds a circle (`field.rs:509`): a circle's scan carries a place's state the
   whole strand inside one tick, so a face in a window reads places outside it and the cut no
   longer keeps the bits. The export stayed in the lap's script and has had no effect on this line.
4. Every one of the room's 2,062 open places is a receiving row that listens to every definite
   site (the question), on each head and tick.

So the circle line pays, each lap, for 53.7 million sites of silent room in order to compare
294,684 places. The room is the code passage's own extent: it is the longest of 24,685 answers,
where the median answer is 247 places.

## 3. The time, from the lap's own sections

The log prints each section's deposit time. Against the ruler's counts for the same section (1,535
sections; `CENSUS_FIT`):

`deposit ms = 38.4 + 0.008746 · sites computed + 0.000003747 · pairs`, pairs the least count over
the read's 16 head-ticks; it explains 0.745 of the sections' variance (sites alone 0.615, pairs
alone 0.715). Of a mean section's 820 ms, 435 follow the sites, 347 the pairs and 38 neither. The
profiled run's 223 sections read the same form (0.01094 and 0.000003875, 0.757).

Applied to the openings, their sites (35,010 a section) carry 306 ms and their pairs 251 ms: 557
of 820 ms, about two thirds of a lap. The limit of that reading: every section holds the same
sixteen rooms (35,006 to 35,028 sites by tenth of the length order), so the fit reads the rate of
a site from the masks' and writers' sites, which vary, and cannot tell a room's sites from a cost
every section pays once. The pairs' part does not share that limit. A lap without the rooms would
measure it directly; none is ordered, because the next line holds no room (§4) and a lap of the
code line with its length law removed would be a change of law run for a timing.

By tenth of the length order, a section's deposit runs from 753 ms (masks of 2,319 sites) to 1,130
ms (masks of 19,306 sites); the rooms and the writers' states are the same in every tenth, since a
section's path problems are a keyed draw of the whole passage.

## 4. What follows for the wider passage: a stretch takes one keyed state, and a section is declared to fill one batch

The documents store is on the PC (P46: 8,000,075,453 text bytes of whole documents; code
3.2 GB, web 1.6, science 1.6, books 0.96, wikidata 0.64; a prefix of 1 GB; 128 held documents a
slice from the far end of the shard order; `corpus_store.txt`). A document has no question and no
answer, and no room. The design, each choice with its reason (agent-inferred; none built). Its cut
is stated draw by draw in the head of `store_stretch_census.py` (the receipts), the reference port
the trainer's own lines are held to, as te7's were held to the first ruler:

1. **A stretch is a keyed run of a document.** From a cursor, a context of `q` places and a run of
   `a` places past it, each drawn on an octave uniform over `[4, 8)` to `[256, 512)` and uniform
   within it, so a stretch is 8 to 1,022 places and 217 on the mean. The void stands only where
   the document truly ends inside the stretch, with the near tail past it; a stretch cut by its
   draw ends at its last place. A stretch that would leave fewer places than the least context
   (4) takes them. The cursor moves on by the whole stretch, so a pass meets each byte in one
   region. A piece that opens with a title is read as the title, one line feed and the text (the
   store keeps no separator). Reason: every octave of context and of run is met alike (the tail's
   and the path states' own law of octaves), and the longest region follows from the draw, never
   from the passage's longest item. The octaves' range is chosen: the least stands under the near
   field (6 places), and the longest stretch, 1,022 places, stands near twice the code line's mean
   mask region (458) and well inside the declared reach (3,771), so no ring is asked a distance the
   code line never gave it. The range is carried in the learner's state, and a wider one is a
   crossing with its own guess.
2. **One state a stretch, keyed.** With even odds a mask state (over the whole stretch or past the
   split, the density `τ = u²` and the weighed domain as now) or the writer's state (the context
   known, the run's places in the writer's octave order from the split, its first `k` resolved,
   `k` by octaves of reads, `k = 0` among them, compared on their classes). Reason: the code line
   visits one problem with three states a lap because its passage is small and is lapped; a pass
   over fresh text meets a new stretch at every draw, and a second state of the same bytes buys
   less than the next stretch does. The fully open run (`k = 0`) is the release's first read; no
   state is compared at the boundary alone, since the end is learnt where documents end.
3. **A section is a declared bound, sized to one batch of the card.** A section takes stretches in
   order until its regions' pairs of sites or its sites would pass a bound carried in the learner's
   state; the bound is set once from the card's reservation at the declaration and changes only at
   a declared crossing (a growth of the constitution). The first bound: 15,606,223 pairs of sites
   and 41,490 sites, which reserve nine tenths of te7's one-batch peak store (8,440,325,846 octets)
   at 280 octets a pair and at the octets a site that 257 classes take (77,766: 71,486 at 100
   classes and 40 a class more), split at the cut's own mean of 376.1 pairs of sites a site
   (`store_stretch_draw.txt`). Reason: the batch a card computes together is a schedule, but
   a section is the unit a deposit consumes, so its extent is law and is carried in the state; a
   section read from the device's free memory would let the bits follow the schedule. The step's
   rate stays the line's: te7 holds 12 under `FIELD_STEP_HELD` and prints the transfer's price
   without acting on it, and the store's line carries the held rate in the learner's state and
   prints the same price over each declared count of sections. A section of about 186 regions has
   a different noise from te7's 48 regions over 16 problems, so whether the rate should move is
   read from that price as a guess of its own, and nothing here assumes it.
4. **The letters are founded at a passage's crossing.** The codec holds the 99 bytes the code
   passage used, with the void as its last class, and refuses any other byte
   (`field_train.rs:79-82`). At the crossing to a store the bytes the store holds and the
   constitution does not are founded once, in byte order after the classes that stand: every class
   that stands keeps its index, the void its own, and the open row moves to the end of each letter
   family. A fresh letter's every row opens at zero (its row of the encoding, its rows of the two
   strand encodings, its rows of the moment encodings and its rate in each paced head's clock,
   which is the bare rate), and its class bias opens at the least class bias the constitution
   holds. Reason: the face reads a class through the encoding that
   encodes it, `z(a) = ⟨E(a), R r̂ + b_R⟩ + c_a`, and a site's opening face is a sum of rows,
   `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))` and its moment's term (`Field::open`). A founding
   draws these rows because what reads them stands at zero and every class reads flat; here every
   reader is trained, and a drawn row would read each fresh letter at a random height at every
   face and would be heard beside it as a letter it is not. At zero a fresh letter reads the same
   at every face, at the share the least-favoured letter the constitution knows is given, and each
   of its rows takes its covector from the first face compared and from the first place the letter
   stands at or beside; the sum has no product of two fresh rows, so none waits on another. The
   founding reads no key. [Corrected November 12, 18:44Z, before any build: this item first drew
   the two strand rows from the key stream, by the founding's habit and with no reason of its own.]
   No founding of a letter leaves every face's bits, so its
   price is read on the code line's held passage before and after it. It moves a standing face by
   two routes: the fresh classes' share at the face itself, and, on a paced head, a blank's clock,
   which runs at its own face's expected rate, `κ_h = 1 + Σ_a p(a) c_h[a]` (`Field::paces_with`),
   so the fresh share moves the clock and through it the standing logits. The readout's map is
   kept entry for entry, and the whole read is kept where no head is paced (found in the build of
   November 12; the growth's test is stated that way). The fresh entries' moments
   and rates open as the growths of November 10 to 12 open theirs (the first moment at zero, the
   second at its family's mean, the base rate). A byte no document of the store holds gets no
   class.
5. **The read is by stretches from the store's files**, never a whole passage in memory (the
   passage is read whole under a 64 MiB budget today, `complete_language.rs:46`); the slices are
   interleaved by least progress against their quotas, the held read is by slice from whole held
   documents, the level is read at means of states over a declared count of sections, and the
   state is saved at least each hour. The pass's place (each slice's piece and cursor, the count
   of stretches), the octaves' range, the section's bounds and the law of its states are one line
   of the learner's text, which no state of the code line holds, so the code line's states are
   read and written as before.

**The ruler drawn on that cut** (`store_stretch_draw.txt`: 100,000 keyed stretches of a piece with
no end): a region is 217 sites and 81,440 pairs of sites on the mean, and a section under the
bounds holds 186 regions and 40,371 sites; 0.325 of the computed sites are open, every one of them
compared (on te7's lap 0.792 are open and 0.132 compared); a computed site meets 54.2 pairs a head
and tick on the least count (116 on te7's).
Priced at te7's own rates (§3), a computed site costs 8.75 µs for itself and 3.25 µs for its
pairs, 12.0 µs, and a pass meets one computed site a byte: 83 KB a second against the line's 9.2,
before any kernel is changed. The letters' growth adds to the entries that follow the alphabet
(the encodings' and readout's families, 0.13 of the profiled kernel time at 100 classes).

**G115** is fixed on this in the guess file before the build's first timed read: 15 µs a computed
site all told (11 to 19), one batch a section, the pairs' term 0.20 to 0.35 of a section's time.
At 15 µs the prefix of 1 GB passes in 4.2 hours and the 8 GB in 33.

**The code line** stays as it is. No build is spent on its room: the cut that kept its bits is
gone with the circles, and a cut that does not keep them is a change of the length law for a line
the store replaces. The code passage stays the yardstick, read by release from held prompts.

## 5. The review: the source against the standing flags

The flags, in the agent's words, with the days Brandon raised them:

| | flag | raised |
|---|---|---|
| F1 | A value is a word at declared widths that follow its information: no width picked by hand, doubled or fixed for a series; one number system across the code; no value is called exact. | October 14 and 18, November 5, 7 and 8 |
| F2 | Learning runs on the card, the workload is never cut for time, and a long projected run is a sign of poor use of the card. | October 27 and 29 to November 5 |
| F3 | An extent follows from a partition of branches or of information: never from doubling, a copy, a factor or a pad to a power of two. | October 31, November 3, 5, 10 and 12 |
| F4 | A behaviour that matters is law carried in the learner's state, never a run switch. | November 8 |
| F5 | A reading names its region; a figure is read at its source before it is repeated. | November 11 and 12 |
| F6 | No extent is a property of the machine: it is stated with the part it sizes. The constitution, a region's current and a receiver's locale are three things, and "the field" names none of them. | November 12 |
| F7 | Inputs are raw bytes, and every design is checked against text, image, sound and motion; what is special to a medium lives in its boundary chart. | October 29 to November 5, and the lessons |

Findings, read at main `8f9edb018`, each with the flag it breaks and the build that closes it:

| | where | what stands there | flag | closed by |
|---|---|---|---|---|
| R1 | `hnn/tower/field.rs:509`; the lap script's exports | Every opening computes its whole room since the circles; the room's cut is exported and inert (§2). | F2 | The store's trainer holds no room (§4). |
| R2 | `field.rs:5733`, `:6610`; `field_train.rs:1348` | The lap line's `sites` are weighed domains under the name of sites; the line's rate and three figures were stated from it (§1). | F5 | The store's trainer prints, by kind of state, the regions, the sites computed and the domain; the old line's word is left as it is. |
| R3 | `field_train.rs:1183` | The declaration line prints the launch's arguments (`width=32`, `contacts=32`) where the continued state holds two lanes of 32 and 128 contacts. | F6 | The line prints the state's declaration by part. |
| R4 | `field_train.rs:1457-1460`, `:1199`; `field.rs:439-443`, `:448-451`, `:6346` | The default growth is still "by two" (`widened(2)`), held off only by an exported variable; `FIELD_WIDEN_FIRST` defaults to two; `grown` multiplies width, contacts and lanes by a factor; `laned` adds a lane of the first lane's width. | F3 | The default growth is retired; a growth is a declared composition (a lane of a width its readers' partition gives, letters at a crossing), each its own guess. |
| R5 | `field_train.rs` (26 variables read; 38 across the trainer, the tower and the card) | The line's law stands partly in the lap script: the path states' law (`FIELD_PATH_OPENING`, `FIELD_PATH_FAR_KEYED`, `FIELD_PATH_WRITER`), the held step and the step's transfer (`FIELD_STEP_HELD`, `FIELD_STEP_TRANSFER`), the held growth (`FIELD_GROWTH_HELD`). | F4 | The store's trainer reads no variable for its law: the states' law, the section's bound and the step's law are carried in the learner's state. The comparisons the variables declared stay in history. |
| R6 | `field_train.rs:52-82` | The letters are the first passage's bytes; an unseen byte is refused; the void is whichever class is last. | F7 | Letters founded at a crossing, the void at a kept index (§4, 4). |
| R7 | `complete_language.rs:46`, `:59` | A passage is read whole under 64 MiB. | F2 | The read by stretches (§4, 5). |
| R8 | `field_train.rs:1096` (`SECTION`); `holonics-cuda/src/hnn/field.rs:2724-2727`, `batches` | A section is a count of problems fixed at the launch (16); its regions are split into about four batches; the weights are reserved a pair of a region's sites. | F2, F3 | The section's declared bound (§4, 3); then the store on its support (`tower.field-support-stride`), which halves what a pair reserves. |
| R9 | `field.rs:185`, `:192`, `:859`, `:1435` and the grains beside them; `holonics-cuda/src/hnn/field.rs` (`MIN_LIMBS 5` to `MAX_LIMBS 20` limbs of 64 bits); 422 `i128` in `hnn/tower/field.rs`; `hnn/tower/field/moment.rs:148`, `hnn/tower.rs:287` | Seven grains fixed by hand (`2^(−16)`, `2^(−24)`, `2^(−30)`, `2^(−40)`, `2^(−62)`, `2^(−63)` and the covector's `2^(−24)`); a row's sum on 5 to 20 limbs of 64 bits by its spread; raw 128-bit carriers whose overflow refuses a lap; `holonics::number` consumed by two census calls. | F1 | After the trainer: the contact's and the site kernels' terms at the widths they need, read entry by entry from a profile of the store's line; the number owner adopted where a carrier refused. |
| R10 | `field.rs:1367`; the record of November 1, §15.9 | The open receiver's law stands, and its written reason is the crib fixture's, retired since as copy-shaped. | (a rule without its reason) | Its reason is restated at the owner at the next build there: an open place's probe carries no letter, so a sharp address would file every open place under one class; it listens to what is definite. [agent-inferred] |

**Every extent of the built declaration, with its part** (te7's state `hnn-field-v14e`; the
constitution's 80,182 entries by block are in the atlas row `tower.face-lane-composition`):

| extent | part it sizes | how it was reached | what sizes it |
|---|---|---|---|
| 100 classes | the face's letters: 99 bytes and the void | the first passage's census | the passages met, at each crossing (R6) |
| 64 coordinates as lanes (32, 32) | the face chart every block reads; a block's rows are as long as the lanes it reads | 32 a launch argument; the second lane a copy of the first's width | the partition a lane's readers hold; G114 could size none from the travel between lap means |
| 4 heads (2 still, 2 turned), 4 ring sets | the heads' charts (20,480 entries); the contact's rows a site | launch arguments | not derived on record: chosen at the founding |
| 8 complex modes a head; 4 shell trits, 81 classes a head | a head's key and probe; its resonance classes | the modes a launch argument; the trits the least `k` with `9^k` at or past the reach | the reach gives the trits; the modes are chosen |
| 128 pair contacts (64 complex), 32 of them carry circles | the strand's contacts (24,576 entries) and the circles' charts (4,096) | 32 at the founding, then 64 and 128 by copies; the circles the last half | a count by need: the added contacts each travelled their own direction (November 11); no derivation of the count stands |
| 4 ticks | a region's clock a read | launch argument | chosen |
| reach 3,771 | the rings' coarsest closures, the class trits, a row's bits | the longest question (1,709) and the room (2,062) of the code passage | the longest region the cut can draw: 1,028 for stretches |
| the room, 2,062 places | the opening state and the release | the longest training answer and one | none in the store's line (§4) |
| NEAR 6 | the near field, a region's tail, a circle's founded group (5), a window | the readings of November 5 and 11 | on record with its reasons |
| 16 problems a section | a deposit's regions | launch argument | the section's declared bound (§4, 3) |
| 280 octets a pair, 71,486 a site | the card's reservation at this declaration | `region_octets` | the declaration; a pair's falls with the store on its support |

The module, its types and its lines keep the name `Field` where the code is cited; no rename is
ordered.

**The order of builds this sets** (each enters by its receipt; the first is a new line and has no
lap to reproduce, and its binary reproduces te7's lap with the old trainer untouched):
1. The store's trainer: the read by stretches, one keyed state a stretch, the section's declared
   bound, the letters at the crossing, its lines by kind of state (R1, R2, R3, R5, R6, R7, R8's
   first half); G115 on its first timed sections.
2. One continuous pass over the 1 GB prefix from te7's state, judged by what it writes from held
   prompts by slice and by its structure measures.
3. From that pass's profile: the terms at their widths (R9), the store on its support (R8), the
   batch's tables staged under the card's stroke.
4. The face as a composition of lanes, and a lane whose width a reading of the pass names (R4),
   fixed as its own guess.

## 6. What this review did not read

The reverse's host code and the moments (`hnn/tower/field/moment.rs`) beyond their entry points;
the release and the writer (`sample_realized`, `sample_runs`); the tower (`hnn/tower.rs`); the
bodies of `grown`, `laned`, `contacted`, `with_carry` and `with_triads`; most of the kernel file
past the contact, the exposure, the circles' scans and the paced skin's reverse; the Lean package;
`tools/runs.py`. The 38 variables were counted, not each read at its use. A finding there is
owed to the build that first touches it.

## 7. Owed to #410

- The founding of a letter at the least class bias: each old face's share of a class moves by at
  most the fresh letters' joint mass, stated with the bound a face reads (not written).
- A section's declared bound keeps the card's reservation inside one batch for every draw of the
  cut: the bound on pairs of sites and on sites against `region_octets` (not written).

## 8. Receipts

In the passage record's receipts directory (`2026-11-12_THE_PASSAGE_WIDENS_..._receipts`):
`section_regions_census.py` (the ruler, with its self-test), `store_stretch_census.py` (the
stretch cut's reference port and its ruler) with `store_stretch_draw.txt`, `te7_regions_census.txt`
and `tp2_regions_census.txt` (P47: host only, one thread, no card; 4.6 s and 55 MB each),
`te7_lap_settings.txt` and `corpus_store.txt`, `corpus_store.tsv`, `corpus_manifest.tsv` (P46: the
fetch in 1,074 s against its 5,400 s deadline, peak resident set 1.3 GB, 99 shards at 10.7 s a
shard). The stretch cut's draw is this thread's run of November 12 on a cloud host (arithmetic on
drawn integers; no passage, no card).
