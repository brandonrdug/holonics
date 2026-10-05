# The same path on text: key location and the release on the byte chart

**Date.** October 5. **Issues.** #73, #148, #63. **Lanes.** B and C of U6 (THE_REBUILD, "U6's order
from October 5"), on text. **Grade.** [measured] for every count below (the runs of
`2026-10-05_THE_SAME_PATH_ON_TEXT_receipts/runs.sh`, at this record's commit); [agent-inferred] for the
pins.

**Occasion.** Lanes B and C passed U6 step 1 on order-2: the turn menu located the key from 16
observations, the certified step deposited it, and the release read it on equal material, 128 of 128
sections whole on the final confirmation
([B](2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md),
[C](2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md)). The plan requires every loop
to show Brandon a text release, and none has been shown since September 29. This loop runs that same
path, with no new machinery, on a passage of real text, and shows what it releases.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop reads **the helix**
(a distance is a residue of the source ring's clock), **the pair** (two crossings `δ` ticks apart, the
menu's edge) and **faces and placement** (the ring's ports, the residue chart `code mod 60`, and the
bank's reading of each candidate's placement); the cell holonomy (the menu's loop law), the tube and
the tower thread stay attached and unchanged.

## 0. The claim and the pins, fixed before any run

**The claim.** The deliverable is the measurement and the output, not a pass: the turn menu's
survivors by distance on a text passage, and one release per request, shown whole with its copy
length (guard 19). No acceptance is claimed.

**The data** [agent-inferred]. The U6 conversation split's choosing role, its flat cut
(`.local/cuts/curated-u6-choosing-flat-cut.bin`, sha256 `eab73259…5dd2`, 523,215 bytes; development
partition, the reserve excluded by its manifest, the evaluation partition outside the stream). The
validation role and every spent split's validation role are not read.
- **The training passage**: the cut's bytes `[0, 6144)`, read as 128 consecutive windows of
  `n + m = 48` bytes, each a request of 40 cells and its section of 8 stations: the order-2 terrain's
  training shape, `1,024 = 2¹⁰` observations.
- **The requests**: 16 windows of 48 bytes in the cut's held-out range `[457751, 523215)`, the `i`-th
  at `457751 + 4091·i` (`4091 = ⌊65464/16⌋`), each a request of the last 40 bytes and its truth, the
  next 8. They are disjoint from each other and from the training passage; no run of this loop
  reads them before the pinned run. (The September 29 text runs read this cut, with other machines;
  nothing of them enters this one: every state here is the declared opening or its deposit.)
- **The development window** (timing only): the bytes `[6144, 6192)`, the window after the training
  passage.

**The field** [agent-inferred]. The order-2 declaration unchanged (`hnn_prediction.rs`,
`order_declared`: three rings of period `60 = 2²·3·5` in a chain, ring 0 the source and receiving
ring, `K = 2`, `w = 1`, `m = 8`, `n = 40`, the bank at `p = 5/8` read at `2^(−16)`), with the exterior
chart the byte chart: `|A| = 257`, the bytes `0 … 255` and the termination `256`. The ring's ports are
its residue chart, `port(x) = x mod 60` (guard 9), so each port holds four or five bytes. `Field::declare`
fixes the rings without the alphabet, so the field is the one step 1 read.

**The path.** `executed text <cut> <out> run` (`hnn_keys_loop.rs`): lane B's location
(`hnn::keys::{station_pairs, PairLocation}`, every distance `δ ∈ [1, 59]` its span reaches), each
distance's menu followed to the observation at which it fails; at a first lock, `pair_deposit` on both
openings and the release on the deposits; with no lock, the release on the lossless and the founded
openings (`generate_by_bank`, lane C's owner, unchanged). Beside it, a terrain-side reading only: the
same edges on the bytes themselves (a turn menu a distance on 256 ports), separating the residue
chart's fold from the passage's own relation. The released stations are decoded to bytes through the
byte chart; each release's copy length (`tools/copy_length.py`) is read against the training passage
and against its own request. Every byte is written only to the worktree's `.local/text_loop/`.

**Thread budget** 12 (`RAYON_NUM_THREADS=12`).

**The projection, fixed after the development read and before the run** (`dev_log.txt`). The
development window read no lock on the training passage, so the run reads the two openings. A
request took `6,208` ms on the lossless opening and `48,032` ms on the founded opening (one request
alone at 12 threads, the bank's own candidates in parallel). The projection is 16 times their sum,
`16 · 54,240 = 867,840` ms; its upper end, `5/4` of it, `1,084,800` ms, is the deadline (an outer
`timeout 1085`). Early stop: the lossless state's line is due by `16 · 6,208 · 5/4 = 124,160` ms; a
later line stops the run, reported incomplete.

**The run stopped early, and the next read, fixed before its launch** [measured; agent-inferred].
The pinned run's lossless line came at `150,953` ms, past its early-stop bound `124,160` ms, and the
run was stopped at `189,102` ms (`run_log.txt`), its lossless state complete and its founded state
unread. The projection error is measured: another worker's 12-thread run (`executed evaluate`, a
454 s deadline) started 48 s before it on this host of 12 physical cores with two threads each, so
the two runs shared the cores the development read had alone (lossless: `150953/99328` of its
projection, 1 rem `51625/99328`). The deadline is not raised; the declared read changes:
- **the founded opening alone** on the same 16 pinned requests (the lossless state is complete), the
  requests read **one after another**, each with the whole thread budget: the unit the development
  read measured, with one progress line a request (`executed text … run founded`);
- **the projection** is the founded state's share of the pinned one: `16 · 48,032 = 768,512` ms, the
  deadline its upper end `960,640` ms (`timeout 961`); **early stop** when request `k`'s line comes
  later than `k · 60,040` ms (`60,040 = 48,032 · 5/4`);
- **launched when no other run holds the cores** (no other `hnn_prediction` process at launch).

**The founded read stopped, and the partitioned read, fixed before its launch** [measured;
agent-inferred]. The founded read launched with no other run on the cores, but another worker's
12-thread runs began beside it; its requests took `47,080, 63,675, 66,496, 67,522, 60,335, 70,629,
75,556, 72,986, 73,359, 64,494` ms, and request 3's line came at `244,774` ms, past its bound
`4 · 60,040 = 240,160` ms. It was stopped at about `663,000` ms after 10 requests (all released),
since the remaining six could not meet the 961 s deadline at that rate. Its releases are lost: the
harness wrote a state's releases only when the state finished, which is the defect this read
repairs. No deadline is raised; the partition and the declared read change:
- **each request is written as it completes** (its release and its section), so a stopped read keeps
  every request it read;
- **four partitions of four requests** (`0..4`, `4..8`, `8..12`, `12..16`), launched one after
  another (each holds the whole 12-thread budget; the host's other 12 threads are held by another
  worker's runs);
- **the unit is re-measured**: the largest founded request before launch, `75,556` ms (under the
  shared host). A partition's projection is `4 · 75,556 = 302,224` ms, its deadline the upper end
  `377,780` ms (`timeout 378`); **early stop inside the harness**: a request above
  `94,445 = ⌈75,556 · 5/4⌉` ms stops its partition, reported incomplete.

## 1. The recorded failures this loop could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md), the
[prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md) and the
[contamination cycles](2026-10-05_THE_CONTAMINATION_CYCLES_EVERY_COPY_PIPELINE_FOLLOWED_A_DEMAND_FOR_OUTPUT_BEFORE_THE_FIELD_COULD_RELEASE.md):
- **3, text as the exception.** Nothing here is text's: the field, the menu, the deposit and the
  release are step 1's, and the only change is the exterior alphabet (`|A| = 257`), which
  `Field::declare` does not read. The byte chart and the cut reader are the boundary codec, in the
  harness. Order-2's `ℤ/4` cells and a pixel's or a sample's codes enter the same mode alike.
- **1 and 17, an authored routine.** No distance, map, turn or class is declared or chosen; no rule
  of text enters. The release reads `FieldMaterial` alone (guard 18).
- **2, recitation.** No context, count or seen passage is read by the release; each release carries
  its copy length against the training passage and against its own request (guard 19), a receipt,
  never a control.
- **6, seen graded as unseen.** The requests are later windows of the choosing role that no run of
  this loop read before the pinned run; the training passage is read only by key location; the
  development window is used for timing only.
- **7, bits read as progress.** No bit count is read; the deliverable is the releases themselves.
- **9, a larger limit.** One development read, then one run under the deadline fixed from it.
- **4 and lesson 3, a located cause carried into a new consumer.** The located causes stand where
  they were recorded: the menu reads a stationary turn, so it needs the passage's relation at a
  distance to be a partial injection; the deposit refuses a port holding two classes (lane B §3).
  This loop names them as its expected blockers and measures where each binds.

## 2. The loop in the objects

- **Holarchy.** Step 1's field: three parametron rings of period `60 = 2²·3·5` joined by two pair
  contacts in a chain `0 — 1 — 2`; ring 0 is the source and the receiving ring. Its ports are the
  residue chart of the exterior chart: a byte `x` enters ring 0 at the port `x mod 60`.
- **Aeon, epoch, cycle.** A window is one span of ring 0's clock within one turn (`n + m = 48 < 60`);
  each station is an epoch, a crossing of the receiving ring's section, and one observation.
- **Keys.** A key is a distance `δ`, a stationary turn `c` of the rotor and the plugboard images,
  read by the turn menu's loop law `S(port(x_t)) = S(port(x_(t−δ))) + c` at every edge. It holds only
  where the menu relation at `δ` is a partial injection: every antecedent port with one
  consequence, every consequence with one antecedent.
- **Receiver and receipt.** The release is the receiving ring's bank's reception at the request
  boundary (`generate_by_bank`); with no closed pair contact it reads the span's law, each
  candidate's storage from its own station. The receipt is one region per station: its top class,
  whether its lock is certified, and the plural stations where none is.

## 3. Measured: key location on the training passage

[measured] `run_log.txt`, `location.curve` (the survivors at every observation: distances and
counts, no byte). Every observation reads the distances `1 … t` of its window, so `δ ≤ 40` is read
at every observation and `δ = 47` only at a window's last station; `δ ∈ [48, 59]` is never read (a
window spans 48 ticks).

**The fibre empties at observation 32** (4 windows, `32 = 2⁵`), against order-2's lock at 16. No
distance ever survives alone with a published map, so nothing locates and nothing is deposited.
The surviving distances, on the field's ports (a distance survives while its menu admits a turn),
by observation:

```text
observation  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 … 31 32
alive       40 37 38 34 29 23 19 14 11  8  7  5  3  3  2  1 …  1  0
```

From observation 16 to 31 the one survivor is `δ = 47`, holding one to three edges (the windows'
last stations), all on paths: its map is never published (plural), and its fourth edge empties it.

Each distance empties by one of two events, read separately:
- **The turn set empties.** At 33 of the 47 distances it empties at the observation at which the
  relation fails (below). At 13 it empties earlier, while the relation is still a partial
  injection, by a fixed point: a port that recurs at the distance (`x → x`) forces `ord(c) = 1`, so
  `c = 0`, and any other edge, a path of one edge, then needs `ord(c) > 1`. At 1 it empties by its
  components' lengths (no `c` whose order fits every cycle and path). The observation at which each
  distance's turns emptied:
  `1:6 2:7 3:5 4:2 5:5 6:6 7:9 8:4 9:2 10:8 11:10 12:8 13:10 14:9 15:2 16:5 17:6 18:7 19:4 20:12
  21:8 22:6 23:7 24:8 25:5 26:4 27:5 28:6 29:4 30:8 31:11 32:9 33:6 34:5 35:2 36:8 37:7 38:6 39:7 40:4
  41:10 42:12 43:13 44:13 45:15 46:16 47:32`.
- **The relation fails** (a port with two consequences or two antecedents at that distance): at
  `δ ≤ 40` between observations 4 and 12 (`δ = 26` at 4, `δ = 20` at 12), at `41 ≤ δ ≤ 47` between
  10 and 32, each after 4 to 12 edges (`run_log.txt`, `δ:observation/edges`).

**The fold is not the cause** [measured]. The same edges read on the bytes themselves (a menu a
distance on 256 ports, the terrain-side reading) fail at exactly the same observation with the same
edge count at every one of the 47 distances: no failure is made by two bytes sharing a port
(`x mod 60`). It is the passage's own relation that leaves no stationary turn at any distance: in
4 windows of text, every distance from 1 to 47 already pairs some byte with two different bytes
(or two bytes with one).

## 4. Measured: the release on the two openings

[measured] Nothing located, so nothing was deposited: no closed pair contact, and the release reads
the span's law (`generate_by_bank`, unchanged). Counts from `copy_lengths.txt` (written by
`triples.py`; integers only), over the 16 pinned requests, 128 stations:

| State | Released / held | Whole | Bytes right of 128 | Plural stations | Constant sections | Adjacent stations equal (of 112) | Copy length against the training passage |
|---|---|---|---|---|---|---|---|
| lossless opening | 0 / 16 | 0 | none released | 128 | — | — | — |
| founded opening | 16 / 0 | 0 | **0** | 0 | 11 | 77 | 0 at 10 releases, 1 at 6 (the longest run 1 byte) |

- **The lossless opening holds every section** at its first refinement: no lock is certified at any
  station, so all eight stations of every request stay plural (as on order-2's final confirmation,
  where the lossless opening also held every section).
- **The founded opening releases every section, and none of it is the text's.** Every request takes
  8 refinements, one lock each; at 12 of 16 the first lock is at station 7 (10) or 6 (2), the
  stations farthest from the request, and at 8 the order is exactly `7, 6, 5, 4, 3, 2, 1, 0`. Each later
  lock continues its locked neighbour: 77 of 112 adjacent station pairs are equal, and 11 of the 16
  sections are one byte repeated, ten of them the same byte at all eight stations. That one byte
  fills 80 of the 128 released stations, whatever the request. 91 of the 128 bytes are printable
  ASCII; 23 distinct bytes on 21 ports appear in all. Against its own request, the copy length is 1
  at one release (the repeated byte also occurs in that request) and 0 at the rest.
- These are lane B's located causes ([§5 wall 1](2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md#5-the-walls-by-their-measurements))
  on text, unrepaired where no contact is closed: the nearest lock decides each later station, and
  one class's own column decides between classes. On order-2's four classes that class was `3`; on
  the byte chart's 257 it is one byte [agent-inferred from the counts: the same byte at 80 of 128
  stations across unrelated requests; its column's resonance on the bank was not read].
- The 16 releases, each with its request's last 40 bytes, its true next 8 bytes and its copy
  lengths, are in the private `.local/text_loop/run/triples.txt` only.

## 5. The blocker, by its measurement

**No distance's stationary turn survives four windows of text.** On the training passage every
distance `δ ∈ [1, 47]` meets a port with two consequences or two antecedents within 4 to 12 edges,
and 13 distances lose every turn earlier still to a recurring byte (a fixed point). The fibre is
empty from observation 32 to the passage's end (1,024), on the bytes exactly as on the ports. The
turn menu's law reads one turn shared by every edge at a distance: a global bijection of the
classes, which order-2 has and text, at no distance, does. So nothing is located, nothing is
deposited, no pair contact closes, and lane C's pair release has nothing to read. Without it the
openings release nothing (lossless: 128 of 128 stations plural) or the prior's own preference
(founded: 0 of 128 bytes right, one byte at 80 of 128 stations).

The cost is also measured. The founded release takes `47,231` to `83,393` ms a request at
`|A| = 257` (8 refinements of up to `8 · 257 = 2,056` candidate readings) on a host shared with
another worker's runs, against `23,527/8` ms a request at `|A| = 5` (lane B's development read).

## 6. Time and memory

Thread budget 12 (`RAYON_NUM_THREADS=12`) on every read. Peak resident sets are the harness's own
reading of the process (`resident`, at its end); a stopped run printed none.

| Run | Projection / deadline | Measured ms | Peak resident bytes |
|---|---|---|---|
| development (1 window, both openings; key location) | — / 600,000 (first read) | 54,319 (location 2; lossless 6,209; founded 48,033) | 134,774,784 |
| pinned run (16 requests, both openings, requests in parallel; build of `1199350c`) | 867,840 / 1,085,000 | lossless state 150,140 (its share 99,328; ratio `150140/99328`); stopped at 189,102 | not read |
| founded read (16 requests in turn; build of `4612f267`) | 768,512 / 960,640 | stopped at about 663,000 after 10 requests; request 3's line at 244,774 against 240,160 | not read |
| founded, requests 0..4 | 302,224 / 377,780 | 273,002 (`66,786; 61,830; 72,126; 72,152`) | 136,912,896 |
| founded, requests 4..8 | 302,224 / 377,780 | 248,200 (`71,550; 71,598; 56,461; 48,504`) | 136,921,088 |
| founded, requests 8..12 | 302,224 / 377,780 | 267,838 (`47,231; 69,883; 83,393; 67,246`) | 135,958,528 |
| founded, requests 12..16 | 302,224 / 377,780 | 223,168 (`63,736; 60,439; 50,139; 48,751`) | 136,310,784 |

The four partitions read in `1,012,208` ms against their projection `1,208,896` (ratio
`1012208/1208896`); every request stayed under the unit bound `94,445` ms (the largest `83,393`).
Another worker's 12-thread runs shared the host through every read after the development read.

## 7. Commits and gates

- The pins and the harness mode before any read (`b815a449`); the development read and the
  projection before the run (`1199350c`); the stopped run and the founded read declared
  (`4612f267`); the stopped founded read and the partitions declared (`b919bb40`); this record's
  measurements with their receipts (`runs.sh`, the logs, `location.curve`, `copy_lengths.txt`:
  counts and distances only; no byte of text is committed).
- Gates: `cargo check --workspace --all-targets` clean at the final harness (one pre-existing
  dead-code warning, `ReceivingPhases::with_rank`). No library code changed, so no library test was
  touched; no Lean changed; no card run.
