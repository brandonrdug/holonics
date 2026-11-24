# A lap's card time was its reads: the held read ran one forward four times, a one-sided region continues by a site, and a read is sized by the scatter between laps

November 24, 2026, 17:36 to 18:40 UTC, the formal thread, in a cloud container with the PC's run logs read through a link (reads only).
Refs #404, #603, #410. Receipts: [`receipts/2026-11-24_lap_cycle/`](receipts/2026-11-24_lap_cycle/). It reads the line as
[the lead's record of this day](2026-11-24_HER_LINE_TAKES_THE_FULL_CURATED_COLLECTION_AT_SEVENTY_TWO_PERCENT_OF_A_PASS_THE_LOGS_CROWD_OUT_THE_REGISTERS_AND_HER_ACTS_AND_THE_LEVELS_LANE_COST_UNDER_FOUR_THOUSANDTHS_AND_MOVE_NOTHING_YET.md)
left it, and the lap after it (W108, with its arm W108d).

## 1. The occasion

Brandon, 17:36 UTC, read in his own message: the work of the last days went deep into engineering and trial, so the context and the
organization are to be tended and consolidated where that helps; and, the weightier of the two for the pace of iteration, the runs
have each taken hours, which is a fair investment for this subject, and no time is to be spent that does not have to be, with every
improvement grounded in the theory. The second is §2 to §6. The first is §7.

## 2. A lap's cycle, measured

`tools/lap_cycle.py` (new with this record) reads each command's own closing line. On W108, a lap of 3,000 sections on the wide
store with the theory and the Lean six times over ([`lap_cycle_W108.txt`](receipts/2026-11-24_lap_cycle/lap_cycle_W108.txt)):

| step | the card's time | |
|---|---|---|
| the lap (`train-store`, 3,000 sections) | 2,061 s | 34.3 min |
| held read, the older held set's five registers (`read-cavity`) | 665 s | |
| held read, store-2026-11-22's seven registers | 948 s | |
| held read, the collection's ten registers | 1,294 s | |
| loudness, the older held set's five registers (`read-loudness`) | 331 s | |
| five panels written on the card (`write-next`; the wide panel's 160 rows of 96 places 60 s) | 105 s | |
| every read and write | 3,342 s | 55.7 min |
| the cycle | 5,403 s | 90.1 min |

Training held 0.381 of the card's time and the reads 1.62 times the training. Two panels and the reach's read ran on the host beside
them (493 s; two more host panels keep no log) and held no card. The times are the commands' own counters; a command's wait for the card's lock is not in them. By the
run's stamps the control and its arm together took 4 h 02 (13:56:14 to 17:57:31 UTC): two joins of the state to the stores 11
minutes, the two laps 69, and the reads of the two laps 161, queued one behind the other on the card.

Inside the collection's held read, by rows, summed over its ten slices: rows P (each held place alone open, one region a place)
791 s; rows F (the frontier under the plain law) 283 s; rows K (the same prefixes as a known stream) 121 s; the code slice's copies on
the host, inside the read's hold of the card, 39 s; rows W (whole masks) 8 s; rows S (the passage by two streams, the comparison she
trains and writes by) 1.8 s. A slice of 20,000 places is about 100 stretches of about 190 places. Rows P stage a region a place, `s²`
sites a stretch of `s` places, where rows S stage one region of `2s` sites: about 94 times the sites. A site costs about 20 µs in
rows P, 15 in F, 6 in K and 4.5 in S (a training section 13 with its return and deposit); the plain law's regions hear both sides
and rows P keep every tick's chart (`agent-inferred` from the regions' notes; a profile of one batch of each kind would place it).
The two together are the measured ratio of 440.

## 3. One forward ran four times

The three held reads read one state on nested held sets. The older held set's five slices are the first five of
store-2026-11-22's seven, which are the first seven of the collection's ten: each log prints the same stretches and places for a
shared slice (code: 107 stretches, 20,124 places, in all three), and on W104f, W105w and W106t the seven shared registers read the
same to every printed digit in the two tables the lead's receipts hold
([`frontier_collection_W106t.txt`](receipts/2026-11-24_collection/frontier_collection_W106t.txt) beside
[`arm_W106t.txt`](receipts/2026-11-24_collection/arm_W106t.txt)). The loudness read runs rows P and W once more for the face lanes' powers
(62 to 69 s a slice against the held read's 72 to 84 s for the same rows).

On the objects: a receipt is a field of readings over a partition, each region in its own frame, and it belongs to the pair (state,
partition). A second command on the same state and the same partition returns the same receipt, and a reading on a part of a
partition is the whole's reading restricted. So one forward of the widest held set serves every reader of that state: the two
narrower reads are rows of the third filtered by register (1,613 s a lap), and the loudness is the same forward with its powers
gathered (331 s a lap; `Resident::run` gathers a tick's charts and its face lanes' scales under separate cells, so one run with both set
returns both, `crates/engine-cuda/src/hnn/resident.rs`). The hardware law names the pattern: shared immutable input, disjoint
staged output. That is 1,944 s of a lap's 3,342 s of reads, 32 minutes, that computed nothing a row already on disk did not hold.

**What the lead did with it** (the split was sent through the coordinator that hour; the lead's guess G-P1, fixed 17:58:33 UTC,
is the lead's and will stand in the lead's receipts). The next lap, W109, reads the collection's held set alone with a new last word
`open` that leaves rows F, K, S and the copies unread, and drops the two narrower reads: its reads are projected at 26 minutes of
card against 56. Read on the PC at 18:18 UTC: on W108's mean the `open` read took 890 s, 14.8 minutes, and its rows P and W
hash equal to the full read's (the lead's receipt to keep). Rows F and K stay a milestone's read, and they are lawful whenever a guess is scored on them.

**What stands after that trim**, in the order of its size: rows P, 13.2 minutes of the remaining 21 (§5); the loudness read, 5.5
minutes, which the forward of rows P already holds and which would then cover the collection's registers too (rule 7's reading does
not reach the theory, the logic, the conversations, the acts or the harness today); and rows S, which `open` leaves unread and
which cost 2 s a lap for the held code of the law she writes by.

## 4. Training stands where its count put it

`tools/engine_count.py` on the lap's log ([`engine_count_W108.txt`](receipts/2026-11-24_lap_cycle/engine_count_W108.txt), without
the pump's chart): a section is 684 ms against a floor of 223 ms at today's declaration (133 ms of narrow products, 90 ms of octets
read in order), 3.1 times over. On November 21 a section stood at 473 ms over a floor of 157, 3.0 times. The section grew by 1.45 and
the floor by 1.42: the growth is the declaration's (the collection's regions: 52,558 sites and 2.3·10⁷ pair terms a section, seven
face lanes), and no part of the realization slipped. The site maps are 124 + 50 of the floor's 223 ms, so the family that binds a
section is the one the count already named; a profile by family (the lead's, started this day) says where the 3.1 stands. A
realization three times over its count is not left to stand (a line's lap, rule 3), and it is one third of a cycle: the reads were
the larger part and cost nothing to take.

## 5. A read is sized by the scatter between laps

The held read takes 20,000 places a slice, a number handed in at the command. Its law is a relation between two grains (the
precision law's clause of November 21): the read's own error, and the scatter of what it is asked to resolve. A lap's difference
from its control is read paired by place. Over the collection's 200,933 places the paired error is ±0.0009 nats a place, and the
scatter between two laps of one state was 0.0012 to 0.0014 on November 18: over all places the read stands just under what it has
to resolve, which is where the relation puts it. By register (about 20,000 places) the paired error is about ±0.003: a register's
difference under that is not resolved by one lap's read, and the tables print four digits of it. So the relation licenses no smaller
count over all, and it says which digits of a register's line are readings.

What it does license is a cheaper form of rows P, because the quantity read is a paired difference and pairing removes what two
states share. Rows P open one place a region: about 190 forwards of a stretch for one forward's worth of places. Opening every
32nd place of a stretch in one region covers the stretch in 32 regions, about six times fewer sites, and each open place then
stands among known places out to 31 on each side, well past the three places before it that her frontier binds (the record of
November 18 on the two streams, §15). The level itself shifts by what the far open places withhold (at the frontier her code still
falls with every octave of known places out to hundreds); the difference of two states read the same way should keep. It is a guess (G-C2 below) and one slice read both ways on
two saved means tests it. A line's series changes its read only across a bridge: both forms on the same state once, as rule 2
asks of a reading a line is scored by.

## 6. A one-sided region continues by a site

**The read.** `write-next` (`crates/athena/src/ruler/tension.rs`) writes a place by rebuilding each row's whole region (the prompt,
what is written, one open place) and running the whole forward to read one face. A region of `n` places read by two streams is `2n`
sites, so each place written costs about `(2n)²` pairs: the wide panel's 160 rows of 96 places counted 2.5·10¹⁰ pairs in 60 s.

**The law.** In a region read one-sided a site hears only what stands before it (atlas `tower.region-known-stream`,
`tower.region-strand`), and the level's hand-on keeps that: a place takes the epoch that ended before its own began
(`tower.level-before`). A site's state is then a function of the symbols up to its own place. Ticks of that kind compose, so after
any count of ticks the states of the sites that stand are the same whatever is appended: they are a retention sufficient for every
continuation, the retention law read along a passage's own order. A place written is one known site and one open place joining the
sites that stand: about `2n` pairs a tick with each tick's states kept, where the replay pays `(2n)²`.
[`HNN/ContinuedRegion`](../../lean/HolonicsResearch/HNN/ContinuedRegion.lean) proves it for any tick of that kind
(`OneSided.iterate`, `kept_states_stand`, `face_stands`) with the count: a site joining `m` adds `2m + 1` pairs, and
`m² + Σ_(k<R) (2(m + k) + 1) = (m + R)²` (`continued_pairs`), so **a whole reply costs one forward of the finished region**, where
the replay costs at least `R` forwards of the prompt (`replayed_pairs_ge`). A 400-place reply after 1,000 places is about
2.3·10⁹ pairs replayed and 4·10⁶ continued. The same bits follow where every part of the built tick is one-sided in the theorem's
sense, which its atlas rows state and a run reads (G-C1).

**What it is for.** A lap's panels are 1.7 minutes of its card, so this is no lap's saving. It is the cost of what the line is
asked for next: an exchange with her, whose reply follows a context that grows, and panels of many draws a prompt (the probe
panel's 200 rows of 64 places take 368 s on ten host threads). Under replay a context of a few thousand places makes each place
written a whole section's forward. The engine holds no command that continues a region: the row in
[THE_ENGINE §11](../../docs/THE_ENGINE.md#11-the-theorys-laws-against-the-engine) says so.

**A guide's sentence this corrects.** `Region::strand`'s note said that the level is not heard in a passage read by two streams and
that its faces are a known stream's open last place bit for bit. Both held until the level's block of the epoch before was built,
later the same day (November 18), and taken into the line: on W103 the lead's table reads the two 0.1309 nats a place apart
([`frontier_collection_W106t.txt`](receipts/2026-11-24_collection/frontier_collection_W106t.txt)), the level's hand-on with the
open place's bare clock (0.004 to 0.013 of it by the atlas row). The note and the atlas row `tower.region-strand` now say where
each holds.

## 7. What was tended in the tree

- **The position.** [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) stood at November 20, 23:05 UTC, four days behind the line. It now opens on November 24, written from the records of November 21 to 24; the position of
  November 20 is cited at its commit, as that file does with every earlier text.
- **The route.** [The records' README](README.md) routed two of the twenty records of November 21 to 24. The other eighteen are
  routed, each on the subject it changes.
- **A wrong figure in the guide.** CLAUDE.md gave the exponential's resident face as 4 GiB on the store line. It is `8 · 2^digits`
  octets at `digits = FACE_BITS = 16`, 512 KiB. The refusal of November 16 that the clause cites was the process's batch budget
  under the board ceiling of that day. The clause keeps its bar and its reason with the figure read at its owner.
- **The cycle's ruler.** `tools/lap_cycle.py` with its controls in gate 1, so a lap's report can carry where its card time went.
- **Guess names.** Guesses are filed by the receipts directory of their record, and a name is unique only with it: the lead's
  `GUESS_H2` to `GUESS_H5` (the history's laps, `receipts/2026-11-24_collection/`) and the formal thread's G-H1 to G-H14 (the handed
  cycle, `receipts/2026-11-23_handed_cycle/GUESS.txt`) share a letter. The position lists the guesses that stand unread with their
  files. No file was renamed: a record cites each by its path.
- **Not done, and why.** CLAUDE.md is 121 KB, 15 KB over its size after the trim of November 18, grown by six clauses that carry
  their occasions in line. Moving those occasions to their records is a pass of its own: the trim of November 18 dropped clauses
  that a review had to restore, so it is done against a list of every bar, reason and scope, and not beside other work.

## 8. The guesses

Fixed 2026-11-24T18:08:02Z (`date -u`), before any read for them, in [`GUESS.txt`](receipts/2026-11-24_lap_cycle/GUESS.txt).
Whether a build or a read runs is the lead's. A miss is scored as a miss in one line.

- **G-C1**, 0.85: a forward that continues a region read by two streams by one site, keeping each tick's states of the sites that
  stand, gives the open place's face the same bits as `write-next`'s replay at every place of the long panel on the line's state.
- **G-C2**: rows P read with 32 regions a stretch against rows P as built, one slice, the saved means of W108 and W108d.
  (a) 0.7: the paired difference of the two states agrees between the two forms within 0.003 nats a place. (b) 0.6: one state's
  level differs between the forms by under 0.01.
- **G-C3**, 0.9: one run with the charts' and the scales' cells both set returns loudness tables equal byte for byte to
  `read-loudness`'s on the same slices.

## 9. The failures this could repeat

- **Speed run as a pendulum** (November 16: nine hours of kernel holds for 0.1 to 1.4% a section while the writes went unread).
  What differs: nothing here is a kernel. The reads were multiples of a cycle, read from counters every lap already prints, and
  taking them changed no bit of the line. §4 names the one realization that stands over its count and leaves it to its profile.
- **A reading a line is scored by, changed without a bridge** (rule 2 of a line's lap; November 11). The lead's `open` read prints
  rows P and W by the same forward. G-C2's form would change the read, so it is asked for as both forms on one state first.
- **A workload cut to fit a clock** (GPU first). No lap, pass or held place is cut. §5 reads the count of places against its own
  law and finds it stands.
- **A design thought in the programming language** (the lessons' list). §6 could be told as a cache of activations. It is stated
  as the retention law: the states kept are sufficient for every continuation, they are what the forward itself computed, and
  reading them costs the pairs a site adds. A table of faces indexed by a context met before would be the cache the guide refuses.
- **A null from an unproved instrument** (rule 11). The ruler's controls plant a training log, a held read with its rows, a host
  log and an open log, and each is read as planted.
