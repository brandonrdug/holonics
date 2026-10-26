# The replay stopped at its first window, so it reads the section's own opening read

**Withdrawn, October 26.** The reset clock this record builds or measures is a copy pointer: it
holds the unit that arrived after a chosen class and raises that unit's logit at the output. An
audit made at Brandon's request found it, and commit `0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. The replay the previous record fixed
([record](2026-10-26_THE_SUMMED_COVECTOR_DOES_NOT_READ_THE_PASS_SO_THE_PASS_IS_REPLAYED_SECTION_BY_SECTION.md)
§4) ran on Brandon's PC at `d366e6201` and stopped at its early-stop bound. This record gives the
stopped run, the projection's error, the changed read and its projection, fixed before it runs.
Grades: [measured] for what the runs and tests printed, [agent-inferred] for each reading of them,
[definition] for what the changed read computes. Receipts:
[`…_receipts/`](2026-10-26_THE_REPLAY_STOPPED_AT_ITS_FIRST_WINDOW_SO_IT_READS_THE_SECTIONS_OWN_OPENING_READ_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the next arrival
and the arrival a reset clock holds, read at the output face beside the readout's own face, and the
deposition's step that moves both, section by section. The read touches faces and placement and the
deposition; the helix, the level's pair contacts, cell holonomy, tube and tower thread stay as the
tower has them.

## 1. The stopped run

[measured] The replay from `lapD8/STATE` over the training text, 8 streams, sections of 128 units,
`RAYON_NUM_THREADS=8`, an 8 GiB memory scope, under `timeout 310`, alone on the host but for desktop
applications.

- `TOWER_REPLAY_OPEN requests=4524 placed=4524 openings=4519 unheld=4 name_mass=+906.5
  F=-12641.553 elapsed_ms=43644`: the start's whole read agrees with the summed reading's (4,519
  openings held, 4 unheld, the name's mass 906.5).
- `TOWER_REPLAY_SECTION section=32 deposits=32 halvings=0 read_ms=1284 elapsed_ms=48914`: the first
  32 sections took 5,270 ms, over the fixed bound of 5,100 ms, so the run was stopped by its PID at
  49.0 s (`RUN_RECEIPT exit=-15 wall_s=49.0 peak_rss_kib=499176`). It was not relaunched. Every
  section to that point passed its moment check.

## 2. The projection's error

[measured] The projection put a section at 159.2 ms: the training pass's largest 32-section window
on the PC times the first smoke's ratio of the replay's sections to the pass's, 386/291, measured
on 4 threads over a slice in the container. The PC measured 164.7 ms a section, 40.1 ms of it in the
place read and 124.6 ms in the rest, 1.376 times the pass's largest window against 1.326 projected.
The integration review found a slip besides: the 159.2 ms follows from a window of 120.0 ms, not the
119.7 ms the receipt states (158.8 ms).

[agent-inferred] Two causes. The ratio measured on one host and thread count was carried to another
without a margin. And the stop bound was set at the projection's point value (32 × 159.2 ms), not at
an upper bound, so a run 3.5% slower than projected stopped although its total would have stayed
under the deadline (43.6 s + 1,311 × 164.7 ms + about 44 s ≈ 303 s against 310 s). By the waiting
standard a stopped run is not relaunched with a larger limit; the read changes.

## 3. The changed read

[definition] The place read was a second forward of every section from the same opening states the
section's own forward reads. The replay now sums the section's own opening read
(`PlacedPass` in `tower_bank.rs`): after the opening forward, the host's realization hands out its
kept cells (`HostPass::read_opened`), each with its index, face, held classes and top face, and
each stream's cells are summed by place as before. The sums are of the very cells the section's
reverse reads, and no second forward is taken. The check is the same: before the section the two
families' first moments are copied, and after it `TowerLearner::first_after` moves that copy toward
the groups' sum as the section moves it; the result must equal the moment the section leaves, else
the run refuses. `first_after` now takes the moment the section opened with (`None` for an unopened
learner, which `TowerLearner::opened` reports, and the replay refuses an unopened one).

[measured] Checks:
- `the_opened_read_hands_the_cells_the_copies_reading_reads`: after the host's opening forward over
  two streams, one opening later than rest, each stream's sink receives every cell's index, face,
  held classes and top face exactly as `Tower::read_clocks` reads them from the same opening state;
  refused before an opening read is kept, with one sink for two streams, and on a tower without a
  clock.
- `a_sections_moment_and_deposit_are_read_from_its_covector`, with the prior moment: the moment
  read after the section equals the one read before it, an unopened read is the covector on the
  deposit's grain, and a prior of another extent is refused. The tower's 69 tests pass.
- The smoke on the same slice as the first (61,952 cells, 4 streams, 121 sections, from the same
  two-clock state): every `TOWER_REPLAY` line is the first replay's but for the timings, the state
  reached is `d2aeb993…c34f` again (`expected=match`), and the sections took 37.1 s against the first
  replay's 46.7 s (0.795), 306.4 ms a section, the place read 2.4 s of it against 11.8 s.

## 4. The run, fixed before it runs

The replay from `lapD8/STATE` over the training text, 8 streams, sections of 128 units, expecting
`lap3T8/STATE` (`33317844…f6be`), on the PC at the commit that adds this record. The decision is the
previous record's §4, unchanged.

- [agent-inferred] The changed read does all of the stopped read's work in a section but one
  forward of the eight streams, and adds a copy of the two families' first moments, so the stopped
  run's 164.7 ms a section bounds it from above. The expected section is 164.7 × 0.795 = 130.9 ms.
- Projection, upper end: 1,311 sections × 164.7 ms = 215.9 s, the load, hash and first whole read as
  measured, 43.6 s, and the end's whole read with the state's text and hash at most the same 43.6 s
  (on the slice the end took 0.99 of the start): 303.2 s. Deadline 304 s, below the first run's 310 s.
  Expected about 259 s.
- A 32-section window past 5,270 ms (32 × 164.7 ms) stops the run: past it the changed read would be
  slower than the stopped read with one forward more. Memory: the stopped run peaked at 487 MiB; the
  ceiling stays 8 GiB.

`lapD8/STATE` stays the state the role and John are read from, and no lap is taken until the read
decides.

## 5. The recorded failures this loop could repeat

- **A refusal answered with a larger limit.** The stopped run is not relaunched. The read changes
  (one forward fewer a section), and its bound is the measured time of the stopped read's larger
  work, with a deadline below the first one.
- **A located cause carried unrepaired into a new consumer.** The projection's two causes are
  repaired where they lie: the bound is an upper bound measured on the PC, not a ratio carried from
  another host.
- **An authored routine standing in for learning.** Nothing enters the machine; the replay reads the
  pass beside it, from the pass's own cells.
- **Seen material graded as unseen.** The read is on the training text; nothing here counts toward
  the held-out acceptance.
