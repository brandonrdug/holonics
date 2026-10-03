# U6 heavy runs for the PC (24 cores, 32,746,147,840 bytes, RTX 4080 SUPER)

Owner of what is measured: the main-line thread (in the cloud since October 2). The PC session runs
these in order and reports each receipt exactly as the harness prints it (rationals, `/4096` cells,
enclosures; never a decimal), with wall time and peak resident set. Small reads (smoke tests, single
`direction`, `locks`, `instants` reads) stay in the cloud.

**Setup.** Check out this branch, `cargo build --release -p holonics --example hnn_prediction`
(`$B` = `target/release/examples/hnn_prediction`); `$S` = `research/runs/u6/states`. Launch every run
in the background with an outer `timeout` from its projection; never raise a limit. Stored states
the cloud runners produce arrive on their branches; the main line names them here when they land.

## Before any launch

A run launches only when its entry here states each of these, and the main line has checked them
(October 3, after the audit of P4; the refits record §12):
1. **The decision it can change**, written as "result A leads to X, result B leads to Y", with the
   latest time at which X or Y still matters. Nothing that the result would decide starts before it
   reads. When that time passes, or the decision is taken anyway, the run is stopped.
2. **A projection on the launch host**: a development read there of early and late units, the
   largest time per unit, and a deadline of three times the declared count times that largest time.
   A projection is never carried to another host, and a deadline never exceeds the host's own
   lifetime (a cloud session's background runs end at 2 h).
3. **A progress line and an early measured part.** The run prints one line per unit with its
   elapsed ms, and the part it measures is reached early (reorder or declare the cut so that it is),
   so that it can stop early on evidence.
4. **What a null means.** A check that the instrument does not change the quantity under test, and
   which outcomes can be read.
5. **No existing receipt.** A search of every branch's receipts for the same input-state sha256 and
   command, and of existing sections that already answer the question.
6. **Receipts on every exit.** The run commits and pushes its own receipts on completion, timeout or
   error (launch UTC, build, host, threads, projection, deadline, wall time, peak resident set), so
   no result waits on a session.

## Where the GPU applies (exact arithmetic only)

The card's realization (`crates/holonics-cuda`) is the exposure protocol's execution port: moment
ingest, the lattice read, chart refinement, the word's forward and reverse passage with its
receiving read, deposits and the landmark tree, all in exact integers (`ℤ/2^128` ring words under
the l1 certificate), each with a host-parity test. So:
- **Campaign 1 and the GPU suite** run on the card exactly (`hnn_exposure` over `Resident`). Gate 3
  for any PR that changes HNN behaviour: `flock .local/gpu.lock cargo test -p holonics-cuda --
  --include-ignored --test-threads=1`, alone on the card.
- **Today's U6 reads have no card path**: the executed comparison, the bank release, the kinetic
  and joined moves, `evaluate`, `word-read`, `spectrum` and `run` are host code over `rayon`
  (`hnn::executed`, `hnn::prediction`). They run on the PC's 24 cores.
- **What could take the card without leaving exact arithmetic**: a word's forward passage and
  receiving read (`hnn_word_forward`) and the per-request observability rank (one word per source
  coordinate, the same kernel). The bank release, the lock order and the move's solve are rational
  host laws with no card owner; porting them is not exact-integer work yet and is not queued.

## P1. Withdrawn

§6's contact-path read reads a receiving map that is zero at every U6 state (the record's §7). Its
replacement, the work of each move's deposit and the changed passage, is a single-request read and
runs in the cloud.

## P2. Held-out reads of the cloud chains' final states (16 threads, one at a time)

As each cloud chain reports its final state (Q2's metric chain, Q2's kinetic control, Q4's joined
chain from w3, Q5's run from r13), fetch the runner's branch and read it out:
```
RAYON_NUM_THREADS=16 timeout 1700 $B executed evaluate order2 2026093012 128 out/p2-<label> <label>=<final state>
```
Measured here before: 566219 ms for w16 at 16 threads; deadline three times that. Report whole
sections and stations right by station.

## P3. Where the decisions change along m6's and m7's directions (#211 §7; moved from cloud Q8)

If the first cloud runner has not started Q8, run it here, the two reads together at 12 threads each:
```
RAYON_NUM_THREADS=12 timeout 7200 $B executed spectrum order2 2026093061 8 m6=$S/m6.state lock-dec kinetic 1/2048 1/1024 16 64
RAYON_NUM_THREADS=12 timeout 7200 $B executed spectrum order2 2026093061 8 m7=$S/m7.state lock-dec kinetic 0 1/2048 16 64
```
Report the header (the lattice unit), each read's cut index, and every wall (its two cut indices,
its jump `J`, the requests it changes).

## P4. The exposure protocol's held-out code at m6 and w16 (record §7's restated gate)

**Incomplete** (October 3, `claude/pc-receipts` `697a89ed`; the refits record §12). Both sources exited
124 at `36000053` ms with only the header written, so the gate is not read. It is not relaunched, and
the record states the decisive form (a progress line, and the held-out passages first under a 2048-window deadline). The
queue then held nothing else; P6 below is planned, not launched. The text below is the plan as launched.

**Running in two places.** The cloud launched it on October 2 at 21:28 UTC, at 2 threads per
source. A container restart at about 23:00 lost that run: only the header line had been written, since
the run prints no per-window progress. The cloud relaunched it at 23:07 under the same deadline. The
deadline is not raised, because the restart stopped the run, not its deadline. The PC also runs it,
from `1e32c868`, under this fallback, because a further restart would lose the cloud copy again.
Whichever copy finishes first is the receipt. The command, both sources together at 2 threads each:
```
RAYON_NUM_THREADS=2 timeout 36000 $B executed expose 2026093061 2026093012 128 all m6=$S/m6.state
RAYON_NUM_THREADS=2 timeout 36000 $B executed expose 2026093061 2026093012 128 all w16=$S/w16.state
```
Projection, from the 200-window smoke at m6 in the cloud:
- 294297 ms for 200 windows, with user time 425 s over a real time of 294 s;
- peak resident set 665231360 bytes per source;
- the full cut is 21845 windows (`2^16` cells, three per window), so 32144589 ms per source,
  and the deadline is 36000 s.

The run prints no per-window progress line, so it cannot stop early on evidence; the deadline
is fixed and is not raised.

Gate: w16's held-out combined code below m6's by at least `1024·1/16 = 64` bits. Report the held-out and
training lines whole.

## P5. The joint held-out read of the arms' end states, paired by move count

**Done** (October 3, `claude/pc-receipts` `5fb7e96b`; the refits record §11). No declared pair is
released: whole-move m2 against at-rest m2 has `b = 172`, `c = 191`; the strict-descent control
against at-rest m6 ties at `b = c = 92`. The text below is the plan as launched.

Each chain stores every move's state. When a chain ends, at m16 or earlier, the main line names its
end state here. A chain ends in one of three ways: at m16; under its own law, where every trial is
refused; or incomplete, past a per-kind bound. The PC reads the end states in one call at 16 threads.
The arms are:
- Q2's Coordinate chain and Q2's Kinetic control, both under #202's interval acceptance;
- the at-rest throw: the throw chain through m5 (every move released from rest), then its own chain
  from `m5-throw.state`, releasing from rest at every move (ρ held). **It ended under its law at m8**
  (`claude/pc-receipts`, `research/runs/throw-rest/m8/m8-throw.state`): at m9, strict descent refused
  every trial from η 8 down to 1/16;
- the coast-alone throw: the original throw chain, which first carried its coast at m6 (#240's rule
  before `5f254c2d`);
- the whole-move throw (#240's whole-move power test, `−⟨∇L, ηD + c⟩` along `w = D + c/η₀`);
- the strict-descent Coordinate control, the same driver with `coordinate`, as the baseline. It
  matches the throw through m1 and leaves it at m2, where Coordinate moves ρ. It ended incomplete
  at m7 under its first, fitted bound, and runs again from m6 under per-kind bounds.

The last four use strict descent. Each throw is read against the at-rest throw, which has the same
driver, the same acceptance and ρ held; only the carried momentum differs.

**The end states named so far** (the main line, October 3):
- `coord`: Q2's Coordinate chain ended at its held state q213, `q213-coordinate.state` on
  `claude/cloud-runs-pfo084` at `5f54e54`, archived at
  `research/runs/branch-archive/claude/cloud-runs-pfo084/research/runs/u6/cloud/q2/q213-coordinate.state` (sha256 `038f227d32924018c2685c345054e32a91e66afad703b41187b66b9241f944b8`);
- `kin`: Q2's Kinetic control ended at q2k14, `research/runs/u6/runner2/q2k/q2k14/q2k14-kinetic.state`
  on `claude/cloud-runs-2-5aw27d` at `1733578`, archived at
  `research/runs/branch-archive/claude/cloud-runs-2-5aw27d/research/runs/u6/runner2/q2k/q2k14/q2k14-kinetic.state` (sha256 `963d122685ee16449ac1cc4fb3f0623c91b9a6ba2ab5770919c79de7d20790d9`);
- `rest`: `research/runs/throw-rest/m8/m8-throw.state` on `claude/pc-receipts`, archived at
  `research/runs/branch-archive/claude/pc-receipts/research/runs/throw-rest/m8/m8-throw.state`;
- `tctl`: the strict-descent Coordinate control is not relaunched. It is read at m6,
  `research/runs/throw-control/m6/m6-coordinate.state` on `claude/throw-control-chain-847j2f` at
  `774079e` (archived at
  `research/runs/branch-archive/claude/throw-control-chain-847j2f/research/runs/throw-control/m6/m6-coordinate.state`), beside `rest6` = `research/runs/throw-rest/m6/m6-throw.state` on `claude/pc-receipts` (archived at
  `research/runs/branch-archive/claude/pc-receipts/research/runs/throw-rest/m6/m6-throw.state`);
- `coast` and `whole`: still running. Coast-alone m8 against at-rest m8 is already read (record §10).

**Like for like by move count.** A pair compares two states at the same move count:
- the coast-alone and whole-move throws at m8, against the at-rest m8;
- the strict-descent Coordinate control at its end, against the throw arms at the same move.

When an arm ends short of another, the call adds the other arm's state at that move as an extra
label. Each arm's own end state is read as well, but it is paired only at equal move counts.

Pairs follow the paired rule: per held-out request, `d` = stations right in A minus in B; `b` counts
`d > 0`, `c` counts `d < 0`, ties dropped; the exact one-sided sign tail on `b` of `b + c` at `1/2`,
released only at a tail of at most `1/64` (`paired.py`'s default; a request's eight stations are not
independent; corrected October 3).
The labels below are the six end states. Pairing labels added for equal move counts extend the call
and its deadline (three times the largest per-state read, per state).
```
RAYON_NUM_THREADS=16 timeout 19493 $B executed evaluate order2 2026093012 128 out/p5-ends.sections coord=<q213> kin=<q2k14> rest=<m8> coast=<end> whole=<end> tctl=<m6> rest6=<m6> [whole8=<m8> ...]
```
Pass a file path for the sections, not a directory. `evaluate` writes it with `std::fs::write`, which
creates no parent directory, so `out/` must exist before launch.

The deadline is three times the largest held-out read per state measured before launch, for six
states. The reads at 16 threads, each on a machine shared with other runs, are:
- w16, `566219` ms (`heldout_end.txt` in the refits record's receipts);
- q411, `712634` ms (`claude/pc-receipts` `141895d6`, `paired/q411_eval.txt`);
- m13-4 (r13close), `1082906` ms (the same commit, `paired/m13-4_eval.txt`).

The largest is `1082906` ms, so the deadline is `18·1082906 = 19492308` ms. It is fixed here before
launch and never raised. Report whole sections and stations right, station by station, for each state.

## P6. The reception carry against rest, on the fresh seed 2026100301

**Planned, not launched** (October 3; record B §6,
`research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md`).
The production path now carries a reception's end into the next reception
(`Reference::with_reception(Reception::Carry(Absorption::Nothing))`, `Word::open_received`). This
run reads whether the carry predicts held-out stations better than today's rest. The six checks:

1. **The decision.** If the carry is ahead (paired by passage, tail at most `1/64`), production
   receptions carry, and the owed work follows: the carried change in `ContinuingState`, the device
   word, and the chained-balance certificate with its Lean (#62). If it is not ahead, receptions
   stay at rest and the carry stays a declared, unadopted opening. Nothing that depends on the answer
   starts first: no exposure or U6 chain is launched under either opening before this reads. If one
   is launched anyway, this run is stopped.
2. **The projection, on the PC.** Before launch, a development read on the PC on the spent seed
   (never on 2026100301), at the declared windows and two passages:
   ```
   RAYON_NUM_THREADS=16 timeout 7200 $B executed held-read 2026093061 2048 2026093012 2 out/p6-dev.listing m7-3=<m7-3 state>
   ```
   Take the largest formation time `F` (the last formation line) and the largest passage time `P`
   (the passage lines). The deadline is `3·(F + ⌈128/16⌉·P)` ms when passages run sixteen at a
   time, written here before launch and never raised.
3. **Progress lines.** Formation prints one line per compared window with its elapsed ms; the read
   prints one line per passage, written to the listing as each passage ends. Formation is the
   longest part and is measured whole by the development read; if the first passages of the
   decisive read run slower than `P`, the run stops and is reported incomplete.
4. **What a null means.** At complete absorption the carry equals rest exactly (tested:
   `the_carry_at_complete_absorption_is_todays_reception_exactly`,
   `each_held_out_passage_is_read_from_the_stored_state`). A state whose receiving map is zero ties
   every passage by construction, which is why the stored state is formed in the same process by
   the exposure protocol at rest (`Reference::expose_forming`): the formed map cannot be saved,
   because `ContinuingState` holds only the source port. **Launch only if the development read shows
   at least one passage whose rest and carry codes differ.** If every development passage ties, the
   instrument cannot separate, and the run is not launched. Every held-out passage reads from the one
   formed state, with nothing deposited (`Reference::read_passage` discards each staged deposit), and
   the carry restarts from that state at every passage.
5. **No existing receipt.** Seed 2026100301 has never been read (record B §4), and no `held-read`
   receipt exists on main or on `claude/pc-receipts`. Check both again before launch
   (`git grep -n 2026100301 origin/main origin/claude/pc-receipts`).
6. **Receipts on every exit.** Launch through a wrapper whose `trap … EXIT` copies the listing,
   stdout, `/usr/bin/time -v` output (wall time, peak resident set), exit code, launch UTC, build
   commit, host and threads into `research/runs/p6/` on `claude/pc-receipts`, and commits and pushes
   them, whether the run completes, times out or fails.

The decisive command, after the development read sets the deadline `T`:
```
RAYON_NUM_THREADS=16 timeout T $B executed held-read 2026093061 2048 2026100301 128 out/p6-carry.listing m7-3=<m7-3 state>
```
The opening state is m7-3, the state #236 released:
`research/runs/branch-archive/claude/pc-receipts/research/runs/u6/receipts_pc/q3/m7-3.state` on main.
Formation runs 2048 windows (6144 cells) of training seed 2026093061 at rest. Report the formation
line, every passage line, and the final paired line (ahead, behind, tied, the exact tail and its
`/2^20` cell, released or not) whole. Stations right are description only.
