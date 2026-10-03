# U6 heavy runs for the PC (24 cores, 32,746,147,840 bytes, RTX 4080 SUPER)

Owner of what is measured: the main-line thread (in the cloud since October 2). The PC session runs
these in order and reports each receipt exactly as the harness prints it (rationals, `/4096` cells,
enclosures; never a decimal), with wall time and peak resident set. Small reads (smoke tests, single
`direction`, `locks`, `instants` reads) stay in the cloud.

**Setup.** Check out this branch, `cargo build --release -p holonics --example hnn_prediction`
(`$B` = `target/release/examples/hnn_prediction`); `$S` = `research/runs/u6/states`. Launch every run
in the background with an outer `timeout` from its projection; never raise a limit. Stored states
the cloud runners produce arrive on their branches; the main line names them here when they land.

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
the record states the decisive form (a progress line and a shorter declared training prefix). The
queue is empty. The text below is the plan as launched.

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
  `claude/cloud-runs-pfo084` at `5f54e54` (sha256 `038f227d32924018c2685c345054e32a91e66afad703b41187b66b9241f944b8`);
- `kin`: Q2's Kinetic control ended at q2k14, `research/runs/u6/runner2/q2k/q2k14/q2k14-kinetic.state`
  on `claude/cloud-runs-2-5aw27d` at `1733578` (sha256 `963d122685ee16449ac1cc4fb3f0623c91b9a6ba2ab5770919c79de7d20790d9`);
- `rest`: `research/runs/throw-rest/m8/m8-throw.state` on `claude/pc-receipts`;
- `tctl`: the strict-descent Coordinate control is not relaunched. It is read at m6,
  `research/runs/throw-control/m6/m6-coordinate.state` on `claude/throw-control-chain-847j2f` at
  `774079e`, beside `rest6` = `research/runs/throw-rest/m6/m6-throw.state` on `claude/pc-receipts`;
- `coast` and `whole`: still running. Coast-alone m8 against at-rest m8 is already read (record §10).

**Like for like by move count.** A pair compares two states at the same move count:
- the coast-alone and whole-move throws at m8, against the at-rest m8;
- the strict-descent Coordinate control at its end, against the throw arms at the same move.

When an arm ends short of another, the call adds the other arm's state at that move as an extra
label. Each arm's own end state is read as well, but it is paired only at equal move counts.

Pairs follow the paired rule: per held-out station, `b` (right in A only), `c` (right in B only), and
the exact one-sided sign tail on `b` of `b + c` at `1/2`, released only at a tail of at most `1/64`.
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
