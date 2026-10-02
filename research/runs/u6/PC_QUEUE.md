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
