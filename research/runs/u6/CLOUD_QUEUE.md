# U6 measurement queue for the cloud runner

Owner of what is measured: the main-line thread. The runner executes in this order and sends each
receipt back (the listing, the wall time, the peak resident set). Report every value exactly as the
harness prints it (rationals, `/4096` cells, enclosures); never a decimal.

**Common setup.** Repository root of this branch. Build once:
`cargo build --release -p holonics --example hnn_prediction` (binary
`target/release/examples/hnn_prediction`, written `$B` below). Terrain `order2`, development seed
`2026093061`, 8 requests, arm `lock-dec`; held out: `order2`, seed `2026093012`, 128 requests. The
founded opening is `research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state` (`$C0`);
the stored states are in `research/runs/u6/states/` (`$S`). This branch's lock rule is main's after
#207 (unranked stations lock together); the earlier chains used the old rule, which differs along
them only at w9 (one freezing order, no change in the released comparison at the grain).

**Times measured on the 24-core PC** (19 threads unless noted): a kinetic move with one trial
158 to 206 s, with 8 trials up to 460 s; a held-out read of 128 requests 566 s at 16 threads; one
`direction`, `step-state` or `locks` read 110 to 600 s at 4 threads under load. On 4 cores set every
deadline at three times these: a chain move `DEADLINE_S=1900` (`UNIT_MS=1900000`), a held-out read
`timeout 5400`, a single read `timeout 1800`. A run past its deadline is reported incomplete with how
far it got; it is not relaunched with a larger limit.

## Q1. The native metrics' first steps at the founded opening

Each metric's step from `$C0`, written one small step out, then paired with the native gradient `G`
(the plain pullback, the reference) and with the normal-law step `ΔE`:
```
$B executed step-state order2 2026093061 8 out/q1 cco=$C0 lock-dec coordinate 1/1024
$B executed step-state order2 2026093061 8 out/q1 cwi=$C0 lock-dec witness 1/1024
for t in out/q1/cco-1024.state out/q1/cwi-1024.state $S/k1_from_opening.state; do
  $B executed direction order2 2026093061 8 lock-dec $C0 $t out/q1/dir-$(basename $t .state) 1/1048576
done
```
`k1_from_opening.state` is the kinetic metric's first accepted move from the opening (η = 1/32); at
the opening the joined metric holds ρ at its bound, so its step is the kinetic one. Report, per
target, the two lines `ΔE (through the chart)` and `G (the plain pullback)`: the pairing's sign and
squared cosine. Already read on the PC (signed cos², `/4096`): `G` with the kinetic step `+[37, 38)`,
`ΔE` with it `+[35, 36)`; `G` with the float descent `+[1693, 1694)`.

## Q2. The 16-move chain under the metric whose step lies closest to `G`

Take the metric of Q1 with the largest positive squared cosine with `G` (`coordinate` or `witness`;
the kinetic one is `+[37, 38)`). Run it from the opening, then read its held state out:
```
METRIC=<that metric> UNIT_MS=1900000 DEADLINE_S=1900 RAYON_NUM_THREADS=4 \
  bash research/runs/u6/chain.sh $C0 q2 out/q2 16 8 0/1 0/1 > out/q2/chain.txt
timeout 5400 $B executed evaluate order2 2026093012 128 out/q2/held <label>=<the final state chain.txt names>
```
Then the like-for-like control, the kinetic chain from the opening under the same acceptance:
```
METRIC=kinetic UNIT_MS=1900000 DEADLINE_S=1900 RAYON_NUM_THREADS=4 \
  bash research/runs/u6/chain.sh $C0 q2k out/q2k 16 8 0/1 0/1 > out/q2k/chain.txt
timeout 5400 $B executed evaluate order2 2026093012 128 out/q2k/held <label>=<its final state>
```
Report each chain's per-move lines (step size, held-sheet and released comparisons, closes), its
final state (the last closed run's end, restored with its byte check if a run was open), and the
held-out whole sections and stations right by station.

## Q3. m7's move with halvings down to the lattice's end (branch `claude/run-end-behaviour-aifrqz`)
```
$B executed run order2 2026093061 8 out/q3 m7=$S/m7.state lock-dec kinetic 1 1800000
```
The header prints the lattice exponent and σ (64 decisions at 1/16 bit, the same σ as `chain.sh`).

## Q4. The joined move from the first stored state where it asks for a shorter memory

The joined solve's `own − supplied` is negative first at w3 (read on the PC: `−4483845/2048`; positive
at w1, w2, w7, w9; negative at w3..w6, w8, w10, w11, w13..w16):
```
METRIC=kinetic-modulus UNIT_MS=1900000 DEADLINE_S=1900 RAYON_NUM_THREADS=4 \
  bash research/runs/u6/chain.sh $S/w3.state q4 out/q4 16 8 0/1 0/1 > out/q4/chain.txt
timeout 5400 $B executed evaluate order2 2026093012 128 out/q4/held <label>=<its final state>
```
Report per move ρ, the line `the joined modulus` (Δρ, own, supplied, s) or `the modulus held at its
bound`, and the first move where ρ leaves `102837/131072`.

## Q5. From the diagnostic chain's move-13 opening to a close or a refusal (branch `claude/run-end-behaviour-aifrqz`)
```
$B executed run order2 2026093061 8 out/q5 m13=$S/r13.state lock-dec kinetic none <cap 32 moves, in the branch's syntax>
```
`r13.state` carries ρ = `168127/262144`. Report the last line (closed at move k, refused, or
INCOMPLETE).

## Q6. The commitment turns at m7 (#225 read 1)
```
timeout 1800 $B executed instants order2 2026093061 8 inc=$S/m7.state succ=$S/m7-2048.state
```
Report request 3's stations 2 and 5: `t`, `⌈t⌉` enclosures at both states.

## Q7. An upper bound on the pass between w16's basin and the fit's
Leg (a), `E` along the segment from w16 to the fit at ρ₀; leg (b), the fit's `E` with ρ walked down:
```
for s in 0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1; do
  timeout 1800 $B executed locks order2 2026093061 8 "a$s=$S/w16.state+$S/fit8_port.txt@102837/131072:$s" lock-dec
done
for r in 102837/131072 3/4 11/16 5/8 9/16 168127/262144; do
  timeout 1800 $B executed locks order2 2026093061 8 "b$r=$S/fit8_port.txt@$r" lock-dec
done
```
Report each read's first line (L, X, solved, whole, stations right). The largest L along both legs
bounds the pass from above.

## Q8. Where the decisions change along m6's and m7's directions, by cut index (#211 §7)
```
timeout 10800 $B executed spectrum order2 2026093061 8 m6=$S/m6.state lock-dec kinetic 1/2048 1/1024 16 64
timeout 10800 $B executed spectrum order2 2026093061 8 m7=$S/m7.state lock-dec kinetic 0 1/2048 16 64
```
Report the header (the lattice unit), each read's cut index, and every wall (its two cut indices,
its jump `J`, and the requests it changes).

## Q9. Each station through the continuing contact path (record §6's gate)

At m6 and at w16, the same 128 held-out requests read three ways: a `Word` opened on the
constitution at each request's own current and moment, run forward over the receiver's epochs and
read by the declared receiver (the contact path); the bank's reads of the same open section (the
release's first refinement); and the bank's release.
```
timeout 5400 $B executed word-read order2 2026093012 128 m6=$S/m6.state w16=$S/w16.state
```
Report the line per source: the receiver's epoch count and stations right by station under each of
the three reads. The gate (record §6): the word's stations right at w16 exceed m6's by at least 28 of
1024. The receiver's epoch count must equal the 8 stations; if it does not, report it and stop.
Smoke first on 2 requests (`… 2026093012 2 …`), then the 128.
