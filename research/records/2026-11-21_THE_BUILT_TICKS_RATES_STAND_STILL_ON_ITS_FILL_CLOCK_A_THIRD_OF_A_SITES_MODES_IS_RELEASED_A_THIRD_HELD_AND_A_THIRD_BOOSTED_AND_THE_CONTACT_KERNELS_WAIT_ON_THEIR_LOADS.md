# The built tick's rates stand still on its fill clock: a third of a site's modes is released, a third held and a third boosted, and the contact kernels wait on their loads

November 21, 2026, 00:59 to 01:30 UTC, on the PC (RTX 4080 SUPER, the host's 24 threads). Refs #404, #407, #410. The engineering report of
November 20 (its §11 list, [the receipts](receipts/2026-11-20_engineering/README.md)) read beside the lattice record's §6.1
([the record](2026-11-20_A_LATTICE_AN_APERTURE_AND_A_DILATION_ARE_ONE_LENS_THE_HEXAGON_IS_THREE_CLASSES_WITHOUT_THEIR_COMMON_MODE_AND_THE_CHARACTERISTIC_POLYGON_LIES_ON_OR_ABOVE_THE_GRAINS_IN_LEAN.md)),
as one design: whether the tick contracts decides both what a pass retains and how long the return's tape must be. Two readings, both
rulers; no state entered the line and nothing was built into it. Receipts: [receipts/2026-11-21_tick-gains](receipts/2026-11-21_tick-gains/).

## 1. The read and its guess

`tree`: the built tick writes a site by sums, `x ← x + g(x)`, and every reader divides the filling out
(`tower.field-tick-running-mean`), so its linear part is `J = I + ∂g/∂x`, and on the clock of the site's own amplitude the eigenvalues
are `1 + ν_j/fill` with steady exponents `ν_j` (`motion.unit-power-push-log-clock`, whose `ε_j` these are with the sign turned). The
lattice record asked for the eigenvalues of the tick's reading-then-writing map by finite differences at saved states, at ticks 4, 8
and 16, each distance from one multiplied by the site's fill, with a guess fixed first. The guess was taken whole from that record and
fixed at 01:12 UTC before the full read (`GUESS.txt`): G1, seven eigenvalues a site within 0.01 of one (one a filled lane: the rays);
G2, the others' median distance from one halves from tick 8 to tick 16 (a ratio of 0.4 to 0.6); G3, the `ν_j` agree across the three
ticks within a quarter of their size; G4, the `|ν_j|` spread over more than a factor of four.

The ruler (`agent-inferred`, the lead): `Constitution::pass_probed` runs the pass as `pass` reads it to tick `k`, and there runs each
perturbed opening state through that one tick with the tick's own operands (its clocks, moments, carried locks and junction); the host
test `the_ticks_gains_by_finite_differences` moves each of a site's 224 entries by `±ε` (`ε` the lane's root mean square released by
ten bits, at least `2^6`) and writes the site's own block of `x⁺ − x⁻`; `tools/tick_gains.py` forms the 224 × 224 block and its
eigenvalues. The state: the store line's L71 end state (width 224, seven face lanes of 32), its declared ticks raised to 17, over the
240 sites of public text the carriers' census read (`docs/THE_ENGINE.md` through the line's codec, 109 open). Sites 120 and 200 open,
122 and 201 known. 5,376 perturbed ticks in 91 s against a projection of 100 s from a one-site development read of 8.3 s.

## 2. What was read

The fill: a lane's `‖x^k‖/‖x^(k+1) − x^k‖`, the state over one tick's current. It reads 1.2 to 2.2 at tick 4, 4.7 to 6.4 at tick 8 and
12.4 to 14.7 at tick 16 (the site's median 1.4 to 1.6, 5.1 to 5.6, 12.8 to 13.8): the fill is `k + a` with `a` near −2.5, because the
state grew faster than the count over the first ticks (the state's step against the state reads 0.53, 1.49 and 2.44 at ticks 1 to 3 of
`tick_residual_L71_17.txt`). On the tick count itself, `k + 1`, the exponents do not agree from tick 4 to 8 (median relative difference
0.52 to 0.57); on the fill they do.

| site | kind | ν agree 4→8 (median rel. diff, share within ¼) | 8→16 | spread p90/p10 of \|ν\| | halving 8→16 |
|---|---|---|---|---|---|
| 120 | open | 0.101, 0.862 | 0.071, 0.871 | 30.1 | 0.544 |
| 122 | known | 0.090, 0.839 | 0.079, 0.893 | 27.5 | 0.583 |
| 200 | open | 0.095, 0.862 | 0.074, 0.848 | 27.9 | 0.552 |
| 201 | known | 0.162, 0.781 | 0.045, 0.897 | 38.5 | 0.603 |

The split on the fill clock, a site's 224 modes at tick 16 (ticks 4 and 8 within a few modes of it, `L71_gains.txt`):

| site | released, ν < −0.02 | held, \|ν\| < 0.02 | of them \|ν\| < 0.005 | boosted, ν > 0.02 | ν from, to |
|---|---|---|---|---|---|
| 120 | 82 | 68 | 21 | 74 | −0.505, +0.189 |
| 122 | 84 | 72 | 19 | 68 | −0.500, +0.193 |
| 200 | 82 | 70 | 19 | 72 | −0.523, +0.184 |
| 201 | 85 | 68 | 24 | 71 | −0.536, +0.187 |

A difference of 0.005 in `ν` is about the read's own resolution at tick 16 (a central difference over `2ε` against the tick's rounding
of a few units), so the 19 to 24 below it are read as held and not counted finer. Three further readings: the block is far from normal,
its largest singular value of `fill · (J − I)` standing at 5.9 to 6.4 at every site and tick where the largest `|ν|` is 0.54
(`L71_octaves.txt`), which is the shear of the lattice record's §6.1 seen in its non-normal part; 87.5 to 88.6% of `J − I` stands off the
lane-diagonal blocks, so the tick's response is mostly across lanes; and the last three lanes' own blocks read every one of their 32
eigenvalues at one from tick 8 on, so those lanes are moved only by the other lanes.

Score: G1 missed (about 70 held a site, ten times the seven rays); G2 held at three sites of four (0.544, 0.583, 0.552; 0.603 at site
201); G3 held on the lanes' fill (78 to 90% of the ranks within a quarter) and missed on the tick count; G4 held (27 to 39 against 4).

## 3. What it says, on the objects

`agent-inferred` from §2. The built tick is the unit-power push of `motion.unit-power-push-log-clock` on a clock of `ln(k + a)` with
`a` near −2.5: its exponents are steady and read on the site's own amplitude, and no rate stands on the tick count. Its modes are of
the swing's three kinds: a third relaxes as a power (`k^ν`, `ν` to −0.5), a third holds (the rays among them, and some 60 more that no
reading of these four sites tells apart from held), and a third grows as a power, `ν` up to +0.19 and +0.31 at tick 4, which is a boost
(`motion.quadratic-three-kinds`). Two consequences:

- **The tape.** At the built tick's form no tolerance releases a tick's operands: nothing contracts at a rate on the count, and a
  third of the modes grows. The engineering report's batches stay three a section at this form (its §8 premise, read again on the
  tick's own gains).
- **Which leak.** A uniform leak, `x ← (1 − λ)x + g(x)`, carries the same exponents to rates on the count and cures a flip, never a
  boost (`motion.relaxed-step-three-kinds`): the third that grows would grow at a rate. A news write, `x ← x + γ(y − P x)`, contracts
  what its reading `P` sees, at slopes `−log|1 − γμ_j|`, and keeps `P`'s kernel. So the leak's arm is the news write, and its premise,
  read before it is built (the method's "a premise is a presence at the consumer"), is whether the boosted third lies in what `P` sees:
  the projection of the boosted eigenvectors on `P`'s range at the same sites and ticks. Its guess is fixed when `P` is named at its
  consumer.

## 4. The contact kernels wait on their loads

The engineering report's next item was the contact kernels' register width (their 128-bit sums a thread). Read first, as a premise:
`ptxas -v` on the merged tree's kernels (`registers_*blocks.txt`; `variant.sh`) and Nsight Compute's source counters on a line-info build,
one launch each after 40 of warm-up on the line's first sections from Y70's end, under the card's lock with OBS the one other process
(`ncu_src.sh`, `stalls_*.txt`).

- Registers: `field_contact_l4` 80 at its bound of six blocks with 168 octets of stack (318 and 564 octets of spill stores and loads),
  96 at five blocks still spilling, 128 at four with none; `field_contact_rows` 128 with 64 octets of stack; `field_exposure` 80 and
  spilling at six; `field_contact_columns` 72 with none; `field_pace_skin_back` 96.
- Stalls: in `field_contact_l4` 19.8% of the warps' samples stand on two lines, the paced head's skin word `w.skin[...]` and its check
  (lines 935 and 957 of `field.cu`), every one a long-scoreboard wait on a global load addressed from the staged term; in
  `field_contact_rows` the eight-mode pair covector's value loads lead (9.5%, line 5442), in `field_contact_columns` the receiver's
  index and gap (16.0%, line 5725), in `field_pace_skin_back` the crowd's summed values (6.5% and 3.8%).

So the kernels wait on dependent loads, one term's chain at a time, and their 128-bit arithmetic is not where they stand: narrowing the
sums alone would lift occupancy only where it frees a block's registers, and the loads would still wait. The lever the counters give is
the one the rows' words already took on November 16: a chunk's skins, values and indices staged together by asynchronous copies, so the
loads stand in flight at once. It keeps every bit (the same terms in the same order). The contact family holds about 95 ms of a
section's 512 (rows 27, columns 22, the forward contact 16, the paced skins' return 14, the skins' fill 8 and the exposure 8, from the
merged build's trace of 40 sections), 31.5 times its floor; it is the realization's next item, beside the arm of §3.

## 5. What the pass's ticks change

The 17-tick read prints a first step 0.6% under the 12-tick read's (5,887,288 against 5,923,141 millionths at tick 0, the chart's step
at tick 4 12,351 against 12,656): the declared count reaches the pass before its first tick, so a read at raised ticks is not the
line's four-tick pass at its own ticks. The line trains at four, where the fill is under two and the rates of §2 have not settled; the
read is of the tick's form, which the raised count leaves as it is (`agent-inferred`).

## 6. Atlas

`tower.field-tick-rates-on-the-fill-clock` (new, measured), using `tower.field-tick-running-mean`, `motion.unit-power-push-log-clock`,
`motion.relaxed-step-three-kinds` and `hodge.newton-above-hodge-is-a-mixing`.

## 7. Sources

`crates/engine/src/contact.rs` (`Constitution::pass_probed`, `TickProbe`), `crates/engine/src/field/tests.rs`
(`the_ticks_gains_by_finite_differences`, `the_trained_ticks_residual_by_tick`), `tools/tick_gains.py`, `crates/engine-cuda/kernels/field.cu`
at `e63c81396`; the receipts directory above.
