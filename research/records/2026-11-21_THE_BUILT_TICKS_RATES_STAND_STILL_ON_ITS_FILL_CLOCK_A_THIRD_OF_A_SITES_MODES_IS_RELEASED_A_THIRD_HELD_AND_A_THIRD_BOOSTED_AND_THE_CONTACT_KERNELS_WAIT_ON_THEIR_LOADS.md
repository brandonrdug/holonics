# The built tick's rates stand still on its fill clock: a third of a site's modes is released, a third held and a third boosted, and the contact kernels wait on their loads

November 21, 2026, 00:59 to 03:00 UTC, on the PC (RTX 4080 SUPER, the host's 24 threads). Refs #404, #407, #410. The engineering report of
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

### 3.1 The news write's premise: the comparison's descent does not prefer the boosted third

Read at 01:54 to 01:56 UTC, its guess fixed first (`LEAK_GUESS.txt`): a leak `x ← x + g(x) − Λ x` founded at `Λ = 0` reads every bit of
the built tick, and its first descent is along `M = Σ_(t,k) λ_t^(k+1) (x_t^k)ᵀ`, the covector each tick's return receives against the
state the tick began from (`a_leaks_first_deposit_against_the_ticks_gains`, `tools/tick_gains.py --leak`). On L71's end state at its own
four ticks, the same 240 sites, against the tick's block at its last tick (`k = 3`, where the lanes' fill is 0.43 to 0.82: the line's
pass ends before the running mean settles): the first-order change of each eigenvalue under `J − ηM` lowers the gain of 43 to 57% of the
boosted modes, 34 to 62% of the held and 39 to 59% of the released, for the region's `M` and each site's own alike (`leak.txt`), and the
region's `M` stands near rank one (its largest singular value 67% of its square norm). Guess: L1, no preference within 0.4 to 0.6 in each
kind (held for the boosted at every site, missed at its edges for the held at two sites and the released at one); L2, near rank one
(held). So a leak whose map the comparison deposits from zero is pushed along the region's one mean covector against its mean state, and
nothing in that push contracts what grows rather than what holds: the comparison's descent does not supply the contraction
(`agent-inferred`). The rate at which a store contracts is the store's own (the stores-and-caches law: a store holds by upkeep at a finite
quality; the method's rule that a temperature is a store's state), so the leak's strength is founded as a store's balance, and the
comparison moves only what it reaches. The arm waits on that founding law, which is the formal thread's to state at its consumer.

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

The first such change (01:25 to 01:36 UTC, [its receipt](receipts/2026-11-21_tick-gains/README.md)): the forward contact's paced skins
staged with the chunk's terms, every bit kept (the card's suite, 24 sections of L71 reproduced). The kernel reads 7.5% shorter a launch
and the section 2.6 ms shorter in a warmed hold (520.4 against 517.8, spreads 2.4 and 2.0); the guess of 10 to 18% on the kernel missed,
because the skin lines' samples were waits that the values' loads beside them still stand behind (`agent-inferred`).

## 5. What the pass's ticks change

The 17-tick read prints a first step 0.6% under the 12-tick read's (5,887,288 against 5,923,141 millionths at tick 0, the chart's step
at tick 4 12,351 against 12,656): the declared count reaches the pass before its first tick, so a read at raised ticks is not the
line's four-tick pass at its own ticks. The line trains at four, where the fill is under two and the rates of §2 have not settled; the
read is of the tick's form, which the raised count leaves as it is (`agent-inferred`).

## 6. The site maps' polygons

The lattice record's §6.2 read, its guess taken whole and fixed at 02:00 UTC (`POLY_GUESS.txt`): on L71's end state each site map that reads
or writes the face (`read` `224 × 224`, `out` `224 × 64`, `w` `224 × 1088`, and `q`, `v`, `a`, `b` reading the face's chart), its grains
(singular values on the material's grain `2^(−24)`) counted by octave, the polygon's breaks (the sorted ranks where the octave changes), and
for the square `read` its rates (eigenvalues' moduli) against its grains (`a_parts_transport_for_its_polygons`, `tools/tick_gains.py
--polygons`, `polygons.txt`).

- The counts by octave are unequal by 11 to 43 times between the fullest occupied octave and the emptiest (P1 held at every map).
- No break falls on a multiple of 32 (P2 held at every map). The face's own reading, `read`, spreads its 224 grains over 17 octaves
  (2^2 down to 2^(−14)): 10, 32, 37, 35, 34, 28, 20, 12, 7, 4, 3 and 1 from the top, breaks at 10, 42, 79, 114, 148, 176 and 196, so its middle
  five octaves are segments of 28 to 37 places, and its last 28 places hold gains under 1/64 of the largest.
- Its rates' polygon meets its grains' only at the ends (both −281.60 bits, the determinant, as Weyl's inequality asks), and stands 26 to 45
  bits from it at ranks 32 to 192: the reading mixes all its places and splits nowhere, so the face's reading is one carrier, and the seven
  lanes of 32 are not segments of its own transport (`agent-inferred`).

So a width read from a part's own polygon is a segment of about one octave of its grains, five such segments of 28 to 37 places in the
face's reading, with a tail of 28 places a register narrower than the rest needs; the lanes' 32 is not a break of any map read here. Which
part a width belongs to is the partition's to found at the part's need (`radix.register-composition`, the precision law); this read gives
the counts it would found on, and changes nothing in the line.

## 7. The fork's closing orders on the carry circles

The lattice record's §6.3 read, its guess taken whole and fixed at 02:05 UTC (`FORK_GUESS.txt`): three pairs opened `([{` and closed in each
of the six orders of `)]}` inside 30 fillers authored for the read (`fork_fillers.txt`: 20 code-like lines, 10 prose-like), each line a region
of its own through the line's codec on L71's end state; at the line's end the last tick's circle operand `Q(t − 1)` of the 512 circles
(the 256 scanned from the left carry it; those from the right stand at rest there), each filler's mean over its six orders taken out (the
common mode), the state as it stands (pumped) and with the pump's chart and bias at zero (`p = 0`, so `η = 0`, the unpumped circles)
(`the_forks_closing_orders_on_the_carry_circles`, `tools/tick_gains.py --fork`, `fork.txt`). The plane is the orders' own: the two
largest principal directions of the six orders' centroids on half the fillers, read on the other half and the halves swapped. A planted
hexagon at half the residual's own spread, added to the read's residuals on the same shapes, is recovered whole first (the held half
reads its order and parity at 1.000, its corners 59 to 61 degrees apart).

| circles | the held half reads the order (chance 0.167) | the parity (chance 0.5) | between-order share of the plane | the centroids' gaps around the plane (degrees) |
|---|---|---|---|---|
| unpumped | 0.478 | 0.650 | 0.464 | 40, 90, 10, 71, 58, 90 |
| pumped | 0.444 | 0.622 | 0.445 | 58, 106, 1, 31, 88, 76 |

Score: F1 (two clusters by parity, unpumped) missed; F2 (six on a hexagon, alternating in parity, pumped) missed. What the centroids show
instead: the orders that close on the same last bracket stand together (`]`, `)`, `}` and `)`, `]`, `}`, both ending on `}`, one degree apart
pumped and ten unpumped; the pairs ending on `]` and on `)` 40 to 58 degrees apart), so the circles at the line's end hold the last closer
and little of the two before it. Three clusters by the last closer with the order within each at chance would read the order at 0.5 and
the parity near 0.5; the reads stand at 0.44 to 0.48 and 0.62 to 0.65. The pump changes neither reading by more than 0.04. So on this state the
circles' terminal operand is a recency of one symbol at the depth of three pairs, the crossings' order is not where it is held, and a
reading of crossed against nested binding is owed elsewhere than this operand: in prefix states, as the failure-group record's §8.4 says
of one terminal product (`agent-inferred`).

## 8. The leak's reads at set strengths

The formal thread's founding law for the leak (merged as #1070, the record of the same night, atlas `store.leak-founded-by-own-news`): by face
lane, `x ← γx + g` with `γ = 1/(1 + d)` and `d` a state founded at zero (the built tick bit for bit), `d` rising where the cosine `c` of
successive chart moves is positive, falling where it is negative, resting at zero; forward only. It offered six reads with their guess
fixed at 02:22:29 UTC before any was read (`receipts/2026-11-21_leak-balance/GUESS.txt` of that record). Read here at 02:33 UTC
(`a_lane_leaks_reads_at_set_strengths`, `leak_reads.txt`): the ruler's lane leak `x ← (1 − δ)x + g` at a set `δ` (`Constitution::ruler_leak`, a
reading, no state), L71's end state, the same 240 sites, its ticks raised to 17, `δ` at 1/4, 1/2, 3/4, 0.8506 and 1, and the line's own
four ticks with no leak.

- B1 (on the built tick the pooled cosine over ticks 5 to 16 above 0.9 at every lane): held, 0.964 to 0.986. Its second half (at the line's
  own four ticks, positive at every lane between 0.2 and 0.8): missed, the cosine of the first moves standing at −0.42 to +0.20, negative at
  six lanes of seven; the first ticks' moves alternate.
- B2 (at `δ = 1/2` the ratio of successive moves level in 0.5 to 0.8 at ticks 10 to 16): held, 0.611 rising to 0.623; the built tick's 0.787
  rising to 0.866.
- B3 (the cosine over ticks 1 to 16 falls with `δ` and changes sign between 3/4 and 1): missed as stated. It falls with `δ` at every lane, but
  it is negative at six lanes already at `δ = 0`, the first ticks' alternation weighing on it. Over ticks 5 to 16, where the law's rest is read
  (the late `c` is the dominant multiplier's sign), it stands at 0.93 to 0.97 up to `δ = 1/2`, 0.11 to 0.69 at 3/4, −0.49 to +0.26 at 0.85 and
  −0.83 to −0.43 at 1: it changes sign between 3/4 and 0.85 at the first four lanes and between 0.85 and 1 at the last three, about the
  rest `δ* = 0.851` the law derives. The moves fall about 0.34 to 0.37 a tick at 0.85 (0.311 derived), 0.46 to 0.51 at 3/4.
- B4 (no growth up to 0.85): held; at every lane the move at tick 16 is 0.000 to 0.096 of the move at tick 6.
- B5 (the held code at 17 ticks and `δ = 1/2` 0.05 to 0.5 nats above the four-tick read): missed, 4.137 against 1.655 nats a place over the 109
  open places, 2.48 above. With no leak the raised ticks alone read 3.422; every `δ` from 1/2 to 1 reads 4.137 to 4.141. The state was trained
  on the four-tick pass's transient, and what a raised pass has to recover is that whole distance.
- F3 (the circles' `|γ|` median under 0.6, under a tenth near a third of a turn at `|γ|³ > 1/2`): held, median 0.400 (0.247 to 0.567 between
  the tenth and ninetieth), 0.0001 near a third of a turn.

So the law's rest stands where it derived it on the late ticks, and the leak contracts every lane geometrically from `δ = 1/2`, while at the
line's four ticks its comparison has the wrong sign at most lanes and would rest `d` at its founding: the leak's consumer is a pass past four
ticks, and such a pass starts 1.8 to 2.5 nats a place behind on this state (`agent-inferred`). Its arm carries that cost: raised ticks with the
law beside raised ticks without it, from one saved state, read over laps long enough for both to recover.

### 8.1 The opening held, and why the arm waits

The formal thread read §8 at its source (02:52 UTC, relayed): the pooled cosine is ruled by the first pairs of moves, whose weights are
288.7, 209.9, 67.2, 8.6, 1.4 and 0.4 (`10^12`) from the first pair, so pairs from the fifth on hold under 2% and the deposit as built would move
`d` at one lane only (lane 2, to about `δ = 0.38` at eight ticks); the rest near `δ = 0.85` belongs to ticks five on, 0.4% of the weight.
And the law as built leaks the opening with the currents, where the built tick keeps the opening as a term of its sum; corrected, the tick is
`x ← x⁰ + γ(x − x⁰) + g`, the same bits at `d = 0`. The host law now holds the opening (`lane_leak_tick`, its return `+δ λ^(k+1)` into the
opening once the ticks have returned), and its tests pass as before. Read with the opening held (02:54 UTC, `leak_reads_opening_held.txt`;
the ruler's leak with `Constitution::ruler_leak_hold`): the held code at 17 ticks reads 4.004, 3.991, 3.932, 3.911 and 3.877 nats a place at
`δ` = 1/4, 1/2, 3/4, 0.85 and 1, against 4.137 to 4.141 with the opening leaked, 3.422 with no leak and 1.655 at the line's four ticks: holding the
opening recovers 0.13 to 0.26 nats and the raised read stays above 3.0 at every `δ` (the formal thread's H4, fixed 02:52:10 UTC, held). The
cosine by pair of moves on the built tick: −0.71 to −0.04 at the first pair, −0.22 to +0.49 at the second, 0.70 to 0.87 at the fourth, 0.95 to
0.99 from the fifth; under the leak the late pairs' cosine crosses zero between 3/4 and 0.85 at the first four lanes, as before.

So the arm as designed would be nearly its own control (the formal thread's guess: the two arms' held codes agree within the scatter between
laps), and it is not given its day of card. The card realization written for it is set aside with this reading
(`lane_leak_card_kernels_set_aside.patch`: the leak's tick, the stores' news by region and lane, and their release into the covector); the
host law stands, founded at zero bit for bit, with the opening held, `d` on the chart `ℓ = log₂(1 + d)` with `γ = 2^(−ℓ)` the formal thread's
choice for when it is next taken up.

## 9. Atlas

`tower.field-tick-rates-on-the-fill-clock` (new, measured), using `tower.field-tick-running-mean`, `motion.unit-power-push-log-clock`,
`motion.relaxed-step-three-kinds` and `hodge.newton-above-hodge-is-a-mixing`.

## 10. Sources

`crates/engine/src/contact.rs` (`Constitution::pass_probed`, `TickProbe`), `crates/engine/src/field/tests.rs`
(`the_ticks_gains_by_finite_differences`, `the_trained_ticks_residual_by_tick`), `tools/tick_gains.py`, `crates/engine-cuda/kernels/field.cu`
at `e63c81396`; the receipts directory above.
