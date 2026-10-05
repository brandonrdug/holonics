# The refit's ingredients ablated: which part of the exterior fit reaches the representation

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured],
exterior float probe; [agent-inferred] where marked.

## 1. The question, fixed before the runs

Step 1's blocker stands as the kinetic move left it: every native move descends the comparison and
none reaches the decisions, while the station-framed refit (96 whole sections of 128 on order-2's
held-out requests) shows a representation exists
([the station-framed placement](2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md) §2;
[the representation](2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)).
The refit (`eO_fit.py`, retired with the notebook's probe at `e214ccc8`) differs from the native
move in its optimizer: float Adam on `E` with a cosine schedule (momentum `9/10` and a per-coordinate
second moment `999/1000`), 400 steps of 16 requests re-read on the release's own trajectory, and `ρ` by
Adam on a central difference. The native moves are certified steps in the port's or the
receiver's metric, each refused unless its executed release falls, a few at a time.

The claim this loop can make is narrow: which ingredient of the exterior optimizer carries it to the
representation. Four arms, every other setting the refit's (`order2 400 256 101 0.03 0.05 1 16`, learning rates `3/100` and `1/20`):
- `adam`, the refit (the reproduction: 96 whole expected);
- `rms`, the per-coordinate second moment without momentum;
- `momentum`, momentum without the per-coordinate scaling;
- `sgd`, neither.

The arms without the per-coordinate scaling take a global step matched to Adam's first step's
root-mean-square. **Acceptance of the location.** An ingredient is located when the arms that keep
it reach at least half the refit's whole sections (48 of 128) and the arms that drop it reach fewer
than a tenth of them; otherwise the optimizer is not the location, and the record says so. Nothing
native changes in this loop.

**What this loop's arms cannot show** (fixed before the arms finished). A lower loss or more whole
sections from an exterior float optimizer, read through a classification, is not the mechanism (the
kinetic move's record §2; the comparison-descent line is closed). The arms are diagnostic only: their
sole output is which ingredient matters. The loop's deliverable is that ingredient's native
counterpart, derived from the existing chain (the constitution's own update, its Fisher form, the
release's schedule), and its acceptance is the METHOD's: a return reaching a locus, changing its
constitution through that native law, and consumed on a later cut, with order-2's held-out sections
read natively. No Adam arm's number stands in for it.

## 2. Measured

Held-out whole sections of 128 at step 400 (the best state read along the way in brackets), three seeds per arm
([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/)):

| Arm | seed 101 | seed 202 | seed 303 |
|---|---|---|---|
| `adam` (the refit) | 36 (43) | 46 (53) | 49 (52) |
| `rms` (no momentum) | 54 (54) | 72 (72) | 47 (52) |
| `momentum` (no per-coordinate scale) | refused at step ~300, a singular solve (34) | 31 (45) | refused (36) |
| `sgd` (neither) | 18 (27): `E` ran to its bound at step 200 and `ρ` back to one | 57 (57) | 57 (71) |

- **The reproduction.** The float refit reaches 36 to 49 whole sections, not the record's 96. That
  96 was the exported `E` read natively after rounding to the lattice (the station-framed record
  §2); the float release here is the probe's own, and the run-to-run spread is large (the same arm
  moves by 10 to 20 sections between the states read along the way).
- **No ingredient is located.** Plain gradient steps with the matched step size reach 57 on two of
  three seeds, as many as the scaled arms; the per-coordinate scale is not required, and momentum is
  not either (it destabilizes the solve). The acceptance's location test is not met by any arm.

[agent-inferred] What the float fits share and the native moves lack is not the metric: every arm
takes 400 small, decaying, stochastic steps, each accepted whatever it does to the comparison,
re-read on the release's own trajectory. The Lean thread's baseline (#195) proves every candidate
move is a gradient step under some metric and stops only where the gradient vanishes; the native
chain stopped first at its acceptance condition (`OwnNotBelow`, the executed release must fall). The step-1
records found the chord to the refit rising before it falls (the stiffness record). So the next
candidate location is the acceptance condition together with the step schedule, read first on the float path
itself: whether the plain-gradient arm's own comparison rises along its way to the sections.

## 3. The plain-gradient path's own comparison

The `sgd` arm re-run on seeds 202 and 303 with its comparison read every 10 steps on a fixed set of 32
training requests, each re-read on its own trajectory ([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/),
`path_sgd_*.txt`; both again end at 57 whole sections).
- **It climbs above where it started.** Seed 202's opening comparison `[6603/4096, 6604/4096)` is exceeded at step 30
  (by `[6/4096, 7/4096)`); seed 303's `[6588/4096, 6589/4096)` at step 60 (by `[536/4096, 537/4096)`).
- **Its excursions above the running minimum** (the step a rise begins, the step the minimum is
  undercut again, the peak rise): seed 202, ten excursions of 20 to 50 steps, peaks `[8/4096, 9/4096)` to
  `[475/4096, 476/4096)`; seed 303, eight of 20 to 60 steps, peaks `[20/4096, 21/4096)` to `[1970/4096, 1971/4096)` (steps 50 to 100, the largest,
  then `[1241/4096, 1242/4096)` over steps 170 to 200). Each later excursion ends below the earlier minimum.

[agent-inferred] The path that reaches the sections is not monotone in its own comparison over
any stretch of steps, and on one seed it rises well above the opening. An acceptance that admits a
rise only below the largest of the last few adopted comparisons cannot follow it; it needs an
excursion above a held state, bounded in height and length, with the certified decrease owed over the
excursion as a whole. The numbers above are what such a law's run length and step schedule read.

## 4. The released comparison's jump at m7, decision by decision, beside the float path's

**The two parts of a move's change.** The released comparison `ℓ` is the cross-entropy between the
release and its targets: the surprise crossing the receiver's section, summed over 8 requests × 8
stations. A move deposits into `E`. Each lock in the release is a parametron settled on one half-turn
sheet.
- With every lock held on its sheet, `ℓ` is a smooth function of `E`: the **held-sheet comparison**
  (the code's "fixed mask"). Each accepted move must lower it, certified at first order: a descent
  of the comparison within one lock configuration.
- Relocking after the move can settle the release into another lock configuration. The released `ℓ`
  then differs from the held-sheet `ℓ` by the difference of the comparison's code length between
  the two configurations at the same `E`: the **relocking jump** (the code's "flip"). It is a
  difference of code length, in nats. No map from this comparison to the Holons' stored energy and
  work is derived here, so it is not called an energy (Astra's review, October 2).

The Lean thread proved this split for #202. Both paths were read under it
([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/): `m7_decision_diff.txt`,
`kinetic_chain_m0_m7.txt`, `split_sgd_303.txt`, `flips_sgd_303.txt`). Native values are lower ends in
units of `1/4096` nat, each within `6/4096`.

- **m7's jump is one request's freezing order.** At `η = 1/2048`, request 3 goes from `43957` to
  `77944` (`+33987`). The other seven requests each fall, by `306` in total. Request 3's released
  section is the same before and after: all eight stations at 3, right at two. What changed is the
  order in which its locks froze. Six of its stations are read in different contexts, and three of
  their leading classes change (stations 3, 6, 7). Per station: 1 `+2742`, 2 `−105`, 3 `+6100`,
  4 `+11986`, 6 `+9452`, 7 `+3815`, 0 `−4`, 5 `−2`.
  - The release locks first the station with the largest certain gap: its leading reading's lower
    end less the strongest rival's upper end. Its reach is the leading reading's upper end less the
    strongest rival's lower end.
  - The swap is at request 3's second freeze, between stations 2 and 5 (units `1/2^24`). At m7,
    station 2's certain gap `187540480` exceeds station 5's reach `187166208` by `374272`, about 140
    cell widths. At the step `η = 1/2048`, station 5's certain gap `187395584` exceeds station 2's
    reach `187339776` by `55808`. Both orders are certified at the receiver's resolution, opposite
    ways. Along the step, station 2's gap fell by `203264` and station 5's rose by `231936`. The two
    lock gaps truly cross, at `731/840` of the `1/2048` step if their motion is linear, just inside the smallest
    step the move tries.
  - The freezing order goes from `[0],[2],[4],[5],[6],[7],[3],[1]` to `[0],[5],[7],[6],[4],[3],[2],[1]`.
    Freezing station 5 before station 2 changes the context every later station is read in, so the
    release settles into another configuration with the same released classes. The jump in `ℓ` is a
    level crossing of two locks' drives along the direction of deposition, not a tie below
    resolution. No refinement of any request has an unranked station at either state (0 of 64 at
    each). Locking unranked stations together (#207) leaves this release unchanged.
- **Per step size η** (held-sheet decrease `d`, relocking jump):

  | η | `d` | jump |
  |---|---|---|
  | 1/16 | 33562 | 74106 |
  | 1/32 | 20269 | 45891 |
  | 1/64 | 10853 | 34325 |
  | 1/128 | 5523 | 34174 |
  | 1/256 | 2804 | 34100 |
  | 1/512 | 1419 | 34065 |
  | 1/1024 | 714 | 34047 |
  | 1/2048 | 359 | 34038 |

  - From `1/64` down, the jump moves by `287` while `d` halves with each halving of η. The jump is
    a difference between two configurations' code lengths, not a slope, so it does not shrink with
    the step.
  - A later run of moves repays it once its held-sheet decreases exceed the jump by one receiver
    grain `σ`: at least `(jump + σ)/d` moves. That is 95 moves at `1/2048`, and about 4 at `1/64` or 3
    at `1/32`, if the jump held.
  - Only the `1/2048` diff was taken; that the same request carries the jump at the other step sizes
    is inferred from its constant size.
  - m6 was accepted at `1/2048` (`d = 361`, no jump), and jumped from `1/1024` up.
  - m7's halvings ended at their count, not at the lattice: from `η₀ = 1/16` the eighth trial is
    `1/2048`, and `LADDER_DEPTH = 8` stopped the move there, refused. The lattice floor (`η·2u < λ`,
    #230) was not reached by then; whether m7 adopts at `1/4096` or below is Q3 of
    `research/runs/u6/CLOUD_QUEUE.md`. The crossing at `731/840` of the `1/2048` step is located only
    under linear motion of the two gaps; what is certified is that they cross inside that step.
- **The float path's rises are not relocking jumps** (`sgd`, seed 303, 32 fixed requests, read every
  10 steps to step 130).
  - Relocking changes the freezing order on 29 to 32 of the 32 requests in every 10-step stretch to
    step 200, falling to 2 by step 390. Yet its share of `ℓ` per stretch stays between `[-293/4096, -292/4096)` and
    `[227/4096, 228/4096)` nats per term, takes both signs, and nets `[-102/4096, -101/4096)` over the 130 steps.
  - The rises are in the held-sheet comparison itself. Single steps raise it, by `[3275/4096, 3276/4096)` per term
    at step 57 (the rise over steps 50 to 100), and by `[1048/4096, 1049/4096)`, `[1028/4096, 1029/4096)` and `[1290/4096, 1291/4096)` at steps 1, 77
    and 78. Later steps repay them.
  - The float path deposits from minibatches of other requests, so the comparison it reads can
    rise. The native move deposits from the requests it reads, so its held-sheet comparison falls,
    and its only rise is a relocking jump.
  - Per term, m7's jump (`34038/64`, between `531/4096` and `532/4096`) exceeds every float
    stretch's relocking share (at most `227/4096`), and it sits in 1 of 8 requests.
- **Float steps per native move.** Native `η = 1/32` moves (m0 to m3) lower the held-sheet comparison
  by `573/4096` to `574/4096` per term. A float step lowers it, per term:
  - `21/4096` to `22/4096` at the net mean over 130 steps;
  - `64/4096` to `65/4096` over the first 10 steps;
  - `101/4096` to `102/4096` at the median descending step.

  One `1/32` move is therefore 26 to 27, 8 to 9, or 5 to 6 float steps by those three rates. The
  float path's rises of 20 to 60 steps come to about 1 to 3 native `1/32` moves at the net rate, or
  3 to 7 at the opening rate. The two per-term means average different families: the float averages
  every open station at every lock snapshot (about 36 terms per request), the native one term per
  station. So the ratio is an enclosure of scale, not an identity.

[agent-inferred] The float path never repays a jump like m7's because it never makes one: its
relocking is frequent, small and of both signs. A run of moves sized on the float rises (about 1 to
7 moves) repays m7's jump only at step sizes of `1/64` or more, where `d` is large enough. The jump
itself is two locks' drives crossing along the deposition's direction, a real reordering the
readings certify on both sides. A smaller step that stops short of the crossing (at `731/840` of the `1/2048` step)
avoids it only by not crossing; the configuration on the far side is reached by any move that passes
it.

## 5. A run of moves crosses m7, and what the chain still lacks against the refit

**The acceptance.** Each move must lower the held-sheet comparison, certified at first order: the
move's own law, unchanged. The released comparison `ℓ` is compared only at the two endpoints of a
run of moves. A run closes when its end lies below its starting state by `σ`, one receiver grain
over the batch: `64 · 1/16 · ln 2` nats at the upper end of `ln 2`'s enclosure (between `11356/4096`
and `11357/4096`). The released `ℓ` of the states inside a run is not constrained. A run that does
not close within `W` moves returns the chain to its starting state, whole (#202).
- `W = 8` is a work bound, chosen (agent-inferred): it covers the measured scale of 1 to 7 moves (§4).
  The laws fix only its least value, 2 and `(jump + σ)/d`, and that bound is necessary, not
  sufficient (Astra's review).
- The comparison is a code length. Each closed run lowers it by at least one grain, so at most
  (opening − floor)/`σ` runs close: a decrease over runs of bounded length rather than at every move.

**From m6, 16 moves** ([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/), `window_chain.txt`;
values `/4096` nats, lower ends):
- Every move was accepted at its largest step whose held-sheet comparison falls: `1/16` at first,
  `1/8` from move 7 on.
- Runs closed at moves 2, 5, 6, 8, 9, 15 and 16. None reached 8 moves, and none returned.
- The released `ℓ` fell from `338257` at m6 to `195744` at w16. The single-move chain had stopped
  at m7's `337896`. The held-sheet excess `X` fell from `156803` to `52990`, and solved terms rose
  from 1 to 37 of 64. Whole sections on the 8 training requests stayed at 0 or 1.
- Held out (order-2, seed `2026093012`, 128 requests, read natively):

  | state | whole | stations right of 1024 | by station |
  |---|---|---|---|
  | m6 | 0 | 235 | 25, 26, 28, 22, 21, 29, 38, 46 |
  | w16 | 0 | 329 | 51, 54, 37, 45, 32, 41, 32, 37 |

  One class in four gives 256 by chance: m6 sits below it and w16 above. Whole sections need about
  `(3/4)^(1/8)` per station for 96 of 128, if stations were independent (inferred). So per-station
  accuracy is the progress reading here, and 0 whole is expected at w16's level.
- Moves took `178306` to `206479` ms each, `3115316` ms in all, against the projection `16 · 460` s;
  the held-out reads took `1669966` ms (m6, 4 threads) and `566219` ms (w16, 16 threads).

**The refit on the same scales**, read natively on the same 8 requests:

| constitution | ρ | `L` | `X` | solved of 64 |
|---|---|---|---|---|
| w16 | `102837/131072` | 195744 | 52990 | 37 |
| the refit's `E` | `137573/262144` (its own) | 133292 | 34021 | 45 |
| the refit's `E` | `102837/131072` (the chain's) | 310210 | 147888 | 15 |
| w16's `E` | `137573/262144` (the refit's) | 574640 | 429220 | 20 |

The refit sits below w16 only at its own memory constant. At the chain's ρ it lies above w16, and
w16's `E` at the refit's ρ lies far above both.

**ρ, the memory transport's modulus.** The chain holds ρ by declaration, not by law: the kinetic
metric moves `E` alone and sets ρ's unit move to zero (`MoveMetric::Kinetic`). The founding law
derives only the bound `ρ ≤ ρ₀` (the one-turn alias, `ρ₀⁶⁰ ≤ 2^(−21)`); sitting at its top is a
choice.
- Along the chain the comparison's slope in ρ, read at each move's starting state (m6, w1..w15), is
  positive at 12 of 16 states, asking for a shorter memory. It is negative over the starts of moves
  8 to 11, and at w16 itself it is `−426589/4096`.
- **The ρ-only walk at w16 climbs** (w16's `E`, ρ lowered; `L`, `X`; solved; training stations
  right of 64):

  | ρ | `L` | `X` | solved | stations |
  |---|---|---|---|---|
  | `102837/131072` (ρ₀) | 195744 | 52990 | 37 | 27 |
  | `102709/131072` (ρ₀ − 2^(−10)) | 196331 | 53808 | 37 | 25 |
  | `101813/131072` (ρ₀ − 2^(−7)) | 218712 | 78119 | 35 | 29 |
  | `3/4` | 279406 | 137900 | 35 | 19 |
  | `11/16` | 384896 | 240950 | 26 | 20 |
  | `5/8` | 475236 | 328710 | 24 | 18 |
  | `9/16` | 547651 | 403415 | 24 | 16 |
  | `137573/262144` | 574640 | 429220 | 20 | 20 |

  With `E` fixed, w16's comparison is least at ρ₀, the top of the admitted set. That walk holds `E`
  fixed, so it does not show where a joined move of `E` and ρ goes from w16: the joined step in ρ
  is the readings' ask less what `E`'s own re-adaptation already supplies through their coupling,
  and that is measured by the joined move (#220), not by this walk.
- [agent-inferred] `E` and ρ co-adapt. The refit's advantage is a joint basin: neither its `E` at
  the chain's ρ nor w16's `E` at its ρ keeps it. The slope's sign along the chain (positive through
  w6, turning as `E` fits ρ₀'s long tail) is the reason to start a joined move from the opening or
  from m6, not from w16.

**Like-for-like on data.** The refit was fit on 256 training requests (`eO_fit.py order2 400 256
101`, minibatches of 16); the chain descends on 8. Fit the same way on the chain's own 8 requests
(`eO_fit.py order2 400 8 101 … 8`, the requests printed by `hnn_prediction -- executed pairs`), the
float fit reaches 39 whole of 128 and 735 stations right on the float probe's held set, against 57
for the 256-request fit, with ρ ending at `168127/262144` on the lattice, a third value. Read
natively (its `E` rounded to the source port's lattice) on the same 128 held-out requests as the
chain, it releases **37 whole of 128 and 717 stations right of 1024** (by station 68, 109, 65, 118,
61, 121, 58, 117; `2088912` ms at 10 threads; two earlier attempts at 4 and 8 threads under load
passed their `2400` s deadline and are incomplete). On the 8 training requests it reads `L =
93355/4096`, `X = 8014/4096`, solved 57 of 64, whole 7 of 8. So data size costs some of the exterior
fit's whole sections, but not most: the same 8 requests and the same native release reach 37 whole
where the native chain reaches 0. ρ's value depends on the data, which argues for learning it rather
than declaring it.

**The memory constant held at the fit's value** (diagnostic: ρ is an exterior constant here). The
chain from the opening with ρ held at `168127/262144`, 16 moves under the same acceptance: runs closed
at moves 1, 2, 3, 4, 12 and 13 (moves 5 to 12 one run of 8, closing at its last move); moves 14 to 16
were an open run at the limit, so the held state is r13: `L = 269593/4096`, `X = 94032/4096`, solved
15 of 64. Held out it releases 0 whole and 272 stations right (26, 29, 43, 23, 23, 13, 46, 69;
`898572` ms at 10 threads). Against the chain at ρ₀ after the same 13 moves from the opening (w7:
`L = 265678/4096`, solved 20) it is no better: held at the fit's ρ from the start, `E` does not find
a lower basin in 13 accepted moves.

**Where the native move goes** (the stored `E` arrays: 600 entries on the lattice `2^(−21)`; the fit's
`E` rounded to it; signed squared cosines as cells of `1/4096`).
- *Reach is not the limit.* The fit's largest entry change from the opening is `4266283` lattice units,
  from m6 `4411164`, from w16 `6458652`; a move changes an entry by at most `1/2` at the kinetic entry
  scale, so 5, 5 and 7 moves reach it. Its largest entry is in `[10032/4096, 10033/4096)`, inside the
  entry bound `8`.
- *The direction is.* `w16 − m6` against `fit − m6`: `−[60, 61)`, covering `[−452/4096, −451/4096)` of the
  distance (away from it) while `|w16 − m6|²` is `[3386, 3387)/4096` of `|fit − m6|²`. Each of the 16
  moves, against `fit − E` from its own start, lies in `−[1, 2)` to `−[133, 134)`: every one negative.
- *The metric turns it, not the comparison.* At the opening (the float probe's `E₀` equals the native
  opening's `E` entry for entry; ρ₀ for both): the native gradient `G` (the plain pullback) against
  the float objective's descent `+[1693, 1694)`; the normal-law step `ΔE` against it `+[1702, 1703)`;
  `G` against the kinetic step (the first accepted kinetic move) `+[37, 38)`; `ΔE` against it
  `+[35, 36)`. The native comparison's gradient agrees with the float one's; the kinetic metric's
  receiver Gauss–Newton step is nearly orthogonal to both. The fit itself lies along a path, not along
  any starting direction (`G` against `fit − opening` `+[2, 3)`), so a metric is judged by the chain it
  produces; that chain is queued (`research/runs/u6/CLOUD_QUEUE.md`, Q2).
- *The joined move's ask on ρ* (`own − supplied` at each stored state, read without moving): positive
  at w1, w2, w7 and w9; negative at w3 to w6, w8, w10, w11 and w13 to w16. The first state asking for
  a shorter memory is w3 (`−4483845/2048`); the joined chain starts there (Q4).

**#207's lock rule along this chain.** At m7, at its `1/2048` successor and at the refit, no refinement
of any request has an eligible station whose reach meets the largest certain gap while it did not
lock with it. Along the chain (w1 to w16) one does, at w9: request 1's first freeze, where station
6's reach `701603840/2^24` meets station 5's certain gap `701591552/2^24`; #207 locks the two together
and the released comparison is unchanged at the grain (`226300/4096` under both rules). #207 releases
the same sections elsewhere on this chain, and its m7 replay and campaign 1's held-out code (`−560 + 15/16 + ε` bits below
PPM-2, the same exact enclosure) are unchanged.

## 6. The plan: read the U6 move through the deposition path

The chain's gains in §5 are read on the bank comparison: a declared receiving bank reads each
station's candidates at the chain's constitution, and the release locks on those readings. Astra's
review (October 2) states the defect: that comparison does not execute the continuing contact and
material-deposition path, so a gain on it is not yet a gain of the machine. This plan decides it.
It runs on Astra's landed continuation (`receiver::reception::continuation`, `98cc6e86`;
`physics::wave::continuation`, `3ef3c6b1`) and on the native `Word` continuation once it lands.

- **The states read.** m6, w16, the diagnostic chain's end at ρ = `168127/262144`, and the joined
  `(E, ρ)` move's end (#220) once run.
- **What each read must show**, per accepted move from m6 to w16:
  - the move's deposition reaches the locus it changes (the source port) as a native deposit, with
    its certified storage growth (`Constitution::deposited`'s conditions, the same ones the move already
    passes);
  - its work at the reached point closes: `W_dep = E(x; Θ′) − E(x; Θ)`, read at the same state;
  - the next passage reads the changed material: a request's `Word`, opened on the successor, reads
    its stations differently from the predecessor's at the same request (Astra's changed-passage
    control, on this constitution).
- **The deciding number.** Held-out per-station accuracy of the release whose station readings
  come from the continuing contact path (a `Word` on the constitution) instead of the declared bank,
  at m6 and at w16, on the same 128 requests (order-2, seed `2026093012`). The bank comparison reads
  235 and 329 of 1024. The gain is real in the deposition path when w16 exceeds m6 there by at least
  28 stations, two binomial spreads at chance (`2·√(1024·3/16)`, below 28; agent-inferred).
- **If it fails** (the path reads w16 within 28 stations of m6, or a move's work does not close, or
  the successor's passage does not change), the bank-comparison chain stops: no further moves are
  run on it, and the executed comparison is rebuilt to read its stations through the contact path
  before any further move. The step-size scan (#211) and the joined move (#220) are then measured on
  that rebuilt comparison, not on the bank.

## 7. The contact-path read of §6 reads nothing at these states

`executed word-read` (`ce4252e7`, Q9) opens a `Word` on the constitution at each request's own
current and moment, runs it over the declared receiver's epochs, and reads each station's class as
the largest real logit of `R P_R v_R`. Read at m6 and w16 on held-out requests
([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/): `word_read_smoke_m6.txt`,
`word_read_receiving_map.txt`):
- **The receiver reads 3 epochs, not 8 stations.** Its aperture is `K·w + 1 = 3`
  (`hnn_prediction.rs`, the declared receiver), so one word reads the next three cells.
- **Its receiving map is zero.** `Constitution::initial` declares `R = 0` on the receiving ring with
  an empty landmark tree, and the U6 chain deposits only into the source port `E` (the move's
  `stepped_source`, a normal-law step from the bank comparison's returns) and holds ρ. At m6 and at
  w16 every station read has every logit zero (3 of 3 reads each), so the word's "class" is the tie's
  first class and its stations right count only targets equal to it: 0 of 8 at both states on one
  request; 2 of 16 at m6 on two. The bank's open section reads 4 and 2 of 8, its release 4 and 4.
- **Reading the stations through `R P_R^(1+j) v_R` is the linear readout retired on September 30**
  (`hnn::prediction`'s header; the [diagnosis](2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md) §3: its descent direction met the executed
  decision's at cosine `39/512`).

So §6's deciding number is withdrawn: no word read at a U6 state can separate m6 from w16 while the
receiving map holds nothing, and forming one would revive the retired readout. In the generation
law the station reader is the receiving bank (`ρ(F^K(I_h)) = T`; `hnn::prediction`), and the U6
move already deposits into `E` natively. What §6 owes is its other two reads, on the move as
executed: the work of each move's deposit at the reached point, `W_dep = E(x; Θ′) − E(x; Θ)`, closing
under Astra's continuation (`receiver::reception::continuation`), and the next passage reading the
changed material. Times: one request at m6 and w16 together `247050` ms on 4 cores, peak resident
`144216064` bytes.

**§6's two remaining reads are empty for this move, by construction.** The deposition work of a
commit is `½⟨x, ΔΘ x⟩` over the power form (`PowerForm::deposition_work`; Lean
`HNN/Word.field_commit_deposition`), and the power form holds the ring admittances, the contacts'
conductances, storage `C`, stiffness `K` and the loaded resonators (`PowerForm::read`). The source
map `E` and the transport ρ are not in it: they enter the passage only through the opening
injection (`SourceMoment::open_storage`). So every U6 move has `W_dep = 0` at every reached point,
and the next passage differs from its predecessor only by its injection. Astra's native return
(`hnn::word::continuation`) admits contact storage `C` and refuses source-map changes until they
have their own transported return. [agent-inferred] The U6 chain's gains are therefore gains of the
source codec read by a declared bank; no material locus of the constitution learns along it.

**The aperture is declared, not derived.** The prediction field's receiver has aperture
`A = K·w + 1 = 3` from the declared words `K = 2` and span `w = 1` (`hnn_prediction.rs`,
`order_declared`); its only law is the refusal of an aperture above the receiver's observability rank
(`ReceivingPhases::declare`). It is a held quantity beside campaign 1's `A = 2` (the
[constants record](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_THE_GRAIN_IS_THE_ROOT_AND_ITS_READING_COUNT_IS_THE_ADMITTED_FUTURE.md) §2),
and it decides how many cells one word reads. No station read through a word is attempted here.

**The next loop's subject** (decided here). No station class is read through `R`: that is the readout
retired above, whether `R` is zero or formed. §6's question is asked instead of the machine's own
receiving path, campaign 1's exposure protocol, whose measurement is a code length, not a station
class: `executed expose` runs `Reference::expose_with` on the prediction field from a stored
constitution, over one cut of the field's declared population (`2^16` cells: order-2 passages at the
training seed, then the 128 held-out passages at seed `2026093012` with their 1024 station cells held
out). The protocol reads each cell's code before it deposits, and deposits into every locus it admits
from the receiver's own comparison at every complete window, held-out windows included: prequential,
not an untouched holdout (`expose_from`, `reference.rs:3999-4008`; corrected October 3, this first
said it never deposits on a held-out cell). `executed evaluate` deposits nothing. Run once from
m6 and once from w16, with everything else equal, it reads whether the U6 move's `E` shortens the
machine's own held-out code. [agent-inferred] The gate is one grain per held-out station: w16's held-out combined
code below m6's by at least `1024 · 1/16 = 64` bits. If it is not, the U6 move's gains do not reach the
machine's receiving path, and the bank chain stops as §6 says.

## 8. What turns the Kinetic step away from `G`, and the throw's acceptance law

Read at the founded opening C0 on the arm lock-dec, 8 requests at seed `2026093061`. The receipts are
in this record's receipts directory: `q1_metric_steps.txt` (runner 1, `fe9c58e9`) and
`q10_kinetic_coupling.txt` (runner 1, `eeafdf7`). Every cosine is a signed squared cosine against the
native gradient `d = −Aᵀc`, in `/4096` cells.

**The target shares' spread is small.** The Coordinate and Witness unit steps lie along `d` at
`[4068, 4069)`. The Kinetic and KineticModulus steps lie at `[37, 38)`, which needs a condition number
near 440 (#235). The 64 lock terms' target shares run from `153439/4769705` to `269508/620323`, so
`max(1/θ_t)/min(1/θ_t) = 34742531220/2572479481 ∈ [13, 14)`. Reweighting a vector's own coordinates
with spread `κ < 14` keeps its `cos² ≥ 4κ/(κ+1)² > 56/225 = (1019 + 101/225)/4096`. The `1/θ_t`
weights act on the terms, and `d = −Aᵀc` sums the terms' pullbacks, so the bound reaches `d` only
where those pullbacks are pairwise orthogonal. Terms that share rows of `E` (below) are not: their
pullbacks can cancel in `d`, and reweighting them can then turn `d` further. Whether the `1/θ_t`
weights alone stay at `[1019, 1020)` or above against `d` is read by Q11 (runner 1, `77afd16`;
`q11_kinetic_coupling.txt`; projection `1400` s from Q10's read, timeout `1800` s, wall `1399930` ms,
peak resident `244817920` bytes). The step with `K` left out, `μ = w = −F⁻¹c` (for a lock term its
target's unit `e_t` over `θ_t`: the `1/θ_t` weights alone), lies at `[1942, 1943)` (Euclidean) and
`[1870, 1871)` (`M`'s metric). It stays above `[1019, 1020)`, but that is measured;
the bound does not give it.

**No single block of the reading Gram carries the turn.** The step is `M⁻¹Aᵀμ`: the chart
`M⁻¹ = H′⁻¹` applied to the readings' pullback, with `μ` from the conjugate-gradient solve of the
witness's form `F = diag(θ) − θθᵀ` against `K = A M⁻¹ Aᵀ` (`kinetic_lift`). `F` acts term by term, so
any coupling across terms comes only through `K`, from terms that share rows of `E`. The chart alone
turns nothing: its first iterate `M⁻¹d` lies at `[4068, 4069)`. With `K` cut to blocks:

| `K` read as | Euclidean | `M`'s metric | Solve |
|---|---|---|---|
| left out, `μ_t = 1/θ_t` | `[1942, 1943)` | `[1870, 1871)` | closed form |
| its diagonal, `μ_t = (1/θ_t)/K_tt` | `[662, 663)` | `[621, 622)` | closed form |
| 64 term blocks | `[852, 853)` | `[800, 801)` | all converged at 5 iterates |
| 8 request blocks (8 terms each) | `[355, 356)` | `[339, 340)` | 4 converged at 38–40, 4 exhausted at 40 |
| whole | `[37, 38)` | `[37, 38)` | exhausted at 320 |

The `1/θ_t` weight alone takes `d` to `[1942, 1943)`, dividing by `K_tt` takes it to `[662, 663)`, and
together they make most of the turn. Coupling inside a term partly undoes it,
coupling inside a request takes it to `[355, 356)`, and the coupling across requests through shared
`E` completes it. The derivations thread's prediction, term blocks in the Coordinate band and request
blocks reaching `[37, 38)`, fails on both counts.

**The deposited step is the solve's 320th iterate, not a converged `K⁻¹w`.** The joint iterates fall
monotonically: `[4068, 4069)` at 1, `[2659, 2660)` at 2, `[653, 654)` at 8, `[258, 259)` at 16,
`[110, 111)` at 32, `[54, 55)` at 64, `[42, 43)` at 128, `[38, 39)` from 188 to 257, and `[37, 38)` from
258 to 320. So the direction holds to one cell over its last 63 iterates, and the turn belongs to `K`,
not to where the solve stopped. In exact arithmetic the solve reaches `K⁻¹w` within its 320 reading
coordinates. Holding every iterate at `JOINT_BITS` (`joint_held`) breaks that, and the solve ends
without its `2⁻³²` energy floor. Q11 reads the residual energy over the opening's: `[10933, 10934)/2^32`
at iterate 188, `[262, 263)/2^32` at 258 and `[16, 17)/2^32` at 320. So the deposited step stops at `[16, 17)/2^32`,
four bits above the `2⁻³²` floor (`16 = 2^4`), and its direction settled at iterate 258 while the
residual fell by a factor in `(262/17, 263/16)`, an interval holding `2^4`.
[agent-inferred] That is a law of the solve's representation, not a property of the metric.

**The throw runs under strict descent, so its control does too.** The throw chain (#240) calls
`move-once`, which holds `ReleaseExcursion::monotone()`. Q2's chains run #202's interval, in which a
successor's released code length is unchecked until the interval closes. At C0 the same trial,
η 1/2 along the Coordinate direction, therefore separates them. Its own release `[517650, 517656)`
lies above the opening's `[500197, 500203)`, so strict descent refuses it and the throw adopts η 1/4
at `[495714, 495719)`. The Coordinate chain adopts η 1/2 with its run open. The throw is read against
a control run on the same driver with `coordinate` in place of `throw`. That control's first move is
byte-identical to the throw's first move, `m0`. [PC_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/PC_QUEUE.md) P5 reads all four
move-16 states.

At `m0`, the slope along `m0`'s own move is positive: `G` at `m0` pairs positively with
`E_c0 − E_m0`, at squared cosine `[354, 355)`. So `m0` already lies past the floor of its line. That is
the crossing jump, not a misoriented momentum. The derivations thread's floor law, which coasts
`min(1, τ*)` with `τ* = −s/κ_c` from the secant curvature, is on #240.

**The exposure gate is read after the opening deposit.** By #244, `R = 0` at every U6 state is the
opening value, the first deposit moves `R` alone, and `C` and `E` learn from the second deposit on.
`executed expose` deposits once per window. Its held-out passages come after every training passage,
so their 1024 held-out station cells are read after 19810 to 21844 deposits from each state (§12), and the gate is not decided by the features'
Gram at the first deposit.

## 9. The wall at m7, the run that crosses it, and the paired held-out reads

The receipts are in this record's receipts directory under `s9/`, copied from `claude/pc-receipts`
(the PC, `51e5792c` and after) and `claude/cloud-runs-2-5aw27d` (runner 2, `9c560e9`). Every code
length is in nats over `/4096` cells, quoted by its lower end where a difference is taken. The
development batch is 8 order-2 requests at seed `2026093061` on the arm lock-dec. The held-out batch
is 128 requests at seed `2026093012`, 1024 station cells. σ over 64 decisions is
`[11356, 11357)/4096`.

**The wall (P3; `p3_m6_spectrum.txt`, `p3_m7_spectrum.txt`).** Along the Kinetic direction from m7,
over `η ∈ [0, 1/2048]` on the lattice unit `2^(−21)`, the held sheet falls from the incumbent
`[337896, 337901)` by `22` or `23` per `η` step of `1/32768`. The released comparison
equals it up to two decision changes, both in request 3:
- at cut `765968 → 765969` (`η 1801125/2^32 → 900563/2^31`), stations 2 and 5 lock together,
  `[[0],[2],[4],[5],[6],[7],[3],[1]] → [[0],[2,5],[7],[6],[4],[3],[1]]`, at `J = 0`;
- at cut `778015 → 778016` (`η 228683/2^29 → 914733/2^31`), the pair reverses, station 2 falling
  below 3, at `J = 34037`. The held sheet there is `[337582, 337587)` and the release above it is
  `[371619, 371624)`.

So the co-lock is free for `12047` cuts and the reversal is then paid at once. From m6 over
`[1/2048, 1/1024]` the same pair co-locks at cut `1675548` (`η 7799875/2^33`) and reverses at cut
`1687863` (`η 1964289/2^31`), at `J = 34040`, with the held sheet at `[337582, 337587)` again. The
wall lies between `1/4096` and `1/2048` from m7 and between `1/2048` and `1/1024` from m6. That is why
m7 stopped: every trial from `1/2048` up pays `J`. Every bisection read on either side agrees with its cut index: a read at cut `778016` or above releases at the jumped value, and one at `778015` or below at the held sheet.

**Below the wall (Q12; `q12/`).** Its claim was fixed before the run: a Kinetic step from m7 at
`η 1/4096` releases at the held sheet, strictly inside `[337582, 337901)`. It does.
- The step-state reads held sheet = released = `[337715, 337720)`, lowering `L` by a margin in
  `(176, 186)`.
- `executed locks` on the stepped state reads `ρ 102837/131072`, solved 1 of 64, whole 0, released
  7, stations right 13. Those are m7's stations: the step at cut `445930` stays below the co-lock.
- Its smallest margin is `49152/2^24`, at request 7, refinement 6, station 4.
- The direction read from m7 at `η 1/1048576` gives `γ_ρ ∈ [584710, 584711)/4096`, the same value
  as Q3's first opening, and `Δρ ∈ [−3018, −3017)/2^21`.

So below the wall the Kinetic step lowers the comparison without changing a decision.

**The run of moves crosses it (Q3; `q3_run.txt`).** This is the Kinetic driver from m7 under #236's
run (cap 32), opening `[337896, 337901)`, solved 1, stations right 13. Each move adopts its first
trial:

| move | η | released | solved | stations right | wall (ms) |
|---|---|---|---|---|---|
| 0 | 1/16 | `[378440, 378445)` | 2 | 18 | 493539 |
| 1 | 1/32 | `[332893, 332898)` | 0 | 19 | 857217 |
| 2 | 1/16 | `[324907, 324912)` | 0 | 22 | 1433622 |

The cloud ran the same move 0 under cap 1 (`cdc9725`, `1068191` ms) with the same readings: a
duplicate measurement (noted October 3). Move 0 releases above the opening, past the wall, and
strict descent would refuse it. The run closes
at move 3, since `324907 < 337896 − 11357 = 326539`. The closing state is m7-3.

**From r13 (Q5; `q5_run.txt`).** The Kinetic driver at `ρ 168127/262144` under the same run, opening
`[269593, 269597)`, solved 15, stations right 17. Moves at `η 1/8, 1/8, 1/4, 1/8`, all first
trials, release `295903, 269925, 259601, 224839`, with stations right `15, 15, 23, 20`. The run closes
at move 4, since `224839 < 269593 − 11357 = 258236`. The closing state is m13-4. Wall `1056768` ms.

**The joined chain (Q4; `q4_chain.txt`).** The joined `(E, ρ)` driver from w3 under #202's interval,
16 moves. Its runs close at moves 1, 2, 6, 9 and 11, and moves 12 to 16 stay open at the limit, so the
chain restores the held state q411:
- `ρ 802987/1048576`, released `[192495, 192499)`, held sheet `[187575, 187579)`;
- solved 37, whole 1, stations right 26.

The Kinetic window chain at the same count is w14 (w3 + 11 moves = m6 + 14): it releases
`[222169, 222173)` at `ρ0`, solved 28 (`lock_reads.txt`), so the joined chain ends `29674` lower.
[Corrected October 3: this first compared w16, two moves further, at `195744`, `3249` above q411.]
Its `γ_ρ` changes sign from move to move.

**Held out.** Each state is read with `executed evaluate`, which deposits nothing, and each pair is
compared request by request (`paired/paired.py`, which now prints both units). The eight stations of a
request are not independent: their targets follow from the request's last two cells
(`x_t = x_(t−2) + 1 (mod 4)`, `hnn_prediction.rs:263-279`), and their classes come from one joint
release. The 128 requests are independent draws read from the same stored states, so they are the
units. For each request, `d` is the first state's stations right minus the second's; `b` counts
requests with `d > 0`, `c` those with `d < 0`, ties are dropped, and the tail is
`P[X ≥ b | X ~ Bin(b + c, 1/2)]`, exact. Station counts are kept as description and enter no tail.
[Corrected October 3, after Astra's review: this first paired the 1024 stations as independent
trials.]

The held-out seed `2026093012` is not a fresh blind read. It is the development validation batch,
consulted for many states and pairs (§9 to §12) before and after these rules were fixed; a grade on
it is a validation grade.

| state | stations right | by station | whole |
|---|---|---|---|
| w16 | 329 | | 0 |
| r13 | 272 | | 0 |
| m7 | 231 | `[25, 25, 27, 24, 19, 28, 38, 45]` (127 released, 1 held) | 0 |
| m7-3 | 279 | `[30, 32, 37, 38, 22, 35, 40, 45]` | 0 |
| m13-4 | 291 | `[34, 39, 47, 52, 23, 10, 28, 58]` | 0 |
| q411 | 345 | | 1 |

| pair (first vs second) | station b / c (described) | request + / − / ties | request tail |
|---|---|---|---|
| m7-3 vs m7 | 128 / 80 | 50 / 22 / 56 | `[678, 679)/2^20` |
| w16 vs r13 | 226 / 169 | 58 / 39 / 31 | `[137, 138)/4096` |
| m13-4 vs r13 | 165 / 146 | 36 / 32 / 60 | `[1466, 1467)/4096` |
| q411 vs w16 | 199 / 183 | 53 / 49 / 26 | `[1570, 1571)/4096` |
| m13-4 vs w16 | 184 / 222 | 47 / 56 / 25 | `[3431, 3432)/4096` |
| m7-3 vs w16 | 154 / 204 | 43 / 56 / 29 | `[3770, 3771)/4096` |

Each station `b − c` equals the difference in stations right. Per station, w16 against r13 read
`[9, 10)/4096`; per request it is above `1/64` and does not separate. It was never declared, and no
release rests on it. The pairs against w16 are not like for like.
w16 is 16 Kinetic moves under #202's interval, while m7-3 is 7 Coordinate moves and 3 Kinetic moves,
and q411 is a joined chain.

**#236 is released.** The rule was fixed before the reads: #236's acceptance is released at a paired
tail of at most `1/64` on a closed run against its opening state, `1/128` for the two reads made.
As first stated it paired stations; read per request, as above:
- m13-4 against r13: 36 ahead, 32 behind, 60 tied, tail `[1466, 1467)/4096`; it does not separate;
- m7-3 against m7: 50 ahead, 22 behind, 56 tied, tail `[678, 679)/2^20`, below `1/128 = 8192/2^20`.

The release holds for both reads together, at request level as it did per station
(`[560, 561)/2^20`). m7-3 has 48 more stations right than m7 (279 against 231) on the same batch;
that is a description, not a second test. It shows that crossing m7's wall with a run of moves
carries held-out stations that strict descent left behind. It does not show that Coordinate beats
Kinetic: m7-3 is below w16.
The same question on a second wall, the at-rest throw's at m9 (below), is queued as Q13 against the
bound `1/128`.

**The at-rest throw meets a wall at m9.** The at-rest arm releases from rest at every move under
strict descent at `ρ0`:
- m6 `385082 → 375945`, solved 2, stations 18;
- m7 `→ 364068`, solved 5, stations 19;
- m8 `→ 352438`, solved 4, stations 17.

At m9 the ladder starts at `η 8` (FirstOrderZero) and every trial down to `1/16` is refused:
- `η 8` and `4` are refused NotBelow, with masks `408679, 368605`;
- `η 2, 1, 1/2, 1/4` are refused OwnNotBelow: the held sheets `347714, 345518, 348089, 349957` fall
  below `352438`, while the releases `370563, 356745, 354258, 361265` rise above it;
- `1/8` and `1/16` are refused the same way.

That is the m7 picture again, a held sheet that falls while the released comparison jumps. m8 is the
arm's end under its law, and P5 pairs the other throw arms against it at m8.

**Two chains stopped past a fitted per-move bound.** Both the whole-move throw's m2 and the
strict-descent Coordinate control's m7 ran past `1349692` ms, which is `253092 + 8·137075`. That
bound came from a two-point fit to the development moves m0 (`527242` ms, 2 rereads) and m1
(`390167` ms, 1 reread), not from measured upper times.
- The whole-move m2's rereads took `151812` and `203871` ms.
- The Coordinate control's moves grew from `533372` to `923456` ms as refused trials accumulated:
  one at m4, two at m6.

Each is recorded as stopped incomplete, and as a projection error. Neither is relaunched with a
larger move bound. Each runs again from its last state as a new launch, with the run's read declared
per unit:
- each kind of unit (incumbent read, persistence, slope, each trial's reread) prints a line;
- each kind is bounded by the largest time measured for it before launch;
- the run stops early when a unit passes its kind's bound.

The move's bound is the sum over one move at the law's depth: the non-reread units once each, plus
one reread per trial the ladder can attempt. On the chains' build (`5f254c2d` with the print picks),
`LADDER_DEPTH = 8` bounds the trials. #236, merged as #264, retires that depth: its halvings end at the
lattice, so a launch from main bounds a move at `log₂(1/λ) + 1` trials (`attempted_halvings_le_lattice`),
with `λ` the source port's lattice unit. Either way the bound is an upper time, which the fitted one
was not. A unit past its bound after launch ends the chain incomplete, and its cost becomes the next
subject. §10 sets the per-kind factor.

## 10. Where the throw's crossing comes from, the chains' end states, and the receiving prior's scale

The receipts are under `s10/`, copied from `claude/pc-receipts` (`92f1fea1`, `6f2e4b5d` and the
`throw-rest` runs). Units and batches are as in §9.

**The per-kind bound is three times the measured maximum.** §9 bounded each kind of unit by its
largest measured time. A sample maximum is not an upper time: if a kind's times on one host are
exchangeable, the next sample passes the largest of `n` with chance `1/(n+1)`, so a chain held to it
stops on the host's variance, and the stop says nothing about the move. Each kind is therefore bounded
by `3` times its largest time measured on the same host before launch. [agent-inferred] The factor is
the queues' own for P2 and P5 in [PC_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/PC_QUEUE.md) and the Q2 chains' `1900` s in
[CLOUD_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/CLOUD_QUEUE.md). [Corrected October 3: not every deadline was; P3's `7200` s
had no projection, and P4's `36000` s was `4000000/3571621` of one (§12).] A unit past it is a change of regime, not variance. It ends the chain
incomplete, the factor is never raised, and its cost becomes the next subject. Bounds are fixed at
launch, from that host's own measurements; one host's maxima are never applied to another.

**The whole-move throw's m2 completes in seven trials** (runner 4's diagnostic on `5f254c2d` with
`7a650e6b`). `η 4, 2, 1, 1/2, 1/4, 1/8` are each refused at the reread (OwnNotBelow), none at first
order, with own releases `428005, 407581, 427086, 425188, 422867, 419588`, all above the incumbent's
`[404256, 404261)`. `η 1/16` is adopted, and the coast is carried again: power on the whole move
`[−169069, −169064)`, impulse step 4. The adopted m2 reads `[401729, 401735)`, `X [220459, 220464)`,
solved 1, stations right 15, at `ρ0`. The move took about `1551030` ms against the fitted `1349692`. It
was reread-bound, at seven reread gaps of `155229` to `209825` ms. The relaunch from m1 runs under
`3·(166264 + 1814 + 32691) + 3·8·209825 = 5638107` ms a move.

**The crossing at m9 comes from the point, not the momentum.**
- *Like for like at m8.* Coast-alone m8 reads `[351324, 351329)`, solved 1, stations right 16. At-rest
  m8 reads `352438`, solved 4, stations right 17. Held out, coast-alone m8 has 258 stations right
  (`[25, 26, 31, 31, 39, 34, 30, 42]`) and at-rest m8 has 282 (`[19, 27, 38, 30, 35, 29, 51, 53]`).
  Paired per station, `b = 94`, `c = 118`; per request (§9's corrected unit), coast-alone is ahead on
  32, behind on 47, tied on 49. Coast-alone ahead has request tail `[3950, 3951)/4096`, and at-rest
  ahead has `[234, 235)/4096` (per station `[3920, 3921)` and `[233, 234)/4096`), so neither is
  released. The development batch's lower coast-alone read does
  not carry to held out.
- *The direct read.* Coast-alone's m9 moved, while at-rest's m9 refused every step (`rest-m9/`). These are two
  different points, so the at-rest driver was run with no flight from coast-alone's m8
  (`rest-from-coast-m8/`). It refuses `η 8` (NotBelow) and `η 4, 2, 1, 1/2` (OwnNotBelow), and adopts
  `η 1/4`. The result is `L 348717`, `X 167601`, solved 1, stations right 16 at `ρ0`, which is
  coast-alone's own m9, released there from rest. [Noted October 3: coast-alone's m9 listing
(`78d922d6`, 23:44:33 UTC) had already shown this release from rest, 21 min before this run, so the
run duplicates it; §11 confirms the two states are byte-identical.]

So from coast-alone's m8 the move needs no momentum, and from at-rest's m8 no step descends. The
difference between the arms at m9 is in their m8 states, not in a carried coast.

**The #202 chains' end states.**
- *Q2's Coordinate chain (runner 1).* The run opened at move 14 was still open at 16, so the chain
  restored its held state q213: `[329485, 329490)`, `X [152529, 152534)`, solved 4, stations right 19,
  `ρ 1636353/2097152`. The open run's move 16 reached `[321272, 321277)` with 23 stations, `8213` below
  the held state, which is less than σ.
- *Q2's Kinetic control (runner 2).* Move 14 closed a four-move run, and the run opened at 15 was still
  open at 16, so the chain restored q2k14: `[248321, 248325)`, `X [85225, 85228)`, solved 24, stations
  right 21, `ρ` unmoved at `102837/131072`. Move 16 (`[243009, 243014)`) is not below `248321 − 11356`.
- *The strict-descent Coordinate control.* It is not relaunched (usage, October 3). P5 reads it at m6
  and pairs it with at-rest m6.

**The receiving prior at `2I` (#259's measurement (b)).** Campaign 1's development control at
`n* = 6148` cells, host reference, compares #259 at `c3e6d21` against its merge base `3515ed4a`. The
held-out cells are `4958..6148`, 1190 targets.

| | `H₀ = I` | `H₀ = 2I` |
|---|---|---|
| held out, model q | `3354 + 13/16 + ε` | `3351 + 0/16 + ε` |
| training, model q | `17437 + 13/16 + ε` | `17430 + 4/16 + ε` |
| PPM order 2, held out | `3913 + 13/16 + ε` | the same |
| wall | `750904` ms (shared load) | `673146` ms (beside P4's two sources) |
| peak resident | `292622336` bytes | `295591936` bytes |

`L(I) − U(2I) = 149301954884965437216731043645/2^95` bits, in `[3 + 12/16, 3 + 13/16)`. The gate fixed
before the run asked for `1190/16 = 74 + 6/16` bits either way, so the read is undecided at the grain.
By the rule fixed with the gate, `2I` stays the scale that the prequential certificate derives, and
#259 merges with this read beside it. The measurement does not contradict it: `2I` codes lower on held
out and on training. The card's parity is gate 3, 32 of 32 on a clean build. The first `2I` attempt ran
beside four other runs and stopped incomplete at its `800` s deadline. It was not relaunched under that
deadline; the second read is a new launch, without the other #259 arm but beside P4's two sources
(corrected October 3: it was first labelled "alone"), projected from its own 200-window read
(`33807` ms) at three times. The two failures in gate 3 that came before it were stale kernels from a copied target
directory, not a fault on main (#262 makes the build script rebuild on a change of the kernel sources'
content).

## 11. The arms' end states held out: no declared pair separates

The receipts are under `s11/`, copied from `claude/pc-receipts` (`5fb7e96b`). The run is P5 of
[PC_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/PC_QUEUE.md): held out, order 2, seed `2026093012`, 128 requests, one
`evaluate` call at 16 threads, with coast-alone m9 read in a second call. `p5.sections` is split into
one file per state; the six files concatenate back to it byte for byte. Stations are counted of 1024
(8 per request); "first lock right" counts requests whose first lock is right.

| state | ρ | stations right | by station | first lock right |
|---|---|---|---|---|
| whole-move m2 | `102837/131072` | 238 | `[18, 15, 37, 29, 32, 33, 30, 44]` | 25 |
| at-rest m2 | `102837/131072` | 257 | `[25, 28, 32, 32, 38, 34, 32, 36]` | 35 |
| strict-descent Coordinate control m6 | `204001/262144` | 268 | `[26, 24, 41, 40, 30, 14, 46, 47]` | 48 |
| at-rest m6 | `102837/131072` | 268 | `[21, 29, 41, 46, 22, 19, 44, 46]` | 49 |
| Q2 Coordinate, q213 | `1636353/2097152` | 278 | `[25, 32, 38, 34, 29, 25, 54, 41]` | 57 |
| Q2 Kinetic control, q2k14 | `102837/131072` | 311 | `[43, 52, 36, 45, 32, 24, 37, 42]` | 40 |
| coast-alone m9 | `102837/131072` | 261 | `[25, 26, 31, 33, 40, 33, 33, 40]` | 33 |

No state makes a section whole: 0 of 128 each, every release incorrect. q2k14 reaches the termination
on one request; no other state does.

**The declared pairs** (paired rule of §9, per request, released at a tail of at most `1/64`):
- *Whole-move m2 against at-rest m2.* Per station `b = 172`, `c = 191`; per request 32 ahead, 46
  behind, 50 tied. Whole-move ahead has request tail `[3914, 3915)/4096` and at-rest ahead
  `[287, 288)/4096` (per station `[3494, 3495)` and `[706, 707)/4096`), so neither is released.
- *The strict-descent Coordinate control against at-rest m6.* Per station `b = 92`, `c = 92`, an exact
  tie in stations right with 184 discordant stations; per request 34 ahead, 33 behind, 61 tied,
  tail exactly `1/2` (per station `[2168, 2169)/4096`).

With §10's m8 pair, the throw's carried momentum is now read held out at m2 and m8, and neither
separates from the at-rest throw. Moving ρ under strict descent (the control) does not separate from
holding it at m6.

**Coast-alone m9 is the at-rest point.** Its state (sha256 `8712ae47…6dab0a5c`) is byte-identical to
the at-rest move from coast-alone's m8 (§10, `rest-from-coast-m8`), so its held-out read (261) belongs
to that state, not to a carried coast. It is read unpaired; the throw's pair stays at m8.

**The #202 chains.** q2k14 has the most stations right of the states in this call (311). It is the same
batch as §9's reads, where w16 has 329; w16 is not an end state of these arms and is not paired here. Against q213, the other Q2 end, it is
an undeclared pair: per station `b = 230`, `c = 197`; per request 55 ahead, 44 behind, 29 tied,
Kinetic-control ahead with request tail `[644, 645)/4096` (per station `[248, 249)/4096`, and
Coordinate ahead `[3891, 3892)/4096`). It is not released, and as an undeclared read it does not count
toward any release.

**Time.** The six-state call took `3095851` ms against its fixed deadline of `19492308` ms
(measured to projected `281441/1772028`, below `3/16`), with a peak resident set of `103690240`
bytes. The per-state reads ran from `501719` to `533346` ms, below the `1082906` ms that set the
projection. Coast-alone m9's call took `519226` ms, peak `85889024` bytes.

## 12. The exposure gate at m6 and w16 is not read: both runs passed their deadline

The receipts are under `s12/`, copied from `claude/pc-receipts` (`697a89ed`). This is P4 of
[PC_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/PC_QUEUE.md), the gate §7 restates: from m6 and from w16, everything else equal,
`executed expose 2026093061 2026093012 128 all`, at 2 threads per source, both sources at once on the
PC, under `timeout 36000`.

**Both stopped incomplete.** Each exited 124 at `36000053` ms. Each output is the header line and the
exit line: a cut of 65536 cells, 1238 training passages from seed `2026093061` (the first entered
after 32 cells), 128 held-out passages from seed `2026093012`, 1024 station cells held out, windows
all. The error files are empty. No code was printed, so w16's held-out code against m6's (the gate,
64 bits) is not read, and §7's question is open. It is not relaunched with a larger deadline.

**Why it failed** (corrected October 3 from an audit of the U6 runs; each item below was checked
against the code and the receipts named). P4 could not have changed a decision, and its deadline
could not have held.
- *No decision waited on it.* Its only consequence was that on failure the bank chain stops (§6, §7).
  P5 was queued 17 s after P4 (`f195474` after `d0af941`) to read the end states of those same chains,
  and Q2, Q4 and the throw arms kept running moves throughout. The last chain ended at 01:55 UTC
  (`4743e836`) and §11 closed at 02:26:59 UTC (`6bd97eb`), while P4's projected finish was about
  08:05 UTC. It was not stopped when its purpose lapsed. It ran `24163` s past §11, to 09:09:42 UTC.
- *The deadline had no headroom.* `36000000/32144589 = 4000000/3571621` over a point projection. The
  queues' rule at launch was three times a measured time (CLOUD_QUEUE's common setup; P2 and P5 in
  PC_QUEUE), so the deadline should have been at least `96433767` ms.
- *The projection was a linear extrapolation from another host's sample.* It took a 200-window read
  at m6 in the cloud (`294297` ms; user time 425 s over a real time of 294 s; peak `665231360` bytes,
  none of which has a receipt on any branch) and multiplied by `21845/200 = 4369/40`. The rule
  CLAUDE.md states asks for a development read on the launch host and the largest time per unit,
  and a 200-window total has no per-unit maximum. The PC copy was a fallback for the cloud copy,
  which a container restart had stopped, and it inherited the cloud's projection.
- *The same host showed the time per window growing, an hour into the run.* Campaign 1's exposure on
  the PC took `33756` ms for its first 200 windows and `672249` ms for its whole 3074-window cut
  (`claude/pc-receipts` `6f2e4b5d`, `c1_259/c1-host-2I-window200.txt` and `c1-host-2I-solo.txt`).
  Per window that is a factor of `193175/149089`. Applied to P4's projection it gives
  `49676249115555/1192712` ms, already past `36000000`, and P4's cut is `4369/40` times its sample
  against campaign 1's `1537/100`. It was not acted on.
- *The measured part was reachable only by finishing, with no progress line.* The held-out passages
  are the cut's last 6144 cells (from cell 59392, window 19797 of 21845; `expose_read`,
  `hnn_executed_loop.rs`), and the mask holds only their 1024 station cells, the first at cell 59432
  (window 19810). `expose_read` prints nothing between its header and its result and keeps
  no state, so the run could not stop early on evidence. Progress lines were added to executed moves
  at 23:14 UTC (`7a650e6b`), five minutes after P4's PC launch, and not to `expose`.
- *A null result could not be read.* `expose_from` deposits every compared window, held-out windows
  included (`reference.rs:3999-4000`), and the deposits reach the source port `E`. So 19810
  windows of the protocol's own learning into `E` stand between m6's or w16's `E` and the first
  held-out station cell. A pass would have shown that w16's `E` survives them. A null could equally mean the
  protocol overwrote it, so it would not have shown that the U6 gains miss the receiving path, and
  the gate's failure branch did not follow from its failure.
- *The cloud copy.* It was relaunched at 23:07 UTC under the same deadline in a session whose
  background runs end at 2 h, below the about `29/32` of the projection needed to reach the first
  held-out station cell. It left no end receipt.

**What was claimed beyond the receipts** (this section as first merged).
- The look at the PC at 05:14 UTC (each source at `6106/6000` of one core with 2 rayon workers) was
  reported to the main line, not receipted: `s12/` holds only the header and exit lines and two empty
  error files.
- "The only parallel work in `expose_with` is two `rayon::join` points" is false. Each window's
  deposit (`resident.constitution.deposited`, `reference.rs:1424`) runs `Constitution::deposited`,
  whose loci run under `par_iter_mut` and `into_par_iter` (`constitution.rs:5431`, `:5512`), and the
  solved chart's rows run under `into_par_iter` (`constitution.rs:1394`, `:1438`, `:1464`, `:1487`).
  The conclusion that the thread count was not the cause rests only on the unreceipted look.

**The direction P4 asked about is already read held out, through `evaluate`** (undeclared; it counts
toward no release). Pairing the existing sections of P4's own m6 (sha256 `9da99d84…`, 235 stations
right, §9's table) and w16 (sha256 `35ca209c…`, 329) with §9's `paired.py`
(`claude/pc-receipts` `paired/m6.sections` and `paired/w16.sections`, copied into `s12/`) gives
per station `b = 215`, `c = 121`, a tail for w16 ahead in `[177/2^30, 178/2^30)`; per request (§9's
corrected unit) 65 ahead, 33 behind, 30 tied, tail `[839, 840)/2^20`. This is the `evaluate` read,
not the exposure's code, so §7's gate as stated stays unread. It shows that the 16 window moves from
m6 raise held-out stations right on the same batch, which P4's direction question needed. The "m6" of
§11's control pair is a different state.

**What a decisive exposure read would need** (stated, not launched). The cheapest form reorders the
cut instead of shortening it.
- *Held-out passages first.* `Cut` takes held-out ranges at any position, and `closing_crib` already
  keeps every crib off them (`reference.rs:2613-2635`). With the 128 held-out passages first and the
  training passages after, the cut is still exactly the declared population of `2^16` cells, so no
  new field declaration is needed. The change is to `expose_read` only.
- *A window deadline.* The receiving windows are `[3k, 3k + 3)` from cell 0 (`receiving_windows`),
  and a passage is 48 cells, so the held-out passages are exactly the first 2048 windows.
  `with_deadline(2048)` stops after 2048 compared windows (`reference.rs:3910`), and the held-out
  code is summed window by window (`reference.rs:3987-3996`), so the stopped run prints the code of
  all 1024 held-out station cells. That is `2048/21845` of the cut, from its cheapest part.
- *What it measures.* Held-out passage `k` opens after `16(k − 1)` deposits. Only its 8 stations are
  held out (`expose_read`): its 40-cell request is coded and deposited like training, so its first
  station cell, in window `16(k − 1) + 13`, is coded after `16(k − 1) + 13` deposits. That is 13 for
  the first, against 19810 in P4 (its first station cell is 59432). The protocol still deposits every
  complete window, the held-out windows included, so the read is not free of the instrument's own
  learning. It is far closer to the stored `E` than P4's layout.
- *Before any launch.* It needs a progress line from `expose_with`, a development read of its first
  windows on the launch host, and a decision it can change. None exists now: the U6 chains have
  ended (§10), and the arms' end states do not separate held out (§11). It stays owed and is not
  queued.

**Other duplicates and an out-of-rule launch in the same period** (noted October 3).
- The whole-move throw's m0 is byte-identical to coast-alone's m0 (sha256 `4c514ff0…` on both
  branches), and its m2 ran twice, once as the diagnostic and once as the relaunch (state `8d3f54c5…`
  in both; the second was declared as a reproduction).
- Coast-alone's m10 was launched at 23:45:24 UTC (`4743e836`, `m10/stamps.txt`) under the fitted
  per-move bound `1349692` ms that §9 had recorded as a projection error at 23:36:36 UTC (`6fc18d6`).
  It timed out in its eighth trial, and its driver read the timeout as a refusal and ran m11 to m13
  outside the chain's rule. Those three are measurements outside the rule, not chain moves.

The pre-launch conditions these failures call for are at the top of
[PC_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/PC_QUEUE.md) and [CLOUD_QUEUE](https://github.com/brandonrdug/holonics/blob/9078f103/research/runs/u6/CLOUD_QUEUE.md).
