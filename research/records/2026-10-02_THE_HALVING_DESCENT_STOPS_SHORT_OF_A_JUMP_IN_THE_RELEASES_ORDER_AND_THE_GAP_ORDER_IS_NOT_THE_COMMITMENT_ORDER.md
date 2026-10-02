# The halving descent stops short of a jump in the release's order, and the gap order is not the commitment order

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for §2's theorems (`HolonicsResearch/HNN/OrderTemperature`, "A jump in the release's
order"); [measured] for §3, an exterior read-only diagnostic at the founded opening, and for §5, the main
line's read of its chain.

**Occasion.** The main line measured that `ρ` alone does not limit `E`'s descent. Held at the
8-request fit's value, the native chain from the opening descends no faster than the `ρ₀` chain: 13
accepted moves reach `269593/4096` against `265678/4096`. Its runs closed at moves 1, 2, 3, 4, 12 and
13, and moves 5 to 12 made one 8-move run that closed only on its last allowed move. The coordinator
steered this thread to the jumps in the release's order and the commitment order. The
[turn-clock record](2026-10-02_THE_COMMITMENT_IS_READ_ON_THE_TURN_CLOCK_ITS_ORDER_IS_RESOLVED_TO_ONE_TURN_AND_A_CROSSING_JUMPS_ONLY_AT_A_WHOLE_TURN.md)
(#225) derived the commitment order on the turn clock. The
[flip record](https://github.com/brandonrdug/holonics/blob/a7d404ea/research/records/2026-10-02_A_FLIP_IS_SET_BY_THE_LOCK_RULES_MARGIN_AND_NO_LAW_IN_THE_CHAIN_CERTIFIES_IT_BEFORE_THE_SUCCESSOR_IS_READ.md)
names a crossing a jump in code length, not a wall or an energy, until the map from code length to
the Holons' storage and work is derived (#62); this record keeps that wording.

**Answer.**
1. **A halving descent stops short of a jump it cannot cross** (§2). Along a move's direction, let
   the release's order change at a step length `w`, where the code length jumps up by more than the
   move's conditions admit. The move's trials halve from `η₀`. The first trial short of the jump
   lands within half of it, so where that trial is adopted the jump's distance halves move by move,
   and what a move can still gain shrinks with it. Once the jump lies closer than the move's
   smallest trial, every trial crosses it and the move is refused. The run therefore closes short of
   the jump, with the continuous slope still negative, a second stopping kind beside #195's.
2. **The gap order is not the commitment order** (§3, measured). At the founded opening on the 8
   development requests, 61 refinements have an eligible station. In 17 of them, `LockOrder::Gap`
   locks a station whose whole-turn commitment turn is strictly later than another eligible
   station's; in 32 it locks the whole-turn law's first set; in 7 it locks part of that set; and in
   5 the enclosures leave the answer open. The 17 are not near ties. The gap order ranks by an
   absolute difference of growths, so a station with large growth and a small ratio locks first.
   The lock face reads ratios.
3. So the jumps the chain meets under the gap order sit where two stations' gaps tie, and the lock
   face marks no change there.
4. **The jumps do not stop the chain's runs** (§5, the main line's read). Every move of the
   diagnostic chain adopted its first or second trial, so no step size fell geometrically toward a
   jump. Only `m7` closed on a jump, and in §2's last case: the jump lay at `731/840` of the smallest
   of the eight trials, so every trial crossed it and the move's depth (`LADDER_DEPTH`), not the
   lattice floor, ended the halvings. The native chain's shortfall against the float fit is
   therefore not a run of closures at jumps; it lies in the native move's direction or reach, which
   the next derivation takes.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the helix**
(a commitment turn is a winding count) and **faces and placement** (the order in which committed data
are placed beside later stations). The pair, the cell holonomy, the tube and the tower thread stay
attached: no contact, restriction or transport changes.

## 0. The recorded failures this could repeat

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **A refusal answered with a larger limit.** Nothing here lengthens a run, adds trials or loosens a
  condition. §2 says more moves would not carry a run past such a jump, since each gains less.
- **Bits read as progress.** No code length is offered as progress. §3 counts decisions of the
  release's order, at the opening, with no training.
- **A located cause carried unrepaired.** The located cause is the release's order, and its owner is
  `hnn::prediction`. This record changes no owner; the release law stays proposed (#225 §7).
- **Text run on its codec's grain.** The read is on the order-2 terrain. The order, the turns and
  the grain are the receiving bank's, the same for every chart.

## 1. The question, fixed before the read

[fixed before the 8-request read; the 1-request development read had been seen] Does the release's
gap order follow the commitment order of the turn clock? If it did, then wherever the enclosures
decide, every refinement's gap lock would lie in the whole-turn law's first set (the eligible
stations of least commitment turn). A refinement whose gap lock commits strictly later refutes that.
The read is a characterization and has no acceptance count.

## 2. What a halving descent does at a jump

[proved-derived; formal-checked] The move's law (`hnn::executed`, module header and the halving
trials): from a first step `η₀`, the step is halved and tried again, at most `LADDER_DEPTH = 8` trials
a move, and no trial below the lattice floor (`η · 2u < λ`, `u` the largest unit move, `λ` the
lattice unit). A trial is adopted when every condition holds on it, among them the fixed mask's
composition strictly lower by disjoint enclosures and the successor's own released code length within
the release excursion. Along one move's direction, let the comparison be its continuous part `g`
short of a step length `w`, and jump up at `w` by more than the excursion admits. Every trial at or
past `w` is refused.
- **The first halving short of the jump lands within half of it** (`first_halving_short_of_jump`).
  With `η₀ ≥ w`, the first `η₀/2^k < w` satisfies `η₀/2^k ≥ w/2`: the trial before it was at or
  past the jump.
- **Where that trial is adopted, the jump's distance halves** (`jump_distance_halves`). After the
  move, the jump lies at most `w/2` ahead. If the next move's direction meets the same jump, then
  after `n` such moves it lies within `w/2^n` (`jump_distance_le`).
- **What a move can still gain shrinks with it** (`gain_short_of_jump`). With `g` falling at most
  `G` per unit step, a move that stays short of a jump at distance `d` lowers `g` by at most `G d`.
  So the decrease may stop being resolved by disjoint enclosures before the jump is reached.
- **Closer than the smallest trial, every trial crosses** (`trials_cross_jump`). Once `w` lies
  below the last trial `η₀/2^7` (or every trial above the floor), each trial reads the jump and the
  move is refused. This is the case the Lean thread's run-length law cites: a jump present at every
  small step is refused at every count (`jump_refuses_every_halving`).

So a chain whose direction keeps meeting such a jump approaches it with geometrically falling
gains. Its run closes short of the jump: either when the jump lies closer than the smallest trial,
or when a gain no longer resolves. Either way the continuous slope is still negative there. #195
proves that every candidate move is a gradient step under some metric and stops only where the
gradient vanishes; that holds for each continuous part. A comparison whose order changes has jumps
between the parts, and a jump closes a run too.

**Its signature in a chain's receipts.** Toward a jump, the adopted step size falls move by move
(each at most half of the previous distance). The closing refusal splits, at its smallest trial, into
a held decrease below the flip. `m6` adopted at `1/2048` with no flip, and `m7` was refused at every
step size from `1/16` to `1/2048` by a flip of `34038/4096`, fixed in size from `1/64` down
([the refit's ingredients](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
§4). That is this signature at one jump.

## 3. The gap order beside the commitment order, at the founded opening

[measured; read-only] `executed instants` (`research/notebook/hnn_design/hnn_executed_loop.rs`) runs
each request's release under its own law, `LockOrder::Gap`, and keeps the refinements. At each
refinement, every eligible station's commitment turn is read from its candidates' joint growths. The
turn is the least whole `n` with `(1 + R(n))^16 ≤ 2`, `R(n) = a_top^(−n) + Σ_y (a_y/a_top)^n`
(`commit_turn_iff`). It is enclosed from the readings' two ends, with each power carried by squaring
and every product rounded outward on `2^(−64)ℤ`, so the enclosure is sound.

Order-2 terrain, development seed `2026093061`, 8 requests, the founded opening:

| Refinements with an eligible station | 61 |
|---|---|
| The gap lock is the whole-turn law's first set | 32 |
| The gap lock is a strict part of it (the law would lock more together) | 7 |
| The gap lock commits strictly later than another eligible station | 17 |
| Undecided (an enclosure leaves a turn open) | 5 |
| Single-station gap locks | 61 |

- **The 17 are not near ties.** Some of them (gap and turn of the locked station against the
  earliest station):

  | Request, refinement | Gap lock | Earliest turn |
  |---|---|---|
  | 0, 0 | station 7: gap `45268/4096`, turn 5 | station 5: gap `21379/4096`, turn 4 |
  | 2, 3 | station 7: gap `20219/4096`, turn 10 | stations 0, 1: gaps `7899/4096`, `8703/4096`, turn 5 |
  | 3, 2 | station 7: gap `9710/4096`, turn 11 | station 2: gap `5633/4096`, turn 6 |
  | 4, 4 | station 4: gap `7352/4096`, turn 11 | station 0: gap `3787/4096`, turn 7 |
  | 6, 1 | station 6: gap `16828/4096`, turn 7 | stations 2, 3: gaps `6097/4096`, `9144/4096`, turn 5 |

  (Each gap is the lower end of a cell `[k/4096, (k+1)/4096)`.) The gap lock has the larger gap by
  the release's law, and in each of the 17 the later turn. The gap is `a_top − a_runner`, a
  difference of growths, and it grows with the scale of the growths. The turn reads the ratio
  `a_runner/a_top` and the threshold term `a_top^(−n)`, and it does not depend on that scale.
- **The commitment turns of the gap locks** run from 2 to 366, most between 3 and 11 (the
  histogram is in the receipt). So the whole-turn law's resolution of one turn is coarse beside an
  instant of 3 turns and fine beside one of 300.
- **Receipt.** Development read, 1 request: `25354` ms, peak resident `54095872` bytes. Projection
  for 8: `8 × 25354 = 202832` ms; deadline `203` s by `timeout`. Measured: `70095` ms
  (`70095/202832` of the projection), peak resident `57376768` bytes, 4 cores, rayon over requests
  and candidates. Receipts: [`2026-10-02_ORDER_JUMPS_receipts/`](2026-10-02_ORDER_JUMPS_receipts/)
  (`opening8.txt`, `dev1.txt`).

## 4. What this changes

- **The gap order is not a proxy for the commitment order.** It is a different order, not a coarse
  or fine version of it. The two disagree in 17 of the 56 refinements the enclosures decide at the
  opening. #225 §7 is corrected to say so.
- **The release's jumps are where gaps tie.** Two stations swap lock order where `a_top − a_runner`
  ties between them. The lock face, which reads shares, has no feature there. A jump of the
  commitment order is where a station's turn changes, which the face does read: it is where the
  top's share over that many turns reaches the grain.
- **The jumps are not what limits the chain.** The native move descends the comparison the release
  executes, and that comparison changes order at gap ties, a feature of the release's ranking that
  the lock face does not read. But the main line's read (§5) finds one move, `m7`, refused at a
  jump, and no approach toward one elsewhere. The gap between the native chain and the float fit
  is not explained by jumps.

**What it does not show.** It does not show that the whole-turn order would let the chain continue
past any closure, nor that it would reach the refit's basin or any held-out decision. The whole-turn
release is not built.

## 5. What the main line read

The read was fixed in advance: for each closed run, the adopted step size of each move before the
closure (a geometric fall toward the closing state is §2's signature), the closing split, and
`executed instants` at the incumbent and the refused successor.

**Measured** (main line, the chain at `ρ` held at the 8-request fit's value, and `m7`; relayed by
the coordinator):
- **The approach.** Every move adopted its first trial except `r5` and `r12`, which adopted their
  second. No step size falls geometrically anywhere, so no run of this chain closes by §2's approach.
- **`m7`.** Its eight trials ran from `1/16` to `1/2048` and all were refused. The jump along its
  direction lies at `731/840` of the smallest trial, so every trial crosses it (`trials_cross_jump`,
  `jump_refuses_every_halving`), and a ninth halving, at `420/840` of the smallest, would land short
  of it. The move's depth ended the halvings; the lattice floor did not.
- **Against the float fit.** The float fit on the same 8 requests, read natively, decides `37/128`
  held-out requests whole and `717/1024` stations right; the native chain at the fit's `ρ` decides
  `0/128` whole and `272/1024`. The gap is the native move's, in its direction or its reach.

The closing split and the `executed instants` read are not needed for the question of §1 and stay
unread.

## 6. Verification

- Lean: `bash tools/lean_check.sh HolonicsResearch.HNN.OrderTemperature` builds with no errors,
  warnings or `sorry` (`first_halving_short_of_jump`, `jump_distance_halves`, `jump_distance_le`,
  `trials_cross_jump`, `gain_short_of_jump`).
- The diagnostic compiles in release with no warnings, and `cargo check --workspace --all-targets`
  passes. It changes no owner and no law.
- Owed (#62): the descent law along a chain whose directions change from move to move (here a
  hypothesis); the commitment turn's enclosure as a theorem on the rounded powers (here argued from
  monotonicity); and the map from code length to storage and work that would let a jump be read as
  an energy (the flip record's obligation).
