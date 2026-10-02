# A zero-temperature descent walks into the release's walls, and the gap order is not the commitment order

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for §2's theorems (`HolonicsResearch/HNN/OrderTemperature`, "Walls"); [measured] for
§3, an exterior read-only diagnostic at the founded opening; [agent-inferred] where marked.

**Occasion.** The main line measured that `ρ` alone does not limit `E`'s descent. Held at the
8-request fit's value, the native chain from the opening descends no faster than the `ρ₀` chain: 13
accepted moves reach `269593/4096` against `265678/4096`. Its runs closed at moves 1, 2, 3, 4, 12 and
13, and moves 5 to 12 made one 8-move run that closed only on its last allowed move. The coordinator
steered this thread to walls and the commitment order. The
[turn-clock record](2026-10-02_THE_COMMITMENT_IS_READ_ON_THE_TURN_CLOCK_ITS_ORDER_IS_RESOLVED_TO_ONE_TURN_AND_A_CROSSING_JUMPS_ONLY_AT_A_WHOLE_TURN.md)
(#225) derived the commitment order on the turn clock and called the release's gap order "that law's
proxy". The [joined move's record](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md)
§4d showed that a move certifies the comparison only at its endpoints.

**Answer.**
1. **A wall stops a halving descent by drawing it in** (§2). A wall is a step length along the
   move's direction where the release's order changes and the comparison jumps up by more than its
   continuous part falls. Halving from a step at or past it, the first trial short of it lands
   within half of it. So the distance to the wall at least halves at every adopted move, and what a
   move can still gain shrinks with it. The chain stops at the wall, not at a point where the
   gradient vanishes. That is a second kind of stopping state beside #195's.
2. **The gap order is not the commitment order** (§3, measured). At the founded opening on the 8
   development requests, 61 refinements have an eligible station. In 17 of them, `LockOrder::Gap`
   locks a station whose whole-turn commitment turn is strictly later than another eligible
   station's; in 32 it locks the whole-turn law's first set; in 7 it locks part of that set; and in
   5 the enclosures leave the answer open. The 17 are not near ties. The gap order ranks by an
   absolute difference of growths, so a station with large growth and a small ratio locks first.
   The lock face reads ratios.
3. So the walls the chain meets under the gap order are where two stations' gaps tie. The lock face
   marks no change there. [agent-inferred] Some of the walls that close the native chain's runs may
   be walls of an order the comparison's own face does not read. §5 names the read that decides it.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the helix**
(a commitment turn is a winding count) and **faces and placement** (the order in which committed data
are placed beside later stations). The pair, the cell holonomy, the tube and the tower thread stay
attached: no contact, restriction or transport changes.

## 0. The recorded failures this could repeat

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **A refusal answered with a larger limit.** Nothing here lengthens a run or loosens the guard. The
  wall law says a run that closes at a wall would not be opened by more moves, since each move gains
  less.
- **Bits read as progress.** No code length is offered as progress. §3 counts decisions of the
  release's order, at the opening, with no training.
- **A located cause carried unrepaired.** The located cause is the release's order, and its owner is
  `hnn::prediction`. This record changes no owner; the release law stays proposed (#225 §7).
- **Text run on its codec's grain.** The read is on the order-2 terrain. The order, the turns and
  the grain are the receiving bank's, the same for every chart.

## 1. The question, fixed before the read

[fixed before the 8-request read; the 1-request development read had been seen] Does the release's
gap order follow the commitment order of the turn clock? #225 §7 predicts that it does as a proxy,
which would mean that wherever the enclosures decide, every refinement's gap lock lies in the
whole-turn law's first set (the eligible stations of least commitment turn). A refinement whose gap
lock commits strictly later refutes that. The read is a characterization and has no acceptance count.

## 2. Walls: what a zero-temperature descent does at one

[proved-derived; formal-checked] Along one move's direction, let the comparison be its continuous
part `g` short of a step length `w` and `g + J` from `w` on. The wall is uphill: `J` exceeds what
`g` falls between any step short of `w` and any step past it. Every trial at or past `w` is refused,
and a trial short of it that descends is adopted. The move tries `η₀` and halves it.
- **The first halving short of the wall lands within half of it** (`first_halving_short_of_wall`).
  With `η₀ ≥ w`, the first `η₀/2^k < w` satisfies `η₀/2^k ≥ w/2`: the trial before it was at or past
  the wall.
- **So the wall's distance halves at every adopted move** (`wall_distance_halves`). After the move,
  the wall lies at most `w/2` ahead. If the next move's direction keeps meeting the same wall, then
  after `n` moves it lies within `w/2^n` (`wall_distance_le`).
- **What a move can still gain shrinks with it** (`gain_short_of_wall`). With `g` falling at most
  `G` per unit step, a move that stays short of a wall at distance `d` gains at most `G d`.
- **At the wall, every halving is refused** (`jump_refuses_every_halving`, from #225).

So a chain whose direction keeps meeting an uphill wall approaches it geometrically, with geometric
falls in its gains. It closes where a gain no longer exceeds the certificate's resolution, or at the
wall itself. That is a stopping state with a nonzero continuous slope. #195 proves that every
candidate move is a gradient step under some metric and stops only where the gradient vanishes;
that holds for each continuous part. A comparison with an order has walls between the parts, and a
wall stops the chain too.

**Its signature in a chain's receipts.** Toward a wall, the adopted rungs fall move by move (each
move's adopted `η` at most half the last one's distance), and the closing refusal at the smallest
rung splits into a held decrease below the flip. `m6` adopted at `1/2048` with no flip, and `m7` was
refused at every rung by a flip of `34038/4096`, fixed in size from `1/64` down
([the refit's ingredients](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
§4). That is this signature at one wall.

## 3. The gap order beside the commitment order, at the founded opening

[measured; read-only] `executed instants` (`research/notebook/hnn_design/hnn_executed_loop.rs`,
commit `eb5a8a77`) runs each request's release under its own law, `LockOrder::Gap`, and keeps the
refinements. At each refinement, every eligible station's commitment turn is read from its
candidates' joint growths. The turn is the least whole `n` with `(1 + R(n))^16 ≤ 2`,
`R(n) = a_top^(−n) + Σ_y (a_y/a_top)^n` (`commit_turn_iff`). It is enclosed from the readings' two
ends, with each power carried by squaring and every product rounded outward on `2^(−64)ℤ`, so the
enclosure is sound.

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
  the release's law, and in each of the 17 the later turn. The gap is `a_top − a_runner`, a difference of growths, and it
  grows with the scale of the growths. The turn reads the ratio `a_runner/a_top` and the threshold
  term `a_top^(−n)`, and it does not depend on that scale.
- **The commitment turns of the gap locks** run from 2 to 366, most between 3 and 11 (the
  histogram is in the receipt). So the whole-turn law's resolution of one turn is coarse beside an
  instant of 3 turns and fine beside one of 300.
- **Receipt.** Development read, 1 request: `25354` ms, peak resident `54095872` bytes. Projection
  for 8: `8 × 25354 = 202832` ms; deadline `203` s by `timeout`. Measured: `70095` ms
  (`70095/202832` of the projection), peak resident `57376768` bytes, 4 cores, rayon over requests
  and candidates. Receipts: [`2026-10-02_WALLS_receipts/`](2026-10-02_WALLS_receipts/)
  (`opening8.txt`, `dev1.txt`).

## 4. What this changes

- **#225's "proxy" is withdrawn.** The gap order is a different order, not a coarse or fine version
  of the commitment order. The two disagree in 17 of the 56 refinements the enclosures decide at the
  opening. The correction is made in #225's §7 in the same branch.
- **The release's walls are where gaps tie.** Two stations swap lock order where
  `a_top − a_runner` ties between them. The lock face, which reads shares, has no feature there. A
  wall of the commitment order is where a station's turn changes, which the face does read: it is
  where the top's share over that many turns reaches the grain.
- [agent-inferred] **The chain's closures may sit at gap-order walls the face does not read.** The
  native move descends the comparison the release executes, and that comparison changes order at
  gap ties. A run closing at such a wall (§2) closes on a feature of the release's ranking, not of
  the lock face. Whether the main line's closures are of that kind is the read of §5.

**What it does not show.** It does not show that the whole-turn order would let the chain pass any
wall, nor that it would reach the refit's basin or any held-out decision. The whole-turn release is
not built.

## 5. What the main line reads

For each closed run of the chain (moves 1, 2, 3, 4, 12, 13 at `ρ` held at the fit's value, and
`m7`):
1. **The approach.** The adopted rung of each move before the closure. A geometric fall in the
   adopted `η` toward the closing state is §2's signature.
2. **The closing split.** At the smallest rung, the held decrease and the flip (#202's split), and
   the request and station pair that flips.
3. **Whose wall it is.** `executed instants` at the incumbent and at the refused successor, on the
   flipping request. If the pair's commitment turns keep their order (or stay in one turn) across the
   step while the gap order swaps them, the wall is the gap order's alone.

## 6. Verification

- Lean: `bash tools/lean_check.sh HolonicsResearch.HNN.OrderTemperature` builds with no errors,
  warnings or `sorry` (`first_halving_short_of_wall`, `wall_distance_halves`, `wall_distance_le`,
  `gain_short_of_wall`; commit `d6ac25d9`).
- The diagnostic compiles in release with no warnings (`cargo build --release -p holonics --example
  hnn_prediction`). It changes no owner and no law.
- Owed (#62): the wall law along a chain whose directions change from move to move (here a
  hypothesis); and the commitment turn's enclosure as a theorem on the rounded powers (here argued
  from monotonicity).
