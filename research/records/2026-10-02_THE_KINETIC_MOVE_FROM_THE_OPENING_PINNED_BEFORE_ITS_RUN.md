# The kinetic move from the opening, pinned before its run

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition] for the
pin; the run is [measured]. Receipts: [`2026-10-02_THE_KINETIC_MOVE_receipts/`](2026-10-02_THE_KINETIC_MOVE_receipts/).

## 1. The claim fixed first

The receiver's minimum-energy move over all of `E` (`MoveMetric::Kinetic`, the
[`hnn.kinetic-move`](../../docs/atlas/objects.tsv) row) is the native counterpart of the refit's
exterior Gauss–Newton fit. **Acceptance:** from the opening (`c0.state`), on gate A's batch under the
lock face at the decisions (`lock-dec`), the chain of guarded kinetic moves raises the stations
right above the opening's 15 and the solved decisions above 0 at its last adopted move. Anything
less is reported as what it measured.

## 2. The read before the run

The solve read at the opening ([`read8/`](2026-10-02_THE_KINETIC_MOVE_receipts/read8/listing.txt)):
320 reading coordinates; 320 iterations with residual energy `2144019/2^49` of its opening
(stopped at the iteration bound). Every iterate's signed squared cosine with the `E` leg to the
refit lies within `[−8768139/2^33, 7932255/2^31]`. A random direction in `E`'s 600 entries has
expected squared cosine `1/600`. The first iterate is the normal law's own direction: it is
`8092753/2^33` against the leg, and the unit move is `16185495/2^34`, the same value. So the local
Gauss–Newton direction is not the chord to the refit. The run tests whether its moves improve the
decisions anyway.

## 3. The run

`bash research/records/2026-10-02_THE_KINETIC_MOVE_receipts/run.sh`: up to 8 successive
`move-once … lock-dec kinetic` moves, each from the last adopted state, stopping at the first refusal.

| | Value |
|---|---|
| Per-move projection | R3's per-move bound `519,235` ms plus the solve read's `111,028` ms: `630,263` ms |
| Deadline | `timeout 631` and a per-line `630,263` ms per move; `8 · 630,263 = 5,042,104` ms for the chain |
| Threads | 19 (`RAYON_NUM_THREADS`), alone on the host's CPU |
| Early stop | a move past its per-line bound stops the chain, which is then reported incomplete |

**The failures this could repeat** (the lessons records): 9, raising a limit; 7, a count read as
progress (decisions, not `L`, are the acceptance); 3, a consumer that isn't built (the move's ladder
is the consumer, the same guards as every metric).
