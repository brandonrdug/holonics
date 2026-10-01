# The corrected move from the founded opening measured: R3, the same valley

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_CORRECTED_MOVE_FROM_THE_OPENING_PINNED_BEFORE_ITS_RUN.md) (source `211c49b1`);
[agent-inferred] where marked. Receipts:
[`2026-10-01_THE_CORRECTED_MOVE_receipts/`](2026-10-01_THE_CORRECTED_MOVE_receipts/).

## 1. The trajectory

The move combines the order at the decisions, one normalized reading at each lock and the witness's
metric under every guard, from the founded opening:

| State | `ρ` (`/2^21`) | `L + O` (`/4096` nats) | Solved | Stations right | Released |
|---|---|---|---|---|---|
| opening | 1645392 | `[569492, …)` | 0 | 15 | 7 |
| move 0 | 1621579 | `[540006, …)` | 0 | 16 | 7 |
| move 1 | 1613169 | `[523839, …)` | 0 | 16 | 8 |
| move 2 | 1616996 | `[509744, …)` | 0 | 13 | 7 |
| move 3 | 1615168 | `[500955, …)` | 0 | 13 | 8 |
| move 4 | 1614241 | `[497677, …)` | 0 | 13 | 7 |
| move 5 | 1614046 | `[497037, …)` | 0 | 13 | 7 |
| move 6 | 1613995 | `[496858, …)` | 0 | 13 | 7 |
| move 7 | refused at all 8 trials (`OwnNotBelow`) | | | | |

**R3.** Stations right never exceed 16, and end at 13, below the opening's 15. Nothing is solved and
no section is whole. The comparison falls at every adopted move, from `[569492/4096, …)` to
`[496858/4096, …)`. `ρ` moves `32223/2^21` in the first two moves, more than in all five order moves
from c6, and then settles. The executed release's descent refuses every step of move 7.

## 2. What it means

[agent-inferred] The corrected comparison, reading and metric, applied from the founded opening,
lead into the same kind of basin as the old law: the comparison descends, then the guard refuses,
and the decisions end worse than they started. Every repair so far:
- the executed-release guard;
- the witness's metric;
- the order term;
- one normalized reading at each lock;

made the descent sound and the comparison closer to the decisions (40 against 18 over 12 states).
None turned a descent of the comparison into progress in the decisions on this batch.

Agreement over far-apart states is not enough. A descent compares a state with its neighbours, and
there the comparison's fall and the decisions' change are nearly independent. Between nearby states
the release's decisions turn on exact lock orders and gaps that the smooth comparison does not
follow. That nearby agreement is the comparison's next requirement, as the pin's R3 named, and no
more moves of this law are run until it changes.

## 3. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 8 moves, 19 threads | `8 · 519,235 = 4,153,880` ms | `timeout 4154`; `timeout 520` and a per-line 519,235 ms each | 2,307,016 ms (178,633 + 181,808 + 183,705 + 252,894 + 279,104 + 343,401 + 421,775 + 465,696, wall; move 7 refused), no early stop | 232,980,480 bytes |

Measured over projected: `2307016/4153880`. The moves' wall rose with each move, from 178,633 to
465,696 ms, as the ladder went deeper.
