# The kinetic move from the opening, measured: the comparison falls fastest and the decisions stay

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured].
Pin: [the kinetic move pinned](2026-10-02_THE_KINETIC_MOVE_FROM_THE_OPENING_PINNED_BEFORE_ITS_RUN.md).
Receipts: [`2026-10-02_THE_KINETIC_MOVE_receipts/`](2026-10-02_THE_KINETIC_MOVE_receipts/).

## 1. Result

**The acceptance fails.** Seven guarded kinetic moves from the opening lower the lock face at the
decisions from `[500197/4096, …)` to `[337896/4096, …)` nats. The stations right go from 15 to 13 and
the solved decisions from 0 to 1, and no section is whole. The eighth move is refused by the guards.

| Move | Adopted step | Solve | `L` after (`/4096` nats) | Solved | Right | Wall (ms) |
|---|---|---|---|---|---|---|
| opening | | | 500197 | 0 | 15 | |
| 0 | `1/32` (entry scale) | 320 iterations, residual energy `2144019/2^49` | 453778 | 0 | 16 | 167,779 |
| 1 | `1/32` | 320 | 430767 | 0 | 15 | 186,894 |
| 2 | `1/32` | 320 | 392653 | 0 | 12 | 181,696 |
| 3 | `1/32` | 320 | 371636 | 1 | 14 | 180,689 |
| 4 | `1/16` | 320 | 341143 | 1 | 13 | 179,659 |
| 5 | `1/256` | 290, converged | 338257 | 1 | 13 | 334,203 |
| 6 | `1/2048` | 302, converged | 337896 | 1 | 13 | 455,557 |
| 7 | refused (guards) | 303, converged | | | | 455,543 |

From move 5 on, the larger trials lower the fixed mask but raise the machine's own release
(`OwnNotBelow`): the comparison has reached a basin of its release, as every earlier metric did
([R3](2026-10-01_THE_CORRECTED_MOVE_FROM_THE_OPENING_MEASURED_R3_THE_SAME_VALLEY.md),
[F3](2026-10-01_THE_FORCED_MOVE_FROM_THE_OPENING_MEASURED_F3.md)). The kinetic metric reaches it faster
and lower: `162301/4096` nats in seven moves, against R3's descent along the same arm's valley.

## 2. What it settles

- **The metric was not the blocker.** The full Gauss–Newton move over all 600 entries of `E`, with
  the witness's coupling and the port's mass, descends the comparison furthest. The decisions do
  not follow it. The solve's direction is at chance against the `E` leg to the refit (the pin §2),
  so the comparison's local geometry leads away from the refit at every step.
- **A lower comparison is not evidence of the mechanism.** This is Astra's point of October 2:
  each accepted successor here is a state written by an exterior optimizer, and the decisions are
  a classification readout. Neither exhibits a return reaching a contact, changing its
  constitution, and being consumed on a later cut.

[agent-inferred] The comparison-descent line ends here. The next loop is a read of the owners,
with no run: one emitting contact, the return that actually reaches it, the change to its
constitution, and the later cut that consumes it (Astra's owner-to-consumer check). The
kinetic metric stays in `hnn::executed` as the move's Gauss–Newton law and its tests.

## 3. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 8 moves, 19 threads | `8 · 630,263 = 5,042,104` ms | `timeout 631` and a per-line `630,263` ms per move | 2,142,020 ms (move 7 refused), no early stop | 235,474,944 bytes |

Measured over projected: `2142020/5042104`. Moves 5 to 7 ran longer (`334,203` to `455,557` ms)
because each walked the ladder through refused trials.
