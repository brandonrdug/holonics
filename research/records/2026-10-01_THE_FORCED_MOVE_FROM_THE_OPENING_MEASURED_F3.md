# The forced move from the founded opening measured: F3, the forced descent does not reach decisions either

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_FORCED_MOVE_FROM_THE_OPENING_PINNED_BEFORE_ITS_RUN.md); [agent-inferred] where
marked. Receipts: [`2026-10-01_THE_FORCED_MOVE_receipts/`](2026-10-01_THE_FORCED_MOVE_receipts/).

## 1. The trajectory

Eight guarded witness-metric moves under `order-forced` from the founded opening. All were adopted:

| State | `ρ` (`/2^21`) | Forced `L + O` (`/4096` nats) | Forced solved | Stations right | Released |
|---|---|---|---|---|---|
| opening | 1645392 | `[2437919, …)` | 0 of 285 | 15 | 7 |
| move 0 | 1644401 | `[2421157, …)` | 0 of 285 | 11 | 8 |
| move 1 | 1643925 | `[2310998, …)` | 1 of 288 | 11 | 7 |
| move 2 | 1635370 | `[2302561, …)` | 1 | 7 | 6 |
| move 3 | 1631035 | `[2210716, …)` | 3 | 14 | 8 |
| move 4 | 1626381 | `[2183135, …)` | 3 | 16 | 8 |
| move 5 | 1633268 | `[2178070, …)` | 2 | 15 | 8 |
| move 6 | 1627149 | `[2164976, …)` | 2 | 16 | 8 |
| move 7 | 1630043 | `[2150938, …)` | 2 | 16 | 8 |

**F3.**
- The forced comparison falls by `286981/4096` nats over the eight moves.
- Its solved terms reach 3 of 288, then fall back to 2.
- Stations right drop to 7, then return to 16, never above the corrected move's best (16) or gate A's
  (24). No section is whole.
- `ρ` moves `15349/2^21` toward `ρ*` (a chord of `544808/2^21` from the opening).

## 2. What it means

[agent-inferred] Every comparison measured has now been descended with sound, guarded moves:
- the lock face at the decisions;
- with the order;
- with one lock reading;
- under the witness's metric;
- along the forced release, the induction-sound objective that reads every decision along the right
  trajectory.

The descents fall, and the decisions do not follow on this batch. Even where the objective's solved
level would imply whole sections, its descent reaches 3 of 288 terms. So the comparison is no longer
the limit to examine. Per the pin, the representation is: what this placement's `E` and `ρ` can
express, and how the refit (55 right, 45 of 64 solved) differs from every state these moves reach.
The witness's span already showed the moves cannot see the directions the refit occupies
([the span](2026-10-01_THE_WITNESSS_DIRECTION_IN_THE_SPAN_OF_THE_RETURNS.md)).

## 3. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 8 moves, 19 threads | `8 · 531,349 = 4,250,792` ms | `timeout 4260`; `timeout 532` and per-line 531,349 ms each | 3,155,180 ms, all adopted, no early stop | 1,232,965,632 bytes |

Measured over projected: `3155180/4250792`.
