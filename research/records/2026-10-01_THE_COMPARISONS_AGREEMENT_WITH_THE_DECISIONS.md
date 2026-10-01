# The comparison's agreement with the decisions: at the decisions it is chance; every refinement and the order each agree

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured], read-only;
[agent-inferred] where marked. Receipts:
[`2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/`](2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/).

## 1. The question

Three readings showed the comparison falling while the decisions did not:
- the order term's stall;
- the chord's rise from the stalled state while solved rose;
- the witness's span step.

A descent can only find decisions if a lower comparison means better decisions between nearby
constitutions. **Agreement** is the count of pairs of constitutions whose comparison and stations
right order them the same way, against the pairs ordering them oppositely. Ties are set aside.

## 2. From the receipts: the lock face at the decisions

Every constitution read under `lock-dec` on gate A's batch was collected from the receipts: 41
distinct ones (gate A, the guarded witness, the native direction, the segment probe, the moves'
metric, one guarded move, the span).

| Pairs | Agree | Disagree |
|---|---|---|
| all 41 | 535 | 191 |
| the native region (`L ≥ 340000/4096`, 38 constitutions) | 422 | 188 |
| within `8192/4096` nats of each other | 25 | 18 |
| within `20480/4096` nats | 69 | 64 |

It orders far-apart constitutions (the refit lies far below) but nearby ones at chance.

## 3. Twelve saved states under three comparisons

`executed agreement` reads the guarded witness's c0 to c6 and the order term's five moves under
`lock-dec`, `lock-all` (the lock face at every refinement the release executed) and `order-dec`. The
release is the same under each; only the terms read differ.

| Comparison | Agree | Disagree | Ties |
|---|---|---|---|
| lock face at the decisions (`lock-dec`) | 29 | 29 | 8 |
| lock face at every refinement (`lock-all`) | 40 | 18 | 8 |
| lock face and order at the decisions (`order-dec`) | 40 | 18 | 8 |
| lock face and order at every refinement (`order-all`) | 39 | 19 | 8 |

[agent-inferred] Both remedies of [the decision margins](2026-10-01_THE_DECISION_MARGINS_THROUGH_THE_ACCEPTED_MOVE.md)
raise the agreement from chance to 40 against 18:
- reading the release's later decisions in their own contexts;
- reading the first lock's order.

The lock face at the decisions sees neither. It is the composition the moves descended, which is
why they could fall without the decisions following. Joining both, the lock face and the order at
every refinement (`order-all`: an order term at each refinement the release executed, covering every
decision in its own context), reads 39 against 19: no further gain on these 12 states. Either
remedy alone carries the agreement. The open question is which one's descent reaches decisions:
the order term at the decisions was measured ([the order](2026-10-01_THE_ORDER_MEASURED_ONE_MOVE_FROM_C6_GAINS_STATIONS_WHERE_THE_LOCK_FACE_ALONE_LOST_THEM.md));
the lock face at every refinement was tried by one guarded witness-metric move from c6 and is
**incomplete**: it passed its deadline of 911 s before its first line (receipts in
`lock-all-move-incomplete/`). Its covectors are read at every refinement; one such read at the
opening alone took 440,159 ms. It was not relaunched with a larger deadline. The order at the
decisions carries the same agreement at about a quarter of the cost, so it stays the main line's
comparison.

## 4. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 12 states × 3 comparisons, 19 threads | `36 · 48,927 = 1,761,372` ms | `timeout 1762`, per-line 48,927 ms | 1,391,724 ms, exit 0 | 83,374,080 bytes (at exit) |
| 12 states × `order-all` (`order-all/`) | `12 · 48,927 = 587,124` ms | `timeout 588` | 460,551 ms, exit 0 | 82,309,120 bytes (at exit) |
| one `lock-all` witness move from c6 | `440,159 + 78,889 + 8 · 48,927 = 910,464` ms | `timeout 911` | 911,081 ms, **incomplete** (deadline) | |

Measured over projected: `1391724/1761372` and `460551/587124`.
