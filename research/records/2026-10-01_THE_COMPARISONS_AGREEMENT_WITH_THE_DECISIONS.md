# The comparison's agreement with the decisions: at the decisions it is chance; every refinement and the order both agree

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

[agent-inferred] Both remedies of [the decision margins](2026-10-01_THE_DECISION_MARGINS_THROUGH_THE_ACCEPTED_MOVE.md)
raise the agreement from chance to 40 against 18:
- reading the release's later decisions in their own contexts;
- reading the first lock's order.

The lock face at the decisions sees neither. It is the composition the moves descended, which is
why they could fall without the decisions following. The next comparison joins both: the lock face
at every refinement with the order of every refinement. That covers every decision the release
makes, each in the context it was made.

## 4. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 12 states × 3 comparisons, 19 threads | `36 · 48,927 = 1,761,372` ms | `timeout 1762`, per-line 48,927 ms | 1,391,724 ms, exit 0 | in the listing |

Measured over projected: `1391724/1761372`.
