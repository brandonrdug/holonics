# The order measured: one move from c6 gains stations where the lock face alone lost them, and four more reach 19 then stall

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_ORDER_AS_A_TERM_OF_THE_COMPARISON_PINNED_BEFORE_ITS_RUN.md) (source
`9bd8ba74`); [agent-inferred] where marked. Receipts:
[`2026-10-01_THE_ORDER_receipts/move/`](2026-10-01_THE_ORDER_receipts/move/).

## 1. The outcome: O1, narrowly

One move under the witness's metric with the order term joined (`order-dec`), from the restored c6:
- **Adopted** at its third trial (`α/4`); `α` and `α/2` were refused by the executed release's
  descent.
- **`ρ`** moved from `1642461/2^21` to `1633145/2^21`, toward `ρ*`, by `9316/2^21`.
- **The comparison** (lock faces plus order terms) fell from `[441372/4096, …)` to `[437814/4096, …)`.
- **Decisions:**
  - stations right 15 to **16**;
  - first locks right in 3 of 8 (requests 3, 5 and 6), against c6's 2;
  - solved 2 of 64, unchanged; no section whole.

The lock face's own witness move from the same c6 is the control: adopted, first locks right 3 of
8, stations right **13**. Same metric, same state; the order term is the difference. By the pin's
rule this is O1: more right first locks than c6 and stations right above 15. The margin is one
station above c6 and three above the control. It is one move.

## 2. The order terms

Seven of eight requests carry an order term (request 1 has no right top). None is solved. Its
value `ℓ_o`:
- **fell** in requests 2 (`[143977/65536, …)` to `[91294/65536, …)`), 4, 5, 6 and 7;
- **rose** slightly in request 0;
- **moved** in request 3, whose first lock came right: its decision refinement moved from 0 to 1,
  so its order is now read one lock later.

The far station still dominates the order. In request 2 station 7's gap fell from `60261/4096` to
`22887/2048`, while station 6's right gap grew from `2193/1024` to `36383/8192`.

[agent-inferred] The order term does what the decision margins named. It carries a covector to the
decision that sends the release into the uncompared contexts: the far station's gap against the
right station's. One move of it gains stations where the lock face alone lost them.

## 3. Four more moves

The same arm and metric, each move the real guarded move from the previous adopted continuing
state (`continuation/continue.sh`, receipts in `continuation/m1` to `m4`). Every move was adopted.

| State | `ρ` (`/2^21`) | `L + O` (`/4096` nats) | Solved | Stations right | Trial adopted |
|---|---|---|---|---|---|
| c6 | 1642461 | `[441372, …)` | 2 | 15 | |
| move 0 | 1633145 | `[437814, …)` | 2 | 16 | 3rd of 8 |
| move 1 | 1626995 | `[429006, …)` | 2 | 12 | 4th |
| move 2 | 1627257 | `[425516, …)` | 1 | **19** | 2nd |
| move 3 | 1625149 | `[424353, …)` | 1 | 19 | 4th |
| move 4 | 1624995 | `[424163, …)` | 1 | 18 | 6th |

- **Stations right** reached 19, above every constitution of the guarded witness (at most 18) and
  below gate A's best of 24. They are not monotone: move 1 fell to 12.
- **Solved** fell from 2 to 1. No section was whole, and no order term was solved.
- **The descent is slowing.** The comparison's fall over moves 1 to 4 shrank (`8808`, `3490`,
  `1163` and `190`, `/4096` nats), and the ladder adopted ever deeper (up to its 6th trial).
- **`ρ` moved `17466/2^21` in five moves** against a chord of `541877/2^21`.
- **The order's balance.** In every request the right station's gap is still below the wrong ones'
  together (no order term solved).
  The order terms' values fell in most requests, and two first locks moved to a right station and
  one away.

[agent-inferred] The order term reaches the decisions, which the lock face alone did not: stations
right rose where the lock face's move lost them. But on this batch it converges to a stall well short
of solving the order: the witness admits small `ρ` moves only, and the wrong stations' gaps keep their lead.
The stall is the next subject. It is not a reason to raise the ladder or the number of moves.

## 4. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| one move, 19 threads | 519,235 ms | `timeout 520` | 262,896 ms, exit 0 | 226,062,336 bytes |
| four continued moves, 19 threads | 2,076,940 ms (4 × 519,235) | `timeout 520` a move | 1,264,481 ms (312,038 + 230,841 + 321,209 + 400,393), all exit 0 | 228,278,272 bytes |

Measured over projected: `262896/519235` and `1264481/2076940`. The continuation's first launch read
no binary (its build directory was not exported), ran nothing, and was relaunched unchanged.
