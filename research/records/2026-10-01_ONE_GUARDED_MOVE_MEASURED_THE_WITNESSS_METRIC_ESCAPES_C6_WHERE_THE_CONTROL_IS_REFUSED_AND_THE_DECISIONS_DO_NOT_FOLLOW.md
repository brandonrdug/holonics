# One guarded move measured: the witness's metric escapes c6 where the control is refused, and the decisions do not follow

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_ONE_GUARDED_MOVE_FROM_THE_STUCK_STATE_PINNED_BEFORE_ITS_RUN.md) (source `b07d08de`);
[agent-inferred] where marked. Receipts: [`2026-10-01_ONE_GUARDED_MOVE_receipts/`](2026-10-01_ONE_GUARDED_MOVE_receipts/)
(listing, identities, the adopted successor's continuing state).

## 1. The outcome: M1

Both arms started from the same restored c6, the guarded witness's state where its move 6 was refused.
The incumbent read `L ∈ [373776/4096, 373781/4096)`, solved 2, stations right 15, no section whole,
exactly as the guarded witness read it.

- **The control** (coordinate metric, on the corrected lock reading) was refused at all 8 trials:
  `η = 4` by the mask (`NotBelow`), `2` down to `1/32` by the executed release's descent
  (`OwnNotBelow`). Every trial's `ρ`, mask and own composition equal the guarded witness's move 6
  at the printed grain. The lock reading's repair alone does not unblock the state.
- **The witness's metric** was adopted at its third trial, `α/4`, where `α` lies in
  `[12625805/2^23, 12625806/2^23)`. `α` and `α/2` were refused by the executed release's descent.
  At the adopted step:
  - `ρ` moved from `1642461/2^21` to `1631843/2^21`, toward the refit's `ρ*`, by `10618/2^21`. That
    is `10618/541877` of the chord, against the coordinate law's largest step of `8010/2^21` in the
    whole guarded run.
  - The executed `L` fell to `[373101/4096, 373106/4096)`, by `675/4096` nats. The mask's fell to
    `[365885/4096, …)`.
  - **The decisions did not follow.** Solved stayed at 2 of 64, stations right fell from 15 to 13,
    and no section was whole.

By the pin's rules, a larger `ρ` change or a lower `L` alone is not success. The move escaped the
state where the coordinate law was stuck, which the corrected metric alone explains: the control on
the same reading was refused. It did not improve a single decision.

## 2. What it means

[agent-inferred] The coordinate metric's direction at c6 leaves the executed release's descent
within one ladder: every one of its 8 trials raised the own `L`. The witness's direction, sized by
the lock's own reading with the interaction between `E` and `ρ` counted, still descends the
executed release a quarter of the way along its Gauss–Newton step. So the stuck state was a fact of
the metric, not of the state. But the executed comparison's descent is not decision progress here:
the lock face's smooth `L` can fall while a lock's sheet moves away from its target. The next
question is what the comparison's covector at the decisions carries. The guarded witness pin named
it for its G2 outcome, and it returns here with the metric repaired.

## 3. A defect the run exposed

The ladder started at the witness's `α` carried exactly. Solved from `δ` held at 128 bits, it has a
1229-digit denominator, and every trial step and successor carried it. The step was valid, but a
value outgrew its carrier. The next change holds `α` at a declared dyadic grain before the ladder
(the source port's lattice reads it there anyway), recorded with that change.

## 4. Time and resources

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| the control (8 trials), then the witness (3 trials), 19 threads | 959,581 ms | `timeout 960`, per-move bound 519,235 ms | 689,303 ms, exit 0, no early stop | 215,592,960 bytes |

- The control's move took 439,775 ms against its bound of 440,346.
- The witness's move took 249,390 ms against its bound of 519,235.
- Measured over projected: `689303/959581`.
