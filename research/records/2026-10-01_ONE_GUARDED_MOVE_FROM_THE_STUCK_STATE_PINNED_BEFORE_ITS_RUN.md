# One guarded move from the stuck state, under each metric (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the law change and the rules; [measured] only in the receipt.

## 1. What changed first: one lock reading for every consumer

The comparison's lock at each decision is one normalized receiver: the resting sheet and the
candidates, read at one common representative of their readings (`LockFace::sheets`). Until now
three consumers read it differently:
- the certificate read the shares' enclosures, which stays: enclosures are bounds;
- the descent covector's weights `θ_x − [x = t]` took each share's own midpoint;
- the witness's metric took the common representative.

Independent midpoints need not sum to one (Astra: three readings in `[1, 9]` give `51/40`). So the
returned covector and the metric could describe two different receivers. Now:
- `LockFace` owns the one reading, and the covector's weights read it (`LockFace::weight`);
- the witness's form reads it through `receiver::face::softmax_jacobian`, which admits only a
  normalized, nonnegative face;
- the integration test `one_lock_reading_serves_the_comparison_the_covector_and_the_metric` runs
  Astra's `[1, 9]` case through the real proposal and the metric.

**Replay identity changes.** Every lock-face move's covector weights move within their enclosures,
so the earlier runs (gate A, the guarded witness) no longer replay bit for bit. Their records and
receipts stand as the measurements of the law they ran.

## 2. The move under a declared metric

The move adjusts two things together:
- the source representation `E`, which maps incoming structure into the receiving state;
- the memory transport `ρ`, which sets how much of each earlier contribution a crossing carries.

The metric decides how the two changes are sized against each other and how their interaction is
counted (`hnn::executed::MoveMetric`):
- **coordinate**, the law the runs used: `E` by the source port's normal law, `ρ` by
  `−γ_ρ/Σ|∂z/∂ρ|²` in the storage coordinates, with no interaction term;
- **witness**: both measured by the lock's own normalized reading, pulled back onto the plane of
  `E`'s unit move and `ρ`, interaction included. The plane step is `(α, β)`. The ladder starts at
  `α` (at most the entry scale), and `ρ` moves `β/α` per unit of `E`'s step. A step with no reading
  of some plane direction is refused (`Invisible`); one that reverses `E`'s unit move is refused
  (`Reversed`).

Every guard is the same under both metrics, including the executed release's descent. A step's
size is a constitutive change, not a velocity or an elapsed time.

## 3. The run

`executed move-once order2 2026093061 8 <out> c6=<the guarded witness's c6.state> coordinate witness`.
The state is restored whole (`ContinuingState` and `Constitution::continued`, no `E`/`ρ` fallback),
and every arm starts from that same restored c6. The order follows Astra's attribution:
- the coordinate metric first, on the corrected lock reading;
- if it is adopted, the run stops: the reading's repair alone explains the escape;
- only if it is refused, the witness's metric from the same restored c6, with its direction, form
  and ladder prepared afresh there.

Each move prints its incumbent, every trial with its refusal kind, the witness's form where read, and
the adopted successor's own release. The incumbent's `L` is checked against the guarded witness's
`[373776/4096, 373781/4096)`. The lock reading changes only the covector's weights, not the
comparison's value, so it should match exactly. `E`'s trial steps are carried by the source port's
own prepared step at each `η` (`PreparedStep::stepped`), never a carried unit move rescaled. This is
a test of escape from an existing state, not the sixth iterate of a corrected trajectory.

**The outcome rules, fixed before the run:**
- **(M1) the witness's move is adopted and the control's is refused.** The corrected metric admits
  a guarded step where the coordinate one cannot. Report what changed: `E`'s step, `ρ`'s move
  against the chord to the refit's `ρ*`, the executed `L`, and the decisions (solved, right, whole).
  A larger `ρ` change or a lower smooth `L` alone is not success. Only then does a longer
  continuation have information value, and it is put to Brandon with its own projection.
- **(M2) the control is adopted.** The corrected reading alone unblocked the state, and the witness
  is not attempted. Report the move.
- **(M3) both are refused.** Stop. The obstruction is read from the trials' refusal kinds:
  - the mask's descent (`NotBelow`);
  - the executed release's descent (`OwnNotBelow`);
  - the first order;
  - the entry bound;
  - the witness's domain (`Invisible`, `Reversed`).

  That kind is the next subject. A refusal at c6 does not show the architecture cannot learn.

## 4. Time, threads and the stopping rule

- **Measured units.**
  - The guarded witness's move 6 at c6, with an incumbent read, persistence, the proposal, the unit
    step and 8 refused trials, took 440,346 ms at 19 threads. That is the coordinate move's upper
    bound.
  - The witness's move adds the plane's terms. The plane read at c6, an incumbent read, the unit
    step and the plane, took 78,889 ms, so the witness's move is bounded by
    `440,346 + 78,889 = 519,235` ms.
- **Projection** `440,346 + 519,235 = 959,581` ms (both arms, when the control refuses), so
  `timeout 960`. One harness line per move
  (its incumbent's report), so the probe's per-line bound is the larger move, 519,235 ms.
- **Threads.** `RAYON_NUM_THREADS=19`, beside nothing else.
- **Early stop.** The launcher stops the run when a move passes 519,235 ms, reported incomplete.
  Nothing is raised.
- **The failures this could repeat:**
  - 5, an uncertified step: every commit guard stays;
  - 7: a lower `L` or a larger `ρ` change is not progress, decisions are read;
  - 9: fixed deadlines;
  - 1: nothing authored reaches the machine (the metric is the lock's own reading).
