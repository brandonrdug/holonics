# The corrected move from the founded opening (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the rules; [measured] only in the receipt.

## 1. Why

Every correction since gate A was measured from c6, a state the old law had already led into a basin
of the comparison ([the stiffness in ρ](2026-10-01_THE_STIFFNESS_IN_RHO.md)). From the founded opening
the chord to the refit descends. The valley is chosen by the first moves. The corrected move is:
- **the comparison:** the order at the decisions, whose agreement with stations right is 40 against
  18 where the lock face alone was at chance
  ([agreement](2026-10-01_THE_COMPARISONS_AGREEMENT_WITH_THE_DECISIONS.md));
- **the reading:** one normalized reading at each lock;
- **the metric:** the witness's, under every guard.

## 2. The run

Eight moves, each `executed move-once order2 2026093061 8 <out> m<k>=<state> order-dec witness`,
from the guarded witness's `c0.state` (the founded opening) and then from each adopted successor's
continuing state. The run stops at the first refusal.

**Outcome rules,** against the guarded witness (old comparison and metric; at most 18 right, no
section whole) and gate A (at most 24 right, no section whole):
- **(R1) a whole section, or stations right above 24:** the corrected move leaves the old valley.
  Continue toward gate A's matched budget, then gate B's controls.
- **(R2) stations right above 18 but at most 24, no whole section:** better than the guarded
  witness, short of gate A. Report the trajectory and the order terms.
- **(R3) at most 18:** the corrected comparison and metric from the opening do not change the
  valley. The comparison's agreement on nearby states, not its coverage, is the next subject.

## 3. Time

The unit is one order-dec witness move. It was measured at c6 and its continuation at 230,841 to
400,393 ms. Its bound is 519,235 ms, the coordinate move's 440,346 ms with all 8 trials plus the
plane's 78,889 ms. The projection is `8 · 519,235 = 4,153,880` ms, each move under `timeout 520` and
the probe's per-line bound of 519,235 ms. The whole run is under `timeout 4154`, at 19 threads.
Failures this could repeat: 9 (fixed deadlines), 7 (a fall in `L` is not progress; decisions are
read), 5 (every guard stays).
