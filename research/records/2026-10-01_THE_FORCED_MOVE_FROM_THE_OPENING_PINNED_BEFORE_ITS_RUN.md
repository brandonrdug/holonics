# The forced move from the founded opening (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the rules; [measured] only in the receipt.

## 1. Why

The forced release (`order-forced`) reads every decision the release faces along the right
trajectory, each in its own context, with the order at every refinement
([the forced release](2026-10-01_THE_FORCED_RELEASE.md)). If every term is solved, the section is
whole. It agrees best with stations right (43 against 15 over 12 states), and its `ρ` slope at the
opening points toward the refit. Its read now costs 39,388 ms at the opening.

## 2. The run

Eight guarded moves under the witness's metric:
`executed move-once order2 2026093061 8 <out> m<k>=<state> order-forced witness`. They start from the
guarded witness's `c0.state` (the founded opening) and continue from each adopted successor, stopping
at the first refusal (`.local/run.sh`).

**Outcome rules**, against the corrected move at the decisions from the same opening (R3: at most 16
right, ending at 13, nothing solved) and gate A (at most 24 right, no section whole):
- **(F1) a whole section, or stations right above 24:** the induction-sound objective leaves the
  valley. Continue toward gate A's budget, then gate B's controls.
- **(F2) the forced terms' solved count rises, with stations right above 16:** the objective
  advances along the right trajectory. Report both.
- **(F3) neither:** the forced descent does not reach decisions on this batch either. The comparison
  is then not the limit, and the representation (`E` and `ρ` at this placement) is examined against
  the refit's.

## 3. Time

The unit bound is one forced move: the measured read of 39,388 ms (incumbent, proposal and
derivatives), plus the plane's 78,889 ms, plus 8 trials at the largest measured forced compare,
51,634 ms. That gives `531,349` ms, `timeout 532` and a per-line bound of 531,349 ms. The projection
is `8 · 531,349 = 4,250,792` ms, with an outer `timeout 4260`, at 19 threads.
