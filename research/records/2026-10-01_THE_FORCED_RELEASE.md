# The forced release: every decision along the right trajectory, the best agreement, and a move the host cannot afford

**Date.** October 1. **Issues.** #73, #76, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for §1; [measured] for §2 and §3. Receipts in
[`2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/`](2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/).

## 1. The reading

The release decides in a cascade. A changed early lock moves every later decision's context, so no
comparison read in the release's actual contexts tracks its decisions between neighbouring states
([agreement](2026-10-01_THE_COMPARISONS_AGREEMENT_WITH_THE_DECISIONS.md), §4).

**The forced release** (`prediction::bank_release_forced`) runs the release's own lock iteration
under its own law: which stations lock comes from their own readings and the largest gap. Each lock
is placed at its target class instead of its top, so its refinements are the contexts the release
would read had every earlier lock been right.
- **`Reading::Forced`** reads every open station of every forced refinement. With the order term
  (`order-forced`) it covers every decision along the right trajectory, so if every term is solved
  the section is whole, lock by lock. It never reads a context with a wrong placed cell.
- **`Reading::ForcedDecisions`** reads each station once, at the forced refinement that locks it,
  with the order at the first refinement.

A placed target is a reading context, not a commit, so its Floquet certificate is not read. The
release itself, its sections and receipts, stays the release's own. Tests:
`the_forced_release_reads_every_decision_along_the_right_trajectory`, plus the forced arms in the
guard test (hnn 245 passed).

## 2. Agreement with the decisions (12 saved states)

| Comparison | All pairs, agree to disagree | Neighbouring moves, agree to disagree |
|---|---|---|
| `order-forced` | **43 to 15** | 5 to 3 |
| `order-fdec` | 40 to 18 | 4 to 4 |
| (for reference) `order-dec`, `lock-all`, `lock-tf` | 40 to 18, 40 to 18, 38 to 20 | 4 to 4, 5 to 3, 5 to 3 |

The forced release has the best agreement over all pairs, but between neighbours no comparison
separates from the others on 8 changing moves.

At the founded opening the forced comparison's slope in `ρ` is positive (`γ_ρ ∈ [2384414/4096, …)`):
it asks for the lower transport, toward the refit's `ρ*`. Under the lock face at the decisions the
same slope is negative there. This is the first comparison read whose `ρ` direction at the opening
agrees with the refit (`forced-incumbent-cost/`).

## 3. Its move does not fit the host

One incumbent read with covectors at every forced refinement took 649,026 ms at the opening: 285
terms, about four and a half times the decisions' candidates, each with its executed growth's
covector. Two guarded witness moves under `order-forced` from the opening were incomplete:
- the first at its 984 s deadline, from a bound not yet measured on this unit;
- the second at 1,141 s, a bound built from the measured incumbent (649,026 ms), the plane
  (78,889 ms) and eight trials (8 · 51,634 ms).

Neither printed a line, and neither was relaunched with a larger limit.

[agent-inferred] The forced comparison is the induction-sound objective. It has the best agreement
measured, and its `ρ` slope at the opening points where the refit lies. Its covector cost on the
host's exact arithmetic is the blocker, named by its measurement: a move at the opening exceeds
1,141 s. The executed growth's covector (`ReceivingBank::read_turn_covector`) has no device
realization (`holonics-cuda` carries the word, port, readout and moment, not the bank's turn
covector). Moving it to the card (#76) is what makes this objective affordable.
