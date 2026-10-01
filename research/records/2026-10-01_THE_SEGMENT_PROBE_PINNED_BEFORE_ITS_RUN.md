# The segment probe: does the lock face rank a working constitution below gate A's, and does it need the lower modulus? (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the question, the reads and the outcome rules; [measured] only after the run, in
its receipt. Read-only: no move, no update, no fit, no law changed.

## 1. Why this read, and why not the two proposed after c2

The [c2 record](2026-10-01_LOOP_1C_C2_NORMALIZATION_ALONE_UNDOES_TWO_OF_THREE_LOSSES_ONE_IS_AN_INTERACTION_AND_THE_ENTRY_KEEPS_THE_FOUR_RETAINED.md),
as corrected, put the causal consumer at the decision at its own lock. Two follow-ups were proposed
there and are withdrawn here, from the mathematics:

- **(A) a "predecessor-occupancy" normalization at native prefixes.** The information available to a
  decision at a prefix is the request and the stations locked in the refinements before it. That is
  availability in the release's own refinement order: neither a station's index nor its tick. The
  station-framed law (`BankPlacement::weights`, Lean `HNN/IndexedOpen` §5) already normalizes over
  exactly that set: the request's cells and every placed station, each at its two-sided transport
  distance. Its kernel `ρ^|Δτ|` is the ring's stationary response, so it was derived independently
  of any score.
  - An index set "before `j`" by station index or by tick would discard placed stations that the
    decision can read. That is contemporary input removed with no law behind it, which makes it an
    exploratory constitutive intervention.
  - The [re-entry diagnosis](2026-09-30_THE_RE_ENTRY_DIAGNOSED_A_LATER_LOCK_TAKES_THE_SPANS_MASS_AND_QUENCHES_THE_EARLIER_STATIONS.md)
    already read its behaviour: the clock-order release, where every placed datum precedes the
    station it reads, was whole at 2 of 16 against 1.
  - (A) is not pinned.
- **(B) an exterior fit for representability at decision time.** Unneeded. A representation control
  exists:
  - The station-framed refit (`refit_on_lattice.txt`; `ρ* = 137573/262144`, `E`'s largest entry
    `2717237/1048576`) is read natively by today's binary in the baseline replay. On order-2
    development seed 41 it releases 6 whole sections of 8 and 57 stations right of 64
    ([replay reference](2026-09-30_THE_BASELINE_receipts/replay_reference.txt)).
  - On Stage 0's 128 held-out requests it released 96 whole.
  - Reading it on gate A's own batch answers representability without any fit.

**The question this leaves.** Gate A's native move ran 16 certified moves on one fixed batch of 8
requests (order-2, development seed `2_026_093_061`). Measured at gate A:
- at most 7 of 64 decision terms solved, stations right from 13 to 24 of 64 (a quarter is 16), and
  0 whole sections;
- the lock face `L` falling from `[500197/4096, 500203/4096)` nats to at least
  `[342226/4096, 342231/4096)` (constitution 14);
- the modulus held within `[809211/1048576, 829845/1048576]`.

A constitution of the same kind (`E` and `ρ` of the source port, the declared bank, the
station-framed release) is known to read order-2. Three causes are open:

- **(O) the objective**: the lock face at the decisions does not rank the working constitution below
  the ones the native move reached;
- **(P) the path**: it does rank it lower, but the move did not head there;
- **(M) the modulus**: the working reading needs `ρ` far below the founded `ρ₀ = 102837/131072`,
  where gate A's modulus never went.

## 2. The read

- **Mode.** `hnn_prediction -- executed segment order2 2026093061 8 <label=source>…` (built in this
  pin's commit; `research/notebook/hnn_design/hnn_executed_loop.rs`, `segment`). Each constitution
  is read on gate A's 8 requests by gate A's comparison (the lock face at the decisions,
  `Comparison::LOCK_DECISIONS`).
  - Per constitution: decision terms solved; class and threshold holding at the decision terms;
    whole sections; stations right, by station; the first lock's station and whether it is right;
    `L` and `X` enclosed; `E`'s largest entry; `ρ`; the term counts.
  - Every request's release, `r*` and every decision term whole (`ℓ`, solved, `θ_t`, the target's
    and leading rival's growths).
- **The constitutions**, in this order (the most decisive first), with the chords exact in `E` and
  in `ρ` (each chord's `ρ` lies on the source port's lattice `2^(−21)`):

  | Label | Source | `ρ` |
  |---|---|---|
  | `refit` | the refit, `E*` and `ρ*` (remount: `E` and `ρ` alone, labelled partial) | `137573/262144` |
  | `refit-founded` | `E*` at the founded modulus | `102837/131072` |
  | `gateA-best` | gate A's `witness_best.state` (its constitution 1, complete continuing state) | `1646645/2097152` |
  | `chord-3/4` | `Θ₀ + (3/4)(Θ* − Θ₀)` | `1236786/2097152` |
  | `chord-1/2` | `Θ₀ + (1/2)(Θ* − Θ₀)` | `1372988/2097152` |
  | `chord-1/4` | `Θ₀ + (1/4)(Θ* − Θ₀)` | `1509190/2097152` |
  | `opening` | the founded opening `Θ₀` | `102837/131072` |

- **Two identity controls.**
  - `opening` must reproduce gate A's constitution-0 line: solved 0, released 7, stations right 15,
    `L ∈ [500197/4096, 500203/4096)`, held 56.
  - `gateA-best` must reproduce its constitution-1 line: solved 7, released 8, stations right 16,
    `L ∈ [517184/4096, 517189/4096)`, held 54.
  - A mismatch in either voids the run, which is then reported as such and not interpreted.

## 3. The outcome rules, fixed before the run

Gate A's lowest `L` is `L_A = [342226/4096, 342231/4096)`, and its most stations right is 24.

- **(O) holds** when the refit reads more than 24 stations right, or any whole section, while its
  `L` is not below `L_A` by disjoint enclosures. The composition does not see the working
  constitution. The next loop is then the composition, located by its terms here (which `ℓ` carry
  the refit's `L`: the resting sheet, the held terms at `r*`, or ties among rivals), and not the
  move.
- **(P) holds** when the refit reads more than 24 right and its `L` lies below `L_A` by disjoint
  enclosures. The composition ranks it below everything the move reached, so the move's path is the
  blocker.
  - The chord shows whether `L` falls strictly along `opening → chord-1/4 → chord-1/2 → chord-3/4 →
    refit` (each below the last by disjoint enclosures) or rises somewhere on it.
  - A monotone chord shows that a descent path from `Θ₀` exists and that the move did not take it.
    A rise shows a barrier on this chord only, never that no descending path exists.
  - The next loop is then the move's direction (the normal law's step through the carried Gram,
    against the comparison's own covector) and its step.
- **(M)** is read from `refit-founded` against `refit`:
  - If `refit-founded` reads at most 24 right and no whole section while `refit` reads more, then
    the working reading needs a modulus below the founded one, and gate A's modulus never left
    `[809211/1048576, 829845/1048576]`. The modulus's step is then implicated, with (O) or (P)
    alongside.
  - If `refit-founded` keeps more than 24 right, the founded modulus admits the refit's `E` reading.
- **No transfer**: if the refit reads at most 24 right and no whole section on this batch, neither
  (O) nor (P) is decided. The representation control does not hold on gate A's batch, and that is
  reported. The refit was fitted by an exterior float procedure on other requests, and seed
  `2_026_093_061` was never read by it.
- **What it cannot show.** It cannot show whether native deposition reaches the refit, and it makes
  no learning claim. The refit is one constitution among many that might work, and the chord is one
  path.

## 4. The failures this could repeat (the lessons record)

- **7, a local pass read as progress.** Nothing is trained, and no count here is progress. The
  refit's sections are an exterior fit's reading, reported as a control.
- **6, seen material graded as unseen.** The batch is gate A's development batch. Its numbers are
  diagnostic, and the refit never read it.
- **9, a refusal answered with a larger limit.** The deadline is fixed below and never raised, and
  an overrun is reported incomplete.
- **3, a located cause carried unrepaired.** No consumer is built: the harness mode is read-only.
- **1, an authored routine.** Nothing reaches the machine: the targets are read only by the
  comparison, as in gate A.

## 5. Time, threads and the stopping rule

- **The unit.** One constitution's lock-face read of 8 requests. The largest measured value before
  launch is 45,592 ms: constitution 1's read at 12 threads (loop 1c's cost reads). Gate A's
  compare-only read of constitution 16 took 39,972 ms on the default pool of 24 threads.
- **Projection.** `7 · 45,592 = 319,144` ms. **Deadline**: `timeout 320` on the process, fixed
  here, measured from launch (the binary is built before it).
- **Threads.** `RAYON_NUM_THREADS=19`, within the 19 of the host's 24 left beside Codex's reserved
  5; no other run is active. Memory: gate A's witness peaked at 235,536,384 bytes, so the projection
  is under 300,000,000.
- **Early stop.** Each constitution prints one line with its milliseconds. If any line exceeds
  45,592 ms, the run is stopped there and reported incomplete with the measured rate.
- **Receipts** (`2026-10-01_THE_SEGMENT_PROBE_receipts/`): the listing, the error stream (the
  partial-remount labels), `/usr/bin/time`'s wall time and peak resident set, and the identities:
  the source commit and the binary's sha256.
