# The modulus's slope at the decisions: does the native comparison point the transport down? (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the question, the reads and the outcome rules; [measured] only in the receipt.
Read-only: no move, no update, no law changed. One receipt field is added: the storage curvature
`G_ρ` on `hnn::executed::SlopeSplit`, the quantity the committed move already divides by.

## 1. The question

The [segment probe](2026-10-01_THE_SEGMENT_PROBE_MEASURED_THE_LOCK_FACE_SEES_THE_REFIT_THE_CHORD_DESCENDS_AND_THE_READING_NEEDS_THE_LOWER_MODULUS.md)
established three facts. The lock face at the decisions descends strictly along the chord from the
founded opening `Θ₀` to the station-framed refit `Θ*`. The refit's reading needs `ρ` near
`ρ* = 137573/262144`. Gate A's moves held `ρ` near `ρ₀ = 102837/131072`.

Gate A's receipt gives the modulus's actual change at each of its 16 moves, in units of `2^(−21)`:
`+1253, +3046, +8892, −10048, −6775, +13462, −8249, −989, −10565, +8330, −25327, +41268, −19864,
−9475, +25642, −7070`. Their sum is `+3531`, against the chord's `−544808`. The moves are small
against the chord (the largest is under a thirteenth of it), but they also alternate in sign.

The move takes `Δρ = −γ_ρ/G_ρ` at the joint step. Here `γ_ρ = Σ_c c ⟨ĝ_c, ∂z_c/∂ρ⟩` is the
composition's first-order slope in `ρ`, and `G_ρ = Σ_c |∂z_c/∂ρ|²`. This read takes the move's own
`γ_ρ` and `G_ρ` at the constitutions below and tells two obstructions apart:
- **(S) sign**: `γ_ρ` points `ρ` up (`γ_ρ < 0`) at gate A's constitutions, or its sign is not stable
  among them. The comparison does not ask for the lower transport until `E` already reads the rule.
- **(K) scale**: `γ_ρ > 0` at gate A's constitutions, so the comparison asks for the lower transport,
  but the joint step moves it far less than the chord needs.

## 2. The read

- **Mode.** `hnn_prediction -- executed rho-slopes order2 2026093061 8 lock-dec <label=source>…`:
  gate A's batch and comparison (the lock face at the decisions). The proposal is formed exactly as
  `executed_move` forms it, and `modulus_slopes` reads its modulus part. Printed per constitution:
  - `γ_ρ`, with its target and rival parts;
  - `G_ρ` and the unit move `−γ_ρ/G_ρ`;
  - `L`, the solved count, the stations right and the whole sections.
- **The constitutions**, gate A's first:

  | Label | Source |
  |---|---|
  | `opening` | `Θ₀` (gate A's constitution 0) |
  | `gateA-c1` | `witness_best.state` (gate A's constitution 1) |
  | `gateA-c2` | loop 1c's `c2.state` (gate A's constitution 2, reproduced exactly) |
  | `chord-1/2` | `Θ₀ + (1/2)(Θ* − Θ₀)` |
  | `chord-3/4` | `Θ₀ + (3/4)(Θ* − Θ₀)` |
  | `refit-founded` | `E*` at `ρ₀` |
  | `refit` | `Θ*` |

- **Identity control.** The `L`, solved count and stations right of `opening`, `gateA-c1` and
  `gateA-c2` must equal gate A's constitutions 0, 1 and 2. A mismatch voids the run.

## 3. The outcome rules, fixed before the run

- **(S) holds** if `γ_ρ < 0` at `opening`, or if the sign of `γ_ρ` differs among `opening`,
  `gateA-c1` and `gateA-c2` (exactly: each `γ_ρ` is a rational read whole). The comparison's own
  slope does not ask for the lower transport where gate A stood.
- **(K) holds** if `γ_ρ > 0` at all three. Its size is then read as the unit move `−γ_ρ/G_ρ`
  against the chord's `−544808/2^21`.
- **Along the chord**: the sign of `γ_ρ` at `chord-1/2`, `chord-3/4`, `refit-founded` and `refit`.
  - It says where in `(E, ρ)` the lower transport begins to pay.
  - If `γ_ρ < 0` at `refit-founded`, the segment probe's secant (lowering `ρ` at `E*` takes `L` from
    `[310210/4096, …)` to `[133292/4096, …)`) is not local. The descent in `ρ` would cross a rise,
    and a first-order move cannot see it.
- **Not decided here**: what replaces the modulus's step. That is the next loop, built from this
  read's outcome.

## 4. The failures this could repeat

- **9**: the deadline below is fixed, and an overrun is reported incomplete.
- **7**: no count here is progress.
- **3**: the added field is a receipt of a quantity the move already computes. No consumer is
  built.

## 5. Time, threads and the stopping rule

- **The unit.** One constitution's incumbent read, with every decision term's five candidates'
  covectors, then the proposal and the modulus pairings. The largest measured value of a read that
  contains it is 83,271 ms: loop 1c's `site_gradients` at 7 threads, which also pulls every term
  back to `E`.
- **Projection.** `7 · 83,271 = 582,897` ms. **Deadline**: `timeout 583`.
- **Threads.** `RAYON_NUM_THREADS=19`, beside nothing else.
- **Early stop.** A constitution's line above 83,271 ms stops the run, which is then reported
  incomplete.
- **Launcher**: `research/notebook/hnn_design/read_probe.sh <out> 83271 583 executed rho-slopes …`
  (the segment probe's launcher, generalized; it enforces the deadline and the early stop).
- **Receipts** (`2026-10-01_THE_MODULUS_SLOPE_receipts/`): the listing, the error stream, the
  launcher's wall time, the harness's resident line and the identities.
