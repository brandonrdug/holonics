# The tightened certificate, pinned before its runs

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the pins; [measured] for the development reads (§3), which used development
seeds, the text's choosing role and the standing cut's first 512 windows only.

**Occasion.** The previous loop ([receipt](2026-09-29_THE_FACTOR_FAMILIES_CERTIFIED_STEP_TEXT_HOLDS_ITS_ENTRY_BOUND_THE_COPY_IS_EXACT_AND_THE_FACTOR_FAMILIES_BARELY_MOVE.md))
certified every family's step and measured that on the prediction field the factor families'
certified steps (`2⁻²³` to `2⁻⁷`) fall below their lattice units, so they barely move. Its cause, by
measurement: the curvature `C = B·½·κ²·b` multiplies three loose upper bounds, the Schur test on the
readout and on each family's moves, the count `B` (about 10) that charges every family as if all
stepped along the worst joint direction together, and the gain summed over every tick and station.

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
names what this loop could repeat:
- **failure 5, an uncertified step.** Loosening a bound must never loosen the certificate. Each
  tightening replaces an upper bound by a sharper one that is itself proved (§1, Lean
  `Holon/Deposition` §9). Each family keeps its own certificate `ηC ≤ a` and `ηc ≤ 1`, the storage
  growth is still certified by inertia or the deposit refused, and the joint certificate descends
  through `certified_step_descends`.
- **failure 9, a refusal answered with a larger limit.** A tighter proof is lawful, a larger limit
  is not. No limit moves: not `ηc ≤ 1`, not the storage search, not the entry bound `8`, not any
  run's bound (§2), which are fixed here before any run. No run is repeated.
- **lesson 3, a located cause repaired in its owner.** The cause stands in `hnn::constitution` and
  `holon::deposition` and is repaired there.
- **failure 7, bits read as progress.** The standing cut's held-out code is reported beside the
  runs, never as the loop's success; the acceptance is that the families move with every check
  holding.
- **failure 6, seen material graded as unseen.** The moiré's six windows are its training windows:
  its reading is stability, not transfer.

## 1. What is built (`dab65944`)

The readout commit `05efc278` counts, for every learned family, the deposits at which any of its
entries changed (a lattice coordinate moved), and the factor families that moved over the run.

The tightened certificate, in `hnn::constitution` (module header, "The tightened certificate") and
`holon::deposition`:
- **The joint moves, not the count `B`.** Each family keeps its own curvature `C = ½·κ²·b` (`B = 1`)
  and its own `ηC ≤ a`, `ηc ≤ 1`. The families' logit moves along the joint ray add, and their
  cross terms are bounded by Cauchy–Schwarz on the joint ray: with `m_ℓ = √(κ²_ℓ b_ℓ)` at its
  dyadic ceiling, the families together hold `½ (Σ η_ℓ m_ℓ)² ≤ Σ η_ℓ a_ℓ`. [agent-inferred] The
  steps start at each family's own certificate; while the joint one fails, the family whose halving
  gains it most, `½ η (s m (2 Σ η m − ½ η m) − a)`, is halved (the first in the deposit's order at a
  tie). Such a gain is positive for some family whenever the joint certificate fails, so the halving
  ends.
- **The readout's spectral bound, not its Schur test.** `‖R‖₂` and the norm of `R`'s unit step are
  read by their Gram certificate (`holon::deposition::spectral_norm`). The matrix is read on a
  dyadic face of 16 significant bits, `R = 2^e N + E` with `|E_ij| ≤ 2^(e−1)`, and the Gram of
  `N`'s smaller side is formed over the integers. A guessed `μ` (the Rayleigh quotient of power
  steps, raised by `2^(−6)`, `2^(−4)`, …) is taken only where exact inertia decides `μ I − G ⪰ 0`,
  so `‖R‖₂ ≤ 2^e(√μ + ½√(rows·columns))`. The Schur test stays the fallback. The readout at the
  receiving map's ray's end is `(‖R‖₂ + η‖D‖₂)²`.
- **Lean `Holon/Deposition` §9**, with `#print axioms` in `Framework/HolonObject` (propext,
  Classical.choice, Quot.sound only):
  - `joint_move_triangle`: `s‖Σ η_ℓ u_ℓ‖² ≤ s(Σ η_ℓ m_ℓ)²`;
  - `joint_step_descends`: the joint certificate descends by `½ Σ η a`, through
    `certified_step_descends` with the joint term apportioned by decrease;
  - `gram_certificate_bound` and `adjoint_gram_certificate_bound`: a certified Gram, of either
    side, bounds the map;
  - `entrywise_error_bound`: `‖E v‖² ≤ m n ε² ‖v‖²` for entries within `ε`.

Nothing is tuned to a terrain: the certificate reads no codec, alphabet, chart or terrain, and the
same `Constitution::deposited` runs on the moiré, the copy, text and the standing cut. The
computational object is the helical pair interaction:
- the contacts' storage and power, and the rings' elements, carry the factor families (the pair);
- the station readout's gain is the spectral bound (faces and placement);
- the words' ticks, re-entries and stations carry the refinement's span (the tube).

The helix, the cell holonomy and the tower thread stay attached through the field's complex.

## 2. The pins

The field, the refinement and the constitution are the previous loops' pins
([record](2026-09-29_THE_CERTIFIED_DEPOSITION_STEP_PINNED_BEFORE_ITS_RUNS.md) §2). Every step is
certified; nothing is authored for a terrain.

**Acceptance 1: every check on every run.** On every run below:
- the balances, pairings and commits each close on every refinement;
- every unreached locus is unchanged at every deposit;
- the committed energy bound holds at every refinement's commit;
- on the prediction field, every learned map's largest absolute entry over the run (`E`, `R`, each
  `W_c`, and the factor families `f`, the slices, `q`, `c`, `b`, `F`) is at most `8 = 2³`;
- on the standing cut, the exposure's tick and word balances close.

**Acceptance 2: the factor families move on text.** The run is `hnn_prediction -- develop text
.local/cuts/curated-u6-passage-cut.bin 385`: one pass over the U6 choosing role's 385 pairs (sha256
`c6e51a35…0816`), batch 16, training only. There is no generation and no validation read, it never
takes `--read-reserve`, and it never reads the evaluation window. It reports each family's certified
steps (the least and largest `k`) and the count of factor families whose entries moved over the run.
- The previous certificate's count is read the same way, once, by the readout commit's build
  (`05efc278`, the factor families' certified step with the count) on the same pairs.
- Of the 15 factor families of the prediction field, 7 lie in the refinement's diamond: ring 0's
  passive factor and slices, the standings `q₀` and `q₁`, and contact 0's `c`, `b`, `F`. The other
  8 are unreached, and acceptance 1 requires them unchanged.
- It **passes** when acceptance 1 holds and more factor families move than under the previous
  certificate.

**Acceptance 3: the standing cut's held-out code.** The run is `hnn_exposure -- cut-file
.local/cuts/u6-encoding-probe.bin cells all`: the residue chart on the host over the whole cut of
6,148 cells (sha256 `39621d52…7fbc`), held out 4,096..6,148. The held-out code at the field's face is
reported against:
- `5472 + 3/16 + ε`, both halves certified;
- `5462 + 4/16 + ε`, the linear half;
- `5459 + 13/16 + ε`, the old step.

The report gives counts, bits and hashes only.

**Acceptance 4: the moiré and the copy.** The runs are `hnn_prediction -- moire 4`, `-- moire 8` and
`-- copy` at the previous loops' pins: 512 training windows of the pinned moiré and its 6 windows
evaluated; 1,536 copy requests and 256 evaluated. They pass as before (6 of 6, 6 of 6, 256 of 256),
or the change is named by measurement.

**Acceptance 5.** No text is generated in this loop.

**Acceptance 6: projections.** Each run is projected below from a development read (§3). Each process
is bounded externally at its projection's upper end, and each harness keeps its own guards (training
stops at 540,000 ms or a 20 GB resident set). A run that reaches its bound is reported incomplete with
its partial evidence and is **not rerun with a larger bound**.

| Run | Development read (§3) | Projection | Bound |
|---|---|---|---|
| `develop text … 385`, this build | 96 pairs, 32,276 ms | 130,000–300,000 ms | 300,000 ms |
| `develop text … 385`, the previous certificate (`05efc278`) | 96 pairs, 27,717 ms | 110,000–170,000 ms | 170,000 ms |
| `moire 4` | 64 windows, 11,692 ms | 512 windows: 100,000–200,000 ms | 200,000 ms |
| `moire 8` | 64 windows, 25,654 ms | 210,000–400,000 ms | 400,000 ms |
| `copy` | 128 requests, 17,449 ms; 32 evaluations, 894 ms | 200,000–400,000 ms and below 10,000 ms | 420,000 ms |
| exposure | 512 windows, 74,565 ms | 3,074 windows: 480,000–780,000 ms | 780,000 ms |

[agent-inferred] Each projection scales its development read by the previous loop's full-to-read
ratio on the same run:
- text `4 + 1/2` (121,975 over 27,100 ms);
- the moiré `9` (101,650 over 10,953 ms; 209,183 over 23,078 ms);
- the copy `13` (182,605 over 13,944 ms);
- the exposure `6 + 1/2` (353,824 over 54,624 ms).

Each upper end allows for the cost growth that moving families bring: the words run on materials off
their founding values, and the storage certificate runs on every form that moves. Every peak resident
set is projected below 1,500,000,000 bytes; the development peaks are 306,880,512 to 569,565,184
bytes. The runs are sequential, on the host, in release. The GPU suite runs after them, alone on an
idle card under `flock .local/gpu.lock`.

## 3. The development reads (before the pins)

Each read closed every balance, pairing and commit, kept every unreached locus unchanged, and held the
committed energy bound at every refinement's commit. `k` is a certified step's exponent (the step
`2^k`). "Moved" counts the factor families whose entries changed over the read, of 15.

| Read | Training | Exact | `k`: `R` / `E` / `W_c` / factor families | Moved | Largest entry | `ε_k` / `∏(1+ε_k)` | Time, peak |
|---|---|---|---|---|---|---|---|
| text, choosing pairs, this build | 96 | (no evaluation) | 0 / −14..−11 / −10..−7 / −18..−5 | 6 (`f₀`, slices₀, `q₀`, `q₁`, `b₀`, `F₀`) | `R` 1997/2048; `q₀` 29/2048 | 0..1/16 / 142545/131072 | 32,276 ms, 569,565,184 bytes |
| text, choosing pairs, the previous certificate | 96 | (no evaluation) | −2..0 / −18..−16 / −15..−11 / −23..−10 | 0 | (not reread) | (not reread) | 27,717 ms, 560,828,416 bytes |
| moiré, `K = 4` | 64 | 6 of 6 | 0 / −13..−12 / −10..−7 / −17..−8 | 3 (`q₀`, `q₁`, `q₂`) | `R` 3607/2048 | 0 / 1 | 11,692 ms, 372,187,136 bytes |
| moiré, `K = 8` | 64 | 6 of 6 | 0 / −14..−13 / −9..−7 / −16..−8 | 0 | `R` 1873/2048 | 0 / 1 | 25,654 ms, 469,938,176 bytes |
| copy | 128 | 16 of 32 | 0 / −11..−10 / −8..−7 / −15..−6 | 3 (`f₀`, `q₀`, `q₁`) | `R` 585/256 | 0 / 1 | 17,449 ms, 306,880,512 bytes |
| exposure, the cut's first 512 windows | 512 | (no held-out) | 0..1 / −3..9 / 1..13 / −23..13 | (not read) | (not read) | 0..1/8 / between `2¹⁷` and `2¹⁸` | 74,565 ms, 332,095,488 bytes |

On the choosing pairs the two tightenings together raise the factor families' steps by about `2⁵`:
- the joint moves about `2³`: in the traced deposits the joint certificate held with each family
  within about one halving of its own curvature step (the count `B` had charged each about `2³`);
- the spectral readout about `2²`: `‖R‖₂² ≤ 2³` against the Schur test's `2⁵`, a readout of 514 rows
  and 64 columns.

The stations' sum is **not** loose on text. Read once in a development trace, the stacked Gram
`Σ_j P_jᵀ RᵀR P_j` over the 32 stations' rotations of the one anchor is within a factor 2 of
`m ‖R‖₂²` (both at most `2⁸` at the second deposit). So that bound stays.

Two risks are named before the runs:
- **The copy's development read fell to 16 of 32 exact**, where the previous certificate reads 32
  of 32 on the same development seeds. The factor families `f₀`, `q₀`, `q₁` and the contrast port
  `W_c` (`3/256`, against `1/2048`) now move, so the medium the receiving map reads changes under it.
  The pinned copy (1,536 requests) is reported as it comes: 256 of 256 or the change named.
- **The exposure's storage grows faster**: `ε_k` reached `1/8` in one deposit, and the product over
  512 windows lies between `2¹⁷` and `2¹⁸`, where the previous full run held between `2⁸` and `2⁹`
  over 3,072 deposits. Every growth is certified at its commit; the bound is enforced, and looser.
