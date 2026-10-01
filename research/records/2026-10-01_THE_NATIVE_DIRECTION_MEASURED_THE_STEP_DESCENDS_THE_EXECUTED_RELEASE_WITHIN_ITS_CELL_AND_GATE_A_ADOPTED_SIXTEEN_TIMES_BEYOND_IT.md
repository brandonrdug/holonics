# The native direction measured: the step descends the executed release within its cell, and gate A adopted sixteen times beyond it

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_NATIVE_DIRECTION_PINNED_BEFORE_ITS_RUN.md) (`caa4f49e`); [agent-inferred]
where marked. Read-only.

## 1. The unit step at the founded opening

On gate A's batch, under the lock face at the decisions, at `Θ₀`:
- **`ΔE`** (the move's step through the normal law's solved chart, largest entry `602475/1048576`)
  pairs **positively** with the route `E* − E₀`, with squared cosine in `[3/4096, 4/4096)`.
- **`G`** (the plain pullback of the same returns) pairs positively too, with squared cosine in
  `[2/4096, 3/4096)`.
- **`Δρ`** lies in `[2506/2097152, 2507/2097152)`, with `γ_ρ` in `[−332395/4096, …)`, as the slope
  record read.

Both directions are **nearly orthogonal** to the descending route, and the chart barely changes
that. The composition's covector at the opening points almost entirely elsewhere, with a small
positive component along the route. By the pin's rules this is not outcome (A).

## 2. The executed release along the step

| `η` | `ρ` (`/2^21`) | `L` (nats) | Solved, right, whole | First locks (station, right `+` or wrong `−`) |
|---|---|---|---|---|
| 0 (the opening) | 1645392 | `[500197/4096, 500203/4096)` | 0, 15, 0 | 6− and 7− (as below) |
| `1/512` | 1645396 | `[499045/4096, 499051/4096)` | 0, 15, 0 | 7− 7− 6− 6− 7− 7− 7− 6− |
| `1/128` | 1645411 | `[495755/4096, 495760/4096)` | 0, 15, 0 | 7− 7− 6− 6− 7− 7− 7− 6− |
| `1/32` | 1645470 | `[481210/4096, 481215/4096)` | 0, 16, 0 | 7− 7− 6− 6− 7− 7− 7− 6− |
| `1/8` | 1645705 | `[486059/4096, 486065/4096)` | 0, 14, 0 | 5− 7− 7− 6+ 6+ 7+ 3+ 5− |
| `1/2` | 1646645 | `[517183/4096, 517189/4096)` | 7, 16, 0 | 7− 7− 7− 7− 7− 7+ 7+ 7− (gate A's constitution 1) |

- **The trajectory cell.** Up to `η = 1/32`, every request's release keeps the opening's
  trajectory: the same first locks, 56 terms held. Within the cell the own `L` falls in proportion
  to `η`. The drops below the opening, `1152`, `4442` and `18987` (`/4096`) at `1/512`, `1/128` and
  `1/32`, are each between `568000` and `608000` (`/4096`) per unit `η`: the first order holds.
- **Past the cell**, at `1/8`, the trajectory changes. Four first locks come right, and `L` still
  lies below the opening's, but above `1/32`'s.
- **At gate A's adopted `η = 1/2`**, the release moves to the far-end, class-3 trajectory, and `L`
  rises above the opening's. The read reproduces gate A's constitution 1: `ρ` exactly, `L` within
  the lattice carry (`[517183/4096, …)` against `[517184/4096, …)`).

**Outcome (B) holds.** The direction pairs positively with the route. The own `L` at `η = 1/2` is
not below the opening's, and at `1/8`, `1/32`, `1/128` and `1/512` it is. The ladder adopted a step
sixteen times past the trajectory cell. Its certified decrease was of the fixed mask, while the
release it executes rose.

## 3. What this locates, and the law it motivates [agent-inferred]

- **The blocker, by its measurement.** Gate A's first committed move certified a decrease of the
  fixed mask at `η = 1/2`, while the executed release's `L` rose from `[500197/4096, …)` to
  `[517184/4096, …)`. Along the same unit step, `η = 1/32` lowers the executed `L` to
  `[481210/4096, …)` on the unchanged trajectory.
  - This is 1a's #62 item 5, "the first order across a trajectory change", now measured.
  - Gate A's own receipt carried it from the start: the timing move's own release rose by a context
    change of `[39322/4096, 39332/4096)` while the mask fell by `[36377/4096, 36387/4096)`.
- **The law it motivates.** The committed move adopts a successor only when the composition the
  release executes also falls: `C_own(Θ′)⁺ < C(Θ)⁻` by disjoint enclosures, beside the fixed mask's
  certified decrease.
  - The successor's own release is already read at every trial, so the guard costs no reading.
  - Within the cell, the mask and the own release coincide and the guard is redundant. Past it, the
    move may leave the cell only while the executed comparison still descends.
  - It is the descent of a declared receiving composition that the learning-failure diagnosis kept
    (its §4): what the release executes, not only its linearization.
  - Over moves on a fixed batch, the executed `L` then falls strictly at every adopted move.
- **What it leaves open.** The covector at the opening is nearly orthogonal to the descending
  route. Whether repeated own-descending moves reach the region where the modulus's slope turns
  down, or settle in the class preference by another path, is the guarded witness's question.

## 4. Time and memory

| Read | Measured | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| the unit step and 5 own-release reads at 19 threads | 262,876 ms (launcher), 262,495 ms (harness) | 382,731 ms / `timeout 383` | 185,995,264 |

- **Per line**: the unit step 41,432 ms, then 39,962, 42,037, 44,140, 46,329 and 48,537 ms. Each is
  below the per-line bound of 154,771 ms. Measured against projected: `262876/382731`.
- **Identities**: source `caa4f49e`; binary sha256
  `b8c837c33ee6059ee9799ae1d446959b8bbbc0e56d30230c1bbb126e1300f46d`.
- **Gates**: `cargo check --workspace --all-targets` clean; the move's tests after the factoring,
  `hnn::tests::lock_face` and `hnn::tests::prediction`, 25 passed in release (36,940 ms).

The receipts (`2026-10-01_THE_NATIVE_DIRECTION_receipts/`, synthetic terrain only) are
`listing.txt`, `stderr.txt`, `identities.txt`, and each step's successor (`eta-0.txt` to
`eta-4.txt`, `E` and `ρ`).
