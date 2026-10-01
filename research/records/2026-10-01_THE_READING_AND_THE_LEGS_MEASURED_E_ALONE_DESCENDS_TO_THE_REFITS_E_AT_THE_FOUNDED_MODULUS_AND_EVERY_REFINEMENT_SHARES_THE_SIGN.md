# The reading and the legs measured: `E` alone descends to the refit's `E` at the founded modulus, and every refinement shares the sign

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_READING_AND_THE_LEGS_PINNED_BEFORE_THEIR_RUN.md) (`000acd2c`); the reading's
second constitution is incomplete. [agent-inferred] where marked. Read-only.

## 1. The legs, under gate A's comparison (Y)

Gate A's batch and comparison (the lock face at the decisions):

| Point | `ρ` | `L` (nats) | Solved, right of 64, whole | `γ_ρ` (`/4096`) | Unit move (`/2^21`) |
|---|---|---|---|---|---|
| `Θ₀` (the opening; the slope record) | `ρ₀` | `[500197/4096, …)` | 0, 15, 0 | `[−332395, …)` | `+2506` |
| `E`-leg `s = 1/4` | `ρ₀` | `[459530/4096, 459535/4096)` | 0, 12, 0 | `[+346375, …)` | `[−2705, −2704)` |
| `E`-leg `s = 1/2` | `ρ₀` | `[413154/4096, 413159/4096)` | 0, 18, 0 | `[+661253, …)` | `[−4689, −4688)` |
| `E`-leg `s = 3/4` | `ρ₀` | `[361399/4096, 361404/4096)` | 6, 17, 1 | `[+928496, …)` | `[−6334, −6333)` |
| `(E*, ρ₀)` (both prior records) | `ρ₀` | `[310210/4096, …)` | 15, 22, 0 | `[+1617648, …)` | `−9692` |
| `ρ`-leg `t = 1/2` | `1372988/2^21` | `[180720/4096, 180723/4096)` | 33, 42, 1 | `[+431542, …)` | `[−8782, −8781)` |
| `Θ*` (the refit) | `ρ*` | `[133292/4096, …)` | 45, 55, 5 | `[+65333, …)` | `−1904` |

- **Both legs descend strictly**, each point below the last by disjoint enclosures. At the founded
  modulus, a descent in `E` alone goes from the opening to the refit's `E`, ending below every
  constitution gate A's moves reached. A descent in `ρ` alone then reaches the working constitution.
- **On the `E`-leg the comparison asks for the lower transport from its first quarter on**, and asks
  harder as `E` approaches `E*`. Gate A's own constitutions 1 and 2 kept it asking for the higher
  one.
- So gate A's failure is located in **`E`'s path at the founded modulus**. A strictly descending
  `E`-only route from the opening exists, and on it the modulus's slope turns within the first
  quarter. Gate A's `E` moves did not take it: its first adopted move raised the own release's `L`
  to `[517184/4096, …)` and locked class 3 everywhere.

## 2. The reading, under every refinement (X): incomplete, and decided by its first read

- `lock-all` at the opening: `L ∈ [2180496/4096, 2180516/4096)` over 285 terms, 2 solved,
  `γ_ρ ∈ [−551096/4096, −551095/4096)`, unit move `[+2062, +2063)/2^21`. **Negative**: under every
  refinement as well, the comparison at the opening asks for the higher transport.
- **By the pin's rule** (negative at either constitution), both readings share the sign obstruction,
  and the decisions reading is not its cause. Gate B's `lock-all` arm would not escape it.
- **Incomplete.** The read took 440,159 ms against the derived unit bound of 374,720 ms (the
  covector-count ratio under-projected it: `440159/374720`).
  - The launcher printed the read's line and then stopped the run before constitution 1, which was
    not read.
  - The launcher checked only finished lines, so the read ran past its bound before the stop. It is
    corrected in this commit (`read_probe.sh`) to stop a read in progress once the unit bound
    passes since the last line.

## 3. What this locates, and the next loop [agent-inferred]

**The blocker, by its measurement.** From the founded opening, a strictly descending `E`-only route
to the refit's `E` exists under gate A's comparison. Along it the modulus's slope turns down within
a quarter, and the following `ρ`-only route descends strictly to a constitution that releases 5 of
8 sections whole. Gate A's certified `E` moves took another direction: their constitutions keep the
modulus's slope up, and their best decisions are a class preference.

**The next loop** is the native move's direction at the opening, against this route. Read-only, it
would read:
- the move's unit step `(ΔE, Δρ)` as `executed_move` forms it (the decisions' covectors through the
  normal law's chart);
- its alignment with `E* − E₀` (the inner product's sign and its squared cosine, exactly);
- the own release's `L` along it at a ladder of steps.

It separates a direction that points away from the route (then the composition's covector or the
normal law's chart is the subject) from one that points along it but whose step overshoots into
another release trajectory (then the ladder's start, bounded by the trajectory cell where the fixed
mask equals the own release, is the subject).

## 4. Time and memory

| Read | Measured | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| the legs, 4 points at 19 threads | 273,859 ms (launcher), 273,403 ms (harness) | 333,084 ms / `timeout 334` | 148,844,544 |
| the reading, `lock-all`, 2 constitutions | stopped after the first: 441,181 ms; the first read 440,159 ms | 749,440 ms / `timeout 750`; unit bound 374,720 ms | not printed (stopped) |

- The legs per point: 64,288, 63,554, 67,663 and 77,855 ms. Measured against projected:
  `273859/333084`.
- Identities: source `000acd2c`; binary sha256
  `6458807bc93f0a1112d75d08b799694600115d3b4ce4c8385328e86d3639a09b` (the binary of the slope
  record, unchanged).

The receipts are in `2026-10-01_THE_READING_AND_THE_LEGS_receipts/{legs,all}/`: the listing, stderr
and identities of each read.
