# The native direction at the founded opening, against the descending `E` route (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the question, the reads and the rules; [measured] only in the receipt.
Read-only. The library change factors the committed move's unit step into one function
(`hnn::executed::unit_step`), now read by `executed_move` and by a read-only diagnostic
(`unit_direction`, which also returns the plain pullback of the same returns). The move's behaviour
is unchanged, and its tests are rerun.

## 1. The question

[The legs](2026-10-01_THE_READING_AND_THE_LEGS_MEASURED_E_ALONE_DESCENDS_TO_THE_REFITS_E_AT_THE_FOUNDED_MODULUS_AND_EVERY_REFINEMENT_SHARES_THE_SIGN.md)
measured the following. At the founded `ρ₀`, `E₀ + s(E* − E₀)` descends strictly in gate A's
comparison from the opening to the refit's `E`, and the modulus's slope turns down within its first
quarter. Gate A's first move went elsewhere: at `η = 1/2` its own release's `L` rose from
`[500197/4096, …)` to `[517184/4096, …)`, and it locked class 3 everywhere.

At the opening `Θ₀`, this read takes the move's own unit step `ΔE` (the decisions' covectors carried
to `E` through the normal law's solved chart), the plain pullback `G` of the same returns (the step
with the chart replaced by the identity), and `Δρ`. It reports each step's alignment with the route
`E* − E₀`, then reads the own release along `(E₀ + ηΔE, ρ₀ + ηΔρ)` for
`η = 1/2, 1/8, 1/32, 1/128, 1/512`, with `ρ` floored onto the lattice.

## 2. The outcome rules, fixed before the run

- **(A) the direction points away from the route**: `⟨ΔE, E* − E₀⟩ ≤ 0`.
  - If `⟨G, E* − E₀⟩ > 0`, the solved chart turns the covector away, so the normal law's chart is
    the next subject.
  - If `⟨G, E* − E₀⟩ ≤ 0` as well, the composition's covector at the opening points away, so the
    covector is the next subject: which terms carry it, for example the 56 terms held at `r*`
    behind a wrong far-end first lock.
- **(B) along the route, and the step overshoots**: `⟨ΔE, E* − E₀⟩ > 0`, the own `L` at `η = 1/2`
  is not below the opening's by disjoint enclosures, and the own `L` at some smaller `η` is. The
  ladder's start is then the subject. The first-order certificate holds only within the trajectory
  cell, where the fixed mask equals the own release, so a start bounded by that cell is derived
  next.
- **(C) along the route, and no step read descends the own release**: `⟨ΔE, E* − E₀⟩ > 0`, and no
  `η` reads the own `L` below the opening's. The own release changes trajectory at every step read,
  so the cell is smaller than `1/512` of the unit step, and the trajectory's discontinuity itself is
  the subject.
- **The caveat.** `E*` is one working constitution. A direction could head for an equivalent one
  (a gauge of `E`) and pair weakly with this route. So the pairing is a test against this route only.
  The own release along `ΔE` and its counts carry no gauge.

## 3. Time, threads and the stopping rule

- The first line (the unit step) contains an incumbent read with every decision term's covectors,
  the proposal, the returns, the normal law's prepared step and the modulus's normal reading. Gate
  A's whole move contains all of these, at 154,771 ms (loop 1c's `cost_move_12`, 12 threads).
- The next five lines are own-release reads, each at most 45,592 ms (constitution 1's read at 12
  threads).
- The launcher holds one per-line bound, the larger: 154,771 ms. The deadline is
  `154,771 + 5 · 45,592 = 382,731` ms, so `timeout 383`.
- `RAYON_NUM_THREADS=19`, beside nothing else, launched with
  `read_probe.sh <out> 154771 383 executed direction order2 2026093061 8 lock-dec opening <refit>@102837/131072 <out> 1/2 1/8 1/32 1/128 1/512`.
- **The failures this could repeat**: 9 (a fixed deadline), 7 (no count is progress), 3 (no
  consumer is built: the factored step has one law and two readers).
