# The guarded witness measured: the modulus's sign turned, the modulus stayed, and the guard refused move six

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] under the
[pin](2026-10-01_THE_GUARDED_WITNESS_PINNED_BEFORE_ITS_RUN.md) (source `35a81746`); [agent-inferred]
where marked. Receipts: [`2026-10-01_THE_GUARDED_WITNESS_receipts/`](2026-10-01_THE_GUARDED_WITNESS_receipts/)
(listing, identities, stderr, the continuing states `c0` to `c6`).

## 1. The outcome: G3, after six adopted moves

| Constitution | `ρ` (`/2^21`) | `L` own (`/4096` nats) | Solved, right, whole | `γ_ρ` sign | The move |
|---|---|---|---|---|---|
| 0 (founded opening) | 1645392 | `[500197, …)` | 0, 15, 0 | − | adopted at `1/4` (`1/2` refused `OwnNotBelow`) |
| 1 | 1646019 | `[495388, …)` | 4, 15, 0 | − | adopted at `1/2` |
| 2 | 1650704 | `[449099, …)` | 2, 16, 0 | + | adopted at `2` |
| 3 | 1642694 | `[435719, …)` | 3, 16, 0 | − | adopted at `1` |
| 4 | 1652819 | `[393284, …)` | 0, 13, 0 | + | adopted at `1` (`8`, `4` refused `NotBelow`, `2` `OwnNotBelow`) |
| 5 | 1649544 | `[384239, …)` | 0, 18, 0 | + | adopted at `2` (`8` `NotBelow`, `4` `OwnNotBelow`) |
| 6 | 1642461 | `[373776, …)` | 2, 15, 0 | + | **refused at all 8 trials** (`4` `NotBelow`, `2` to `1/32` `OwnNotBelow`) |

- **G1 fails.** `γ_ρ > 0` at constitutions 2, 4, 5 and 6, which gate A never reached, but stations
  right reach at most 18 (≤ 24) and no section is whole.
- **G2 holds in part.** The executed `L` falls strictly at every adopted move, as the guard
  enforces, from `[500197/4096, …)` to `[373776/4096, …)`, and decisions do not follow. But `γ_ρ`
  does not stay negative.
- **G3 holds.** Move 6 is refused by the guards at every step of its ladder: the executed descent
  along the native direction ends within 8 halvings at constitution 6.

## 2. What the modulus did

The sign obstruction the segment probe named is gone: from constitution 2 on, the comparison asks
for the lower transport, and `ρ` moved toward the refit's `ρ* = 1100584/2^21` at every such move
(`−8010`, `−3275` and `−7083`, in units of `2^(−21)`). The scale obstruction stands. `ρ` stayed in
`[1642461, 1652819]/2^21`, and its largest step toward `ρ*` was `8010/2^21` against a remaining
gap of `541877/2^21`. The executed descent was spent on `E`: `L` fell by `126421/4096` nats while
the refit's `L` at `ρ*` reads `[133292/4096, …)`.

[agent-inferred] The modulus's step is `−γ_ρ/G_ρ` with `G_ρ = Σ|∂z/∂ρ|²`, the storage coordinates'
own form, while `E`'s step carries the normal law's accumulated feature Gram: the move is measured
by two witnesses, one of them no receiver. The next record derives the move's metric from its one
witness ([the move's metric](2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md)).

## 3. Time and resources

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| 8 moves at 19 threads (`timeout 7021`) | 7,020,328 ms | 6,974,736 ms (the witness's own) | 1,564,001 ms, exit 0, no early stop | 203,182,080 bytes |

Measured over projected: `1564001/7020328`. The longest move, move 6 with all 8 trials, took
440,346 ms, below the per-move bound of 871,842 ms.
