# The witness's direction in the span of the requests' pullbacks: a deeper fall, the same decisions

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for §1; [measured], read-only, for §2. Receipts:
[`2026-10-01_THE_WITNESSS_SPAN_receipts/`](2026-10-01_THE_WITNESSS_SPAN_receipts/).

## 1. The span

[The stiffness in ρ](2026-10-01_THE_STIFFNESS_IN_RHO.md) named `E`'s direction as the choice of
valley. That direction is the source port's normal law, measured by the port's retained Gram, not by
the witness. The witness's form generalizes from the plane to any span, since the library pieces
(`softmax_jacobian`, `SymmetricForm::{direct_sum, pullback}`, `inertia`) do not fix a dimension
(`PlaneTerm::along` and `WitnessForm::gradient` are now vectors).

`E` changes only along covectors that reached it, so its directions are the returns' own.
- **One direction a return**, `g_k f_kᵀ`. This was too wide: 85 directions on 2 requests, a form
  with a six-dimensional kernel, and 2,154,876,928 bytes resident.
- **One direction a request**, `D_r = Σ_t w_t g_t f_tᵀ` over the returns that request's
  contributions make alone. The witness weighs the requests against each other by its own measure,
  plus `ρ` (`hnn::executed::witness_span`).

## 2. At the founded opening, 8 requests, the lock face at the decisions

- The span (8 requests and `ρ`) is positive definite: inertia 9, 0, 0.
- **Alignment with the route.** The witness's `E` move has squared cosine `14180265/2^31` with the
  route to the refit's `E`, against `16185495/2^34` for the port's unit move: about seven times
  more, and still nearly orthogonal. A specific refit is one gauge among many, so this test is
  weak.
- **`ρ` moves `9213081/2^26` of the chord**, more than a tenth of the way, against `12487475/2^30`
  on the plane at the same state.
- **The step's effect:**

| The span's step | `ρ` (`/2^21`) | `L` (`/4096` nats) | Solved | Stations right | Released |
|---|---|---|---|---|---|
| none (the opening) | 1645392 | `[500197, …)` | 0 | 15 | 7 |
| × 1 | 1570597 | `[476738, …)` | 6 | 15 | 8 |
| × 1/2 | 1607994 | `[439805, …)` | 0 | 15 | 8 |
| × 1/4 | 1626693 | `[438523, …)` | 0 | 12 | 6 |

The Gauss–Newton model predicts `−5662175/2^17` nats. Half the step falls further, by `60392/4096`.
Against it, gate A's first move raised `L` to `[517184/4096, …)`, and the guarded witness's first
move lowered it only to `[495388/4096, …)`.

[agent-inferred] The witness's span direction descends the comparison far more deeply than any
earlier move, and moves `ρ` a real fraction of the way. The decisions do not follow: stations right
stay at 15 or fall. This is the third reading in which the comparison falls while the decisions do
not, after the order's stall and the chord's rise. **The binding problem is now the comparison's
agreement with the decisions, not the step.** The move under this direction (each request's returns
weighted by the witness, deposited by the normal law) is not built; it would descend a comparison
that does not yet lead to decisions.

## 3. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| development, one direction a return, 2 requests | (development read) | `timeout 300` | 283,989 ms | 2,154,876,928 bytes |
| development, one direction a request, 2 requests | (development read) | `timeout 300` | 28,859 ms | 176,615,424 bytes |
| the opening, 8 requests, the span and three reads | `115,436 + 3 · 48,927 = 262,217` ms | `timeout 263` | 214,135 ms, exit 0 | 478,838,784 bytes |

Measured over projected: `214135/262217`.
