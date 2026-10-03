# The corrected throw chain, relaunched from m1 (m2 to m15)

**Build.** `5f254c2d` (the throw's power read on the whole move) with four print-only and
script-only cherry-picks, `7a650e6b fc4ca0f3 55a99bd8 cd8f654f` (local HEAD `82dcb53`; binary sha256
`f67254e7be794c891f39da3e5debb9a45ac44b22a34bc09e54249d55ebaf2878`), and `run.sh` at `aa9f0fc7`.
Started from `../m1/m1-throw.state` and its flight (sha256 `d29465f16f15b063…`, `fc7d9f8d0a125c8f…`),
`FIRST_MOVE=2`, 4 threads, alone in its container. Launched 23:48:39 UTC, October 2.

**The first launch's projection error.** The first launch (`../m0` to `../m2`) held each move to
1349692 ms, a bound fitted from two moves (m0 at rest, m1 with its first coast). It was not a measured
upper time. m2 passed it by whole rereads: a single trial's reread is 151812 to 206634 ms, and m2 ran
seven trials (`../diag-m2/`). That launch's receipt stands: m2 incomplete at its deadline.

**The new unit and bounds.** Each unit kind of an executed move is bounded on its own, at 3 times its
largest wall-stamped gap measured in the m2 diagnostic on this host:

| kind | largest gap (ms) | bound (ms) |
|---|---|---|
| incumbent (from process start) | 166264 | 498792 |
| proposal and persistence | 1814 | 5442 |
| returns, slope, first step, whole-move power | 32691 | 98073 |
| a trial's deposit or reread | 209825 | 629475 |

The per-move guard is G = 498792 + 5442 + 98073 + 8·629475 = 5638107 ms (deadline 5639 s), and the
outer timeout is 14·G = 78933498 ms (78934 s) for m2 to m15. The bounds are fixed at launch: a unit
past its bound stops the chain, reported incomplete, and it is not relaunched with a larger bound.

**Like-for-like check.** This launch's m2 must reproduce the diagnostic's m2 byte for byte: state
sha256 `8d3f54c545237293…`, flight `9eb79b1148b003c5…`.
