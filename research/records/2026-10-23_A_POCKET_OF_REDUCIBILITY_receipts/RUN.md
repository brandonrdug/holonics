# Run receipt

Host: the session's cloud container, one thread, Python 3, exact integer arithmetic.

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `eca_binding.py` | the normal-form degree and threshold test of all 256 elementary rules; the count of ones on every cyclic configuration of length 1 to 12 under every rule; rule 90's `2ᵏ`-step jump on every cyclic configuration of length 16, `k ≤ 3` | unmeasured, planned under 1 min | 120 s | 2,329 ms | 12,436 KiB |

The first run (713 ms, 11,028 KiB, 60 s deadline) held only the degree and threshold test; the
conservation and jump checks were added after it, and the committed output is the full run. The
threshold search covers integer weights in −3..3 and thresholds in −4..4, which realizes every
threshold function of three inputs (104, the known count).
