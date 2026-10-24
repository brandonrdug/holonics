# Run receipt

Host: the session's cloud container, one thread, Python 3, exact fractions.

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `tension.py` | A: the joint Gram, its Schur complement and the least residual on six cells of a three-class comparison; B: two merged cells; C: eight line starts of two media under one face, three candidate faces, the code at the optima; D: one complex readout row, two arrivals, a turned row; E: a rebase of the face | unmeasured, planned under 1 min | 120 s | 33 ms | 11,984 KiB |
| `closure.py` | A: `tr T` against the aligned friction on every binary pair of length 4, a late release; B: `det S / det S₀` and the canonical correlations on `tension.py`'s data A and C; C: the grain, the order, and every pair of strands of 2 classes to length 8, 3 to length 5 and 4 to length 4 (`λ`, chance coupling, couplings that pay) | 0.64 s: 7,849,491 sweep cells at a measured 81 ns per cell; upper end 1.9 s, three times that for the per-pair work | 60 s | 829 ms | 12,132 KiB |
| `pool.py` | F1: a product of two signs against additive faces; F2: every ±1 pattern of the eight line starts as a candidate face, its drop and code saving, and the 14 square-wave clocks; F3: a pool of two correlated coordinates, its generalized eigenvalues and combinations | under 1 s (128 patterns of 3 × 3 exact solves) | 60 s | 76 ms | 11,864 KiB |

All three ran to completion inside their deadlines; `closure.py` took 1.3 times the sweep projection and 0.44 of its upper end. No private data. The outputs are `tension.json`, `closure.json` and `pool.json`.
