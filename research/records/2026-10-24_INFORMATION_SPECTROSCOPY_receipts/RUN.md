# Run receipt

Host: the session's cloud container, one thread, Python 3, exact fractions, Gaussian rationals and
cyclotomic fields (no floating point).

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `spectroscopy.py` | A: first-order line shifts of a two-site Rayleigh-damped constitution under mass, viscosity and stiffness loads, and their kinds on the lossless lines; B: the clock gauge, the lossless mass–clock equivalence, the loss invariants with the viscosity held, the first-order ratio moves; C: the Cayley chart conjugating the clock to the disk boost; D: the basin's group delay as the Poisson kernel and the Doppler factor; E: the ring sum over the `N`-th roots of unity for `N = 1..12` and four basins in `Q(ζ_M)`; F: disk motions keep the count and the pseudo-hyperbolic distances; G: the minimum-phase and all-pass split, the two series through their exact aliasing, the delay totals; H: the receiver's mass along a reading | unmeasured, planned under 1 min (2 × 2 pencils, cyclotomic fields of degree at most 20) | 60 s | 565 ms (523 ms inside the script) | 13,948 KiB |

It ran to completion inside its deadline. No private data. The output is `spectroscopy.json`.
