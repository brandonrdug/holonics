# Runs of the diffusion and keys receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `diffusion_keys.py` | A: the twisted cycle `C_n` with a `ℤ_4` connection turned by one contact, `n = 2, 4, 8, 16`, every eigenvector checked in `ℚ(ζ_(4n))`, labellings brute-forced to `n = 8`, the Fejér identity; B: plain relaxation against critically tuned momentum on a path of 33 vertices (`H = aI + BᵀB`, `a = 4/(m² − 1)`) at `κ ≤ 9, 25, 81, 289`, and the cone (`t` passes reach exactly `t` hops); C: a unique game over `S₃` on the Petersen graph at value 1 and with one contact corrupted, loop closure, brute force over `3¹⁰` and syndrome location; D: two flat `K4` blocks over `ℤ₃` joined by two conflicting contacts, their optimal labellings, gauge, landmark and two slow modes; E: gradient play on `f = xy`, simultaneous, alternating and with friction; F: the least certifiable relative drop at `N = 10³, 10⁴, 10⁵`, `|P| = 2¹⁰` | unmeasured before the first run, so planned at one to three minutes | 180 s (first run), 60 s (final run, from the first run's 15.0 s) | 14.6 s | 18,304 KiB |

`diffusion_keys.py`: exit 0, `all 394 checks hold`. Output `diffusion_keys.txt` (one block per part, each with its
elapsed milliseconds). Script SHA-256 `a9f3242c148d0664c6e0376438e578a8bd5040e732eab3591e4e4bf2b00f5040`; output
SHA-256 `f4a208f67fcf9f0bc6dd130a5c3dfbb775d5805bb5bbe509cfd4223ddac703a3` (the elapsed milliseconds differ between
runs; every other field is deterministic). Exact arithmetic only: `fractions.Fraction`, integers, and `ℚ(ζ_N)` for `N` a
power of two as `ℚ[x]/(x^(N/2) + 1)`; the decimal figures in the output are printed readings beside exact values and
enter no check. No private data. Run as `timeout 60 python3 -I` through `runpy`, the peak read by
`resource.getrusage` (`/usr/bin/time` is not installed here). Measured to projected wall: 14.6 s against 60 s on the
final run; the first run took 15.0 s and 18,432 KiB against its 180 s deadline.

Development, before the final run:
- An unused dictionary of float readings in part A was removed, so no float is built anywhere.
- The record's statement 3 first said that heat flow changes no holonomy. That is true of relaxing the potential (a
  gauge move: an exact cochain integrates to zero round every cycle) and false of friction on the faces (the Hodge heat
  flow changes the circulation round a face-bounding cycle while keeping the harmonic part). The statement now names
  the two separately.
