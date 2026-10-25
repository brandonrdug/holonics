# Runs of the reflection-passage receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `reflection_passage.py` | A: the mirror `R_k(u, v) = (v/k², k²u)` for six rational `k` on 51 events (involution, interval, pairing, worldline, future cone, null axes, radar `t₂ = k²t₁`); B: the returned frequency `ω/k²`; C: two mirrors against `boost_((k₁/k₂)²)`, two Euclidean reflections against a turn; D: the box with one receding wall, 40 bounces each for `β = 1/3, 1/7, 2/5, −1/3`; E: the reactive wall over `ℚ(i)` | under 1 s, from a development run (0.06 s) | 60 s | 0.1 s | 11,200 KiB |

`reflection_passage.py`: exit 0, `fail []`. Output `reflection_passage.txt` (9 lines, one per part, each with its elapsed
milliseconds), SHA-256 `11042e28c97af7513f560e3447d5b963755cd709b60d6d0529a6979e8e8cde3a`; script SHA-256
`57b85720aad0efad2993c5e07b4ba3d403ad6700c56cbc7d53b74cfd8a8fd845`. Rationals only (`fractions.Fraction`), no float
anywhere. The elapsed milliseconds differ between runs; every other field is deterministic. Its development run printed the
last wall position of D as a float; that print was replaced by the exact check `L_last = L_first · ((1 + β)/(1 − β))³⁹`,
which D's verdict now includes. No private data.

October 25, later: E's delay at `x = 0` is now computed from the logarithmic derivative (it was printed as a literal
`2`), from the integration thread's review of PR #469. Rerun: exit 0, `fail []`, 0.1 s, 11,224 KiB; the hashes
above are the rerun's.
