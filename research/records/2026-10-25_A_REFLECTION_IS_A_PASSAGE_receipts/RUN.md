# Runs of the reflection-passage receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `reflection_passage.py` | A: the mirror `R_k(u, v) = (v/k², k²u)` for six rational `k` on 51 events (involution, interval, pairing, worldline, future cone, null axes, radar `t₂ = k²t₁`); B: the returned frequency `ω/k²`; C: two mirrors against `boost_((k₁/k₂)²)`, two Euclidean reflections against a turn; D: the box with one receding wall, 40 bounces each for `β = 1/3, 1/7, 2/5, −1/3`; E: the reactive wall over `ℚ(i)` | under 1 s, from a development run (0.06 s) | 60 s | 0.1 s | 11,200 KiB |

`reflection_passage.py`: exit 0, `fail []`. Output `reflection_passage.txt` (9 lines, one per part, each with its elapsed
milliseconds), SHA-256 `00323972a3f1569065e138a0c11995c4645af21b585dc6c588a379a32163969f`; script SHA-256
`895bbf8c8067829884d0b1d711101bafd9d1329de71dd4a43b642720259201f1`. Rationals only (`fractions.Fraction`), no float
anywhere. The elapsed milliseconds differ between runs; every other field is deterministic. Its development run printed the
last wall position of D as a float; that print was replaced by the exact check `L_last = L_first · ((1 + β)/(1 − β))³⁹`,
which D's verdict now includes. No private data.
