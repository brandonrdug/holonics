# Runs of the binding bank receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `binding_bank.py` | A: the harmonic box's kernel `K(d) = Σ_(n<16) ζ₃₂^(nd)` at all 32 differences; B: 16 grid bindings read back, then a 17th on a used key, additive and delta; C: an off-grid key's leak into four grid reads against `2v/(16(1 − ζ^d))`; D: recurrent against chunk form (delta write, gate, decay) on 12 cells and five partitions; E: an antecedent-clocked bank with hand-set keys over a repeated six-class word and over `1 2 1 3`; F: the MQAR terrain's first passage, the held-out set's SHA-256 and a disjointness check | under 2 s, from a development run (1.0 s) | 60 s | 1.4 s | 15,884 KiB |

`binding_bank.py`: exit 0, `all checks hold`. Output `binding_bank.txt` (one block per part, each with its elapsed
milliseconds). Script SHA-256 `e6b078d6e892552edba31d32a9f1b7a4747529cde38f8bf2cdda47225c9ae801`; output SHA-256
`79141b1bb34f8356f53c6e1a6d1e8786d75adcbc4153efdd19e16716c7e18d37` (the elapsed milliseconds differ between runs;
every other field is deterministic). Exact arithmetic only: `fractions.Fraction` coefficients in `ℚ(ζ₃₂) = ℚ[x]/(x¹⁶ + 1)`
and SHA-256 for the terrain's shuffles, no float anywhere. No private data. Measured to projected wall: 1.4 s against 2 s.

Development, before this run:
- C first failed: the leak's difference was written `3 − a`; the read at `a` of a key at 3 is `K(a − 3)/16`, and the
  check now uses it.
- F's first generator built keys and values as arithmetic progressions modulo 64. A passage's value was then an affine
  function of its key, readable from two pairs without binding, and key 0 met only 8 value classes across the held-out
  set. It now shuffles by SHA-256 of the passage index (key 0 meets 63 value classes).
- Each part was then broken on purpose in a scratch copy, and each broken copy failed: the delta's read not subtracted
  (B), the read scaled by `1/15` (B), the chunk form's decay span shifted by one cell (D), the write's phase not
  conjugated (B), and the key taken from the arrival instead of its antecedent (E).
