# Run receipt

Host: the session's cloud container, one thread, Python 3 (`python3 -I`), integers and residues only.

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `closure_torsion.py` | A: base 10, 10,000 two-place sums, rank, minors' gcd, torsion; B: the eleven key on every true line and 595,040 false lines; C: the units key, `c mod 110` and the length bit; D: the two halves by result length, their torsion and their integer value keys; E: bases 3 to 9 and 12, operands below `b²`; F: bases 3, 4, 5 (all lines) and 6, 7, 8, 10 (6,000 seeded lines), operands below `b³` | 175 s (A 25, B and C 2, D 20, E 35, F 95), upper 260 s, from development reads of A to E9 (57 s) and of bases 6, 7 and 12 | 300 s | 221.5 s (ratio to the projection 1.27) | 31,820 KiB |

Exit 0, `fail []`. Output `closure_torsion.txt` (20 lines, one per part, each with its elapsed
milliseconds), SHA-256 `0a9273e652aaddd9e9e8d88d940010601e5db794ac31a0b661d413aeb723d782`; script
SHA-256 `d34d4e4cfa7ca3935b45d869d7c9c7707e9b8e9ce68c0e7b36037b8d1e3e7263`. The elapsed milliseconds
differ between runs; every other field is deterministic (the samples are seeded, 20261025). No private
data.

Earlier runs of this receipt, kept as evidence:
- the first launch used `/usr/bin/time`, which the host does not have (exit 127, nothing computed);
- the second was stopped by hand after part C printed: its check asked the leading digit to separate
  `x` from `x + 110`, which is false (`1` and `111`); C now checks the length, and that the leading
  digit does not;
- the third reached its 300 s deadline in its part D (three-place operands, 20,000 lines), factoring
  one maximal minor of many digits by trial division. The deadline was not raised; the law changed:
  the minors' gcd over several row orders, factored below `2²⁰` with the cofactor reported; the
  kernel solved from the echelon's kept rows and still checked on every row; 6,000 seeded lines per
  sampled base in F.
