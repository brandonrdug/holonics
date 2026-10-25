# Run receipt

Host: the session's cloud container, one thread, Python 3 (`python3 -I`), integers and residues only.

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `closure_torsion.py` | A: base 10, 10,000 two-place sums, rank, minors' gcd, torsion; B: the eleven key on every true line and 595,040 false lines; C: the units key, `c mod 110` and the length bit; D: the two halves by result length, their torsion and their integer value keys; E: bases 3 to 9 and 12, operands below `b²`; F: bases 3, 4, 5 (all lines) and 6, 7, 8, 10 (6,000 seeded lines), operands below `b³` | 175 s (A 25, B and C 2, D 20, E 35, F 95), upper 260 s, from development reads of A to E9 (57 s) and of bases 6, 7 and 12 | 300 s | 221.5 s (ratio to the projection 1.27) | 31,820 KiB |
| `closure_differences.py` | G: base 10, the 5,050 differences `b ≤ a < 100`, torsion and the results each field tells apart; H: the key modulo 20 on every true line and every false line below 100; I: the 4,995 two-place minuends, torsion, results told apart over Q, the exact key on true and false lines; J: split by the result's length; K: bases 3 to 9 and 12, `b ≤ a < base²` | 85 s (G 16, H 1, I 15, J 10, K 43), upper 130 s, from development reads of G, I, J (31 s) and of K (45 s) | 160 s | 80.5 s (ratio to the projection 0.95) | 53,280 KiB |
| `closure_reflection.py` | L: the 5,050 differences with the hand reversible (no reflector, `−` reflecting, `−` reflecting and `=` restarting, `=` reflecting), torsion and results told apart over Q; M: sums in bases 3 to 10 with `=` reflecting, the minors' gcd over four row orders against `b(b − 1)`; N: the 15,050 sums and differences in one menu under four hands, torsion and, at each torsion prime, the results of each family told apart | about 190 s (L 25, M 55, N 110), from development reads of the one-menu hands (27 s each) and of the differences (16 s) | 300 s | 183.3 s (L 23, M 51, N 109; ratio to the projection 0.96) | 31,100 KiB |

Exit 0, `fail []`. Output `closure_torsion.txt` (20 lines, one per part, each with its elapsed
milliseconds), SHA-256 `0a9273e652aaddd9e9e8d88d940010601e5db794ac31a0b661d413aeb723d782`; script
SHA-256 `d34d4e4cfa7ca3935b45d869d7c9c7707e9b8e9ce68c0e7b36037b8d1e3e7263`. The elapsed milliseconds
differ between runs; every other field is deterministic (the samples are seeded, 20261025). No private
data.

`closure_differences.py`: exit 0, `fail []`. Output `closure_differences.txt` (13 lines, one per part, each with its
elapsed milliseconds), SHA-256 `d3a0c5e9735cfae0d20567fc481b7ca2f116b10e71d301a07c56b46dd7643565`; script SHA-256
`6b9cbc7b4c581e18fc78ba2b2701585f8b4654a410e3d889597294b59a53f7c1`. It imports `closure_torsion.py`'s exact reading
from the same directory. One run of the receipt. A development read before it checked false lines up to
`c′ = 129`: a three-place false result meets the pair `(1, c₁)`, which no two-place line has, so the closed
forms do not read it; H and I take false results below 100, the results' own range.

`closure_reflection.py`: exit 0, `fail []`. Output `closure_reflection.txt` (17 lines, one per reading, each with its
elapsed milliseconds), SHA-256 `6979d56c21f0207a4406e0b57fd3b3ccd9969b8683ed8c6cef8dc1e19d266377`; script SHA-256
`ec3ea446d78bc1637ad62347c6005ca2076c2d3633490e757e4068d62d24cada`. It imports `closure_torsion.py`'s exact reading.
Its first run (deadline 360 s) failed only N's sums modulo 11: the result's classes were read from the whole
line's row, which counts a pair the operands share with the result twice. The law changed, not the limit: the
result's own share is the pairs from the `=` seam on, each with its hand, and `−ψ(c₀)` with the end's hand. The
second run, above, passed under a lower deadline.

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
