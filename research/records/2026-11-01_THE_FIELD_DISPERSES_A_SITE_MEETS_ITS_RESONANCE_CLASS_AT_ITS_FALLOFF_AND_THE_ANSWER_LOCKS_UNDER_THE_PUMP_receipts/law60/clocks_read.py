"""§16.44's reading (1), from restate-field's CLOCKS.tsv (private; this prints only means): with every answer place but the
result C open, at the two `>` places of each restatement, by tick (the ticks whose clocks the blanks set) and paced head,
the gap's expected duration over its written duration, `(κ₁ + κ₂) / (2 κ(>))`, and the faces' code of the `>` against
their entropy in bits (a face that still predicts its byte codes it near its entropy).
"""
import csv, sys
from collections import defaultdict
for path in sys.argv[1:]:
    acc = defaultdict(lambda: [0, 0.0, 0.0, 0.0])
    for r in csv.DictReader(open(path), delimiter='\t'):
        a = acc[(int(r['tick']), int(r['head']))]
        a[0] += 1
        a[1] += (int(r['kappa_first']) + int(r['kappa_second'])) / (2 * int(r['kappa_written']))
        a[2] += (int(r['code_first']) + int(r['code_second'])) / 2 / 2 ** 20
        a[3] += (int(r['entropy_first']) + int(r['entropy_second'])) / 2 / 2 ** 20
    print(path)
    for (t, h), (n, ratio, code, ent) in sorted(acc.items()):
        print(f"  tick {t} head {h}: restatements {n}; the gap's expected over its written duration {ratio / n:.3f}; the >'s code {code / n:.3f} bits against the faces' entropy {ent / n:.3f}")
