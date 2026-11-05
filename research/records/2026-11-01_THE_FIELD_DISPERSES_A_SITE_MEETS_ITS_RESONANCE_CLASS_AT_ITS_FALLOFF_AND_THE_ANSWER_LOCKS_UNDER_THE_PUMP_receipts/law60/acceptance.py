"""§16.44's acceptance (a), from restate-field's RESTATEMENTS.tsv (private; this prints only means): with every answer
place but the result C open, at D's places read (its first and its last, one place for |C| = 1, so every place of D for
|C| <= 2), head 3's share of its row at the restatement's offset |C| + 2 at the last tick (offsets past the near field
not read), and the code of D's true class in bits; the reading of November 4 fixed (a) at a share above 0.45 and a code
under 3.60 bits.
"""
import csv, math, sys
for path in sys.argv[1:]:
    rows = [r for r in csv.DictReader(open(path), delimiter='\t') if r['state'] == 'answer_open' and r['at'] in ('first', 'last')]
    rows = [r for r in rows if not (r['at'] == 'last' and r['length'] == '1')]
    ticks = 1 + max(int(c.split('h')[0][1:]) for c in rows[0] if c.startswith('t') and 'h' in c and 'd' in c)
    near = [r for r in rows if int(r['offset']) <= 5]
    share = sum(int(r[f't{ticks - 1}h3d{r["offset"]}']) for r in near) / len(near) / 2 ** 63
    code = sum(-math.log2(max(int(r['p_true']), 1) / int(r['p_total'])) for r in rows) / len(rows)
    print(f"{path}: D places read {len(rows)} (within the near field {len(near)}); head 3 at the offset {share:.3f}; D's code {code:.3f} bits")
