"""Rows for the reach's presence read: passages of three records of one kind, each record `EXPRESSION = ANSWER` on its own line as the
terrain's world writes them, read whole by two streams. The places of the third record's answer are named in `places.tsv` (row, kind,
place, the answer digit's index k, the needed source places). A ruler's table, outside the machine.
Usage: make_rows.py SEED N_PER_KIND OUT_ROWS OUT_PLACES"""
import sys, random
seed, n, out_rows, out_places = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
rng = random.Random(seed)
def copy_rec(L):
    d = [str(rng.randrange(10)) for _ in range(L)]
    return 'copy ' + ' '.join(d) + ' = ' + ' '.join(d), d
def rev_rec(L):
    d = [str(rng.randrange(10)) for _ in range(L)]
    return 'reverse ' + ' '.join(d) + ' = ' + ' '.join(reversed(d)), d
def sum_rec(la, lb):
    a = rng.randrange(10 ** (la - 1) if la > 1 else 0, 10 ** la); b = rng.randrange(10 ** (lb - 1) if lb > 1 else 0, 10 ** lb)
    return f'{a} + {b} = {a + b}', (str(a), str(b), str(a + b))
rows, places = [], []
for kind in ('copy', 'reverse', 'sum'):
    for i in range(n):
        recs = []
        if kind == 'sum':
            for _ in range(3):
                recs.append(sum_rec(rng.randint(1, 3), rng.randint(1, 3)))
        else:
            L = rng.randint(2, 7)
            for r in range(3):
                recs.append((copy_rec if kind == 'copy' else rev_rec)(rng.randint(2, 7) if r < 2 else L))
        text = '\n'.join(t for t, _ in recs) + '\n'
        start = len(text) - len(recs[2][0]) - 1          # the third record's first place
        last, info = recs[2]
        eq = start + last.index(' = ') + 3               # the answer's first place
        r = len(rows)
        if kind in ('copy', 'reverse'):
            L = len(info); src0 = start + last.index(' ') + 1
            for k in range(L):
                p = eq + 2 * k
                s = src0 + 2 * (k if kind == 'copy' else L - 1 - k)
                places.append(f'{r}\t{kind}\t{p}\t{k}\t{L}\t{s}')
        else:
            a, b, c = info
            for k in range(len(c)):                     # k counted from the answer's end
                p = eq + len(c) - 1 - k
                sa = start + len(a) - 1 - k if k < len(a) else -1
                sb = start + len(a) + 3 + len(b) - 1 - k if k < len(b) else -1
                places.append(f'{r}\t{kind}\t{p}\t{k}\t{len(a)}{len(b)}\t{sa},{sb}')
        rows.append(f'{kind}:{len(text)}:{i}\t{text[:-1].replace(chr(10), chr(92) + "n")}\t\\n')
open(out_rows, 'w').write('\n'.join(rows) + '\n')
open(out_places, 'w').write('\n'.join(places) + '\n')
