"""The circle moves read by region and surprise fifth (the lead, November 22, the chirality pass): `moves.tsv` (each known site's counts
of turn+, turn-, shear+, shear-, lock+, lock-, flip+, flip- over its ticks and circles) joined to `codes.tsv` (the law's code of each place
on 2^-20 bits) and to the rows' text (a site's byte: a letter, a digit, a space, a word's first letter). Outside the machine.
Usage: moves_table.py DIR ROWS"""
import sys, collections
d, rows_f = sys.argv[1], sys.argv[2]
texts = []
for line in open(rows_f, encoding='utf-8'):
    f = line.rstrip('\n').split('\t')
    texts.append((f[1] + f[2][:1]).replace('\\n', '\n').encode('utf-8', 'surrogateescape'))
codes = {}
for line in open(d + '/codes.tsv'):
    r, g, t, c = line.rstrip('\n').split('\t')[:4]
    codes[(int(r), int(t))] = int(c)
recs = []
for line in open(d + '/moves.tsv'):
    f = line.rstrip('\n').split('\t')
    r, t = int(f[0]), int(f[2]); m = list(map(int, f[4:12]))
    b = texts[r][t:t + 1]; prev = texts[r][t - 1:t] if t > 0 else b' '
    ch = b.decode('latin-1') if b else ''
    region = 'digit' if ch.isdigit() else 'space' if ch.isspace() else ('first' if ch.isalpha() and not prev.decode('latin-1').isalpha() else 'letter' if ch.isalpha() else 'other')
    recs.append((region, codes.get((r, t)), m))
coded = sorted(c for _, c, _ in recs if c is not None)
cuts = [coded[len(coded) * k // 5] for k in range(1, 5)]
def fifth(c): return None if c is None else sum(c >= x for x in cuts)
def line(name, sel):
    tot = [sum(m[i] for _, _, m in sel) for i in range(8)]; n = sum(tot) or 1
    kinds = [(tot[0] + tot[1]) / n, (tot[2] + tot[3]) / n, (tot[4] + tot[5]) / n, (tot[6] + tot[7]) / n]
    plus = (tot[0] + tot[2] + tot[4] + tot[6]) / n
    print(f'MOVES {name:<14} sites {len(sel):>7}  turn {kinds[0]:.4f}  shear {kinds[1]:.6f}  lock {kinds[2]:.4f}  flip {kinds[3]:.6f}  right-handed {plus:.3f}')
line('all', recs)
for reg in ('letter', 'first', 'digit', 'space', 'other'):
    line(reg, [x for x in recs if x[0] == reg])
for k in range(5):
    line(f'surprise {k + 1}/5', [x for x in recs if fifth(x[1]) == k])
