"""A ruler: read-reach's codes at the answer digits make_rows.py names, by kind, digit index and setting, in nats a digit.
Usage: answer_codes.py CODES_DIR PLACES"""
import sys, collections, math
d, pf = sys.argv[1], sys.argv[2]
settings = [l.strip() for l in open(d + '/settings.tsv') if l.strip()]
code = {}
for line in open(d + '/codes.tsv'):
    f = line.rstrip('\n').split('\t')
    code[(int(f[0]), int(f[2]))] = [int(v) for v in f[3:]]
by = collections.defaultdict(lambda: [0] + [0.0] * len(settings))
for line in open(pf):
    r, kind, p, k, L, src = line.rstrip('\n').split('\t')
    c = code[(int(r), int(p))]
    for key in (kind, f'{kind}:k{min(int(k), 4)}'):
        b = by[key]; b[0] += 1
        for i, v in enumerate(c):
            b[i + 1] += v / 2 ** 20 * math.log(2)
print('ANSWER_CODES nats a digit, settings: ' + ' | '.join(settings))
for key in sorted(by):
    b = by[key]
    print(f'ANSWER {key:12s} n={b[0]:5d} ' + ' '.join(f'{v / b[0]:.3f}' for v in b[1:]))
