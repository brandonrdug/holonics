"""A ruler: a sum's answer digits coded apart by the carry their place takes from the places under it. It reads what
answer_codes.py reads (read-reach's codes at the places make_rows.py names; receipts/2026-11-21_reach) and the rows' text, and
prints, by digit index k (from the units) and setting, the code in nats a digit where a carry is due, where none is, and their
difference. `plant` checks the split first: codes are drawn with one nat more wherever a carry is due, and the difference must
read one. Outside the machine. Usage: carry_split.py CODES_DIR PLACES ROWS | carry_split.py plant PLACES ROWS"""
import sys, collections, math, random

def sums(places_f, rows_f):
    texts = [l.rstrip('\n').split('\t')[1].replace('\\n', '\n') for l in open(rows_f, encoding='utf-8')]
    for line in open(places_f):
        r, kind, p, k, L, src = line.rstrip('\n').split('\t')
        if kind != 'sum': continue
        a, b = (int(x) for x in texts[int(r)].split('\n')[-1].split(' = ')[0].split(' + '))
        k = int(k)
        yield int(r), int(p), k, (a % 10 ** k + b % 10 ** k) >= 10 ** k

def table(code, settings, places_f, rows_f):
    by = collections.defaultdict(lambda: [0] + [0.0] * len(settings))
    for r, p, k, carry in sums(places_f, rows_f):
        cell = by[(min(k, 3), carry)]; cell[0] += 1
        for i, v in enumerate(code[(r, p)]): cell[i + 1] += v
    out = []
    for k in range(4):
        due, none = by.get((k, True)), by.get((k, False))
        line = f'CARRY sum:k{k} due n={due[0] if due else 0:4d} none n={none[0] if none else 0:4d}'
        if due and none and due[0] and none[0]:
            d = [x / due[0] for x in due[1:]]; n = [x / none[0] for x in none[1:]]
            line += ' | due ' + ' '.join(f'{x:.3f}' for x in d) + ' | none ' + ' '.join(f'{x:.3f}' for x in n) + ' | due less none ' + ' '.join(f'{x - y:+.3f}' for x, y in zip(d, n))
        out.append((line, due, none))
    return out

if sys.argv[1] == 'plant':
    rng = random.Random(7); code = {}
    for r, p, k, carry in sums(sys.argv[2], sys.argv[3]):
        code[(r, p)] = [rng.random() + (1.0 if carry else 0.0)]
    rows = table(code, ['planted'], sys.argv[2], sys.argv[3])
    for line, due, none in rows:
        print(line)
        if due and none and due[0] > 20 and none[0] > 20:
            assert abs(due[1] / due[0] - none[1] / none[0] - 1.0) < 0.15, line
    print('CARRY planted: one nat more where a carry is due reads as one nat at every index with 20 places a side')
else:
    d = sys.argv[1]
    settings = [l.strip() for l in open(d + '/settings.tsv') if l.strip()]
    code = {}
    for line in open(d + '/codes.tsv'):
        f = line.rstrip('\n').split('\t')
        code[(int(f[0]), int(f[2]))] = [int(v) / 2 ** 20 * math.log(2) for v in f[3:]]
    print('CARRY_SPLIT nats a digit, settings: ' + ' | '.join(settings))
    for line, _, _ in table(code, settings, sys.argv[2], sys.argv[3]):
        print(line)
