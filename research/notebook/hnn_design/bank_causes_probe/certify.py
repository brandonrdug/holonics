"""Certify exactly a found E: round it to the dyadic grid 2^-g (exact), form every candidate's storage
exactly (the placement law with the chart's exact nu), read each by the owner's exact bank
(bank_causes exact-turns), and decide each station by the lock's flip on exact enclosures.

usage: certify.py <E.npy> <terrain> <seed> <requests> <grain bits> [mode causal|open]"""
import os
from fit import *
from fractions import Fraction
import subprocess
import bankprobe

path, tname, seed, count, g = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
mode = sys.argv[6] if len(sys.argv) > 6 else 'causal'
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
BIN = os.environ.get('BANK_CAUSES_BIN', 'target/release/examples/bank_causes')
t0 = time.time()

# the chart's exact nu, read from the owner's dump
NU = {}
for ln in open(DIR + '/read.dump'):
    if ln.startswith('nu '):
        _, n, v = ln.split()
        NU[int(n)] = Fraction(v)


def dyadic(x, bits):
    return Fraction(round(x * (1 << bits)), 1 << bits)


def exact_E(Ec, bits):
    return [[(dyadic(Ec[n, x].real, bits), dyadic(Ec[n, x].imag, bits)) for x in range(CLASSES)] for n in range(D)]


def exact_storage(Ex, request, placed, station, cand):
    cells = dict(placed)
    if station is not None:
        cells[station] = cand
    items = [(NU[len(request)], (len(request) - 1 - k) % D, x) for k, x in enumerate(request)]
    if cells:
        wv = NU[len(cells)]
        items += [(wv, (D - 1 - j) % D, x) for j, x in cells.items()]
    re = [Fraction(0)] * D
    im = [Fraction(0)] * D
    for w, r, x in items:
        for n in range(D):
            a, b = Ex[(n - r) % D][x]
            re[n] += w * a
            im[n] += w * b
    out = []
    for n in range(D):
        out += [re[n], im[n]]
    return out


# the exact placement path checked against the owner's exact storages (E_0, the dump's request 0)
E0c, _ = bankprobe.E0()
E0x = exact_E(E0c, 1)
req0 = None
checks = 0
for ln in open(DIR + '/read.dump'):
    if ln.startswith('request 0 '):
        rest = ln.split(' [', 1)[1]
        rq, tg0 = rest.split('] [')
        req0 = [int(x) for x in rq.split(',')]
        tg0 = [int(x) for x in tg0.strip().rstrip(']').split(',')]
    if ln.startswith('exact '):
        head, storage = ln.split(' | ')[0], ln.strip().split(' | ')[-1]
        label, cls = head.split()[1], int(head.split()[2])
        placed = {} if label == 's0' else {0: tg0[0], 1: tg0[1]}
        st = 0 if label == 's0' else 2
        mine = exact_storage(E0x, req0, placed, st, cls)
        assert mine == [Fraction(x) for x in storage.split()], 'exact placement differs from the owner'
        checks += 1
print(f'exact placement equals the owner BankPlacement::storage on {checks} storages')

Ec = np.load(path)
Ex = exact_E(Ec, g)
Er = np.array([[complex(float(a), float(b)) for (a, b) in row] for row in Ex])
held = terrain(np.random.default_rng(seed), count)
decs = decisions(held, mode)
Cs, tg = counts_of(decs)
fl = read(Cs, Er)['a']
ftop = fl.argmax(1)
print(f'float at the dyadic E (grain 2^-{g}): top = target {int((ftop == tg).sum())} of {len(decs)}; largest |entry| {max(max(abs(a), abs(b)) for row in Ex for (a, b) in row)}')
lines = []
for i, (req, placed, j, t) in enumerate(decs):
    for y in range(CLASSES):
        st = exact_storage(Ex, req, placed, j, y)
        lines.append(f'{i}:{y} ' + ' '.join(str(v) for v in st))
inp, outp = DIR + '/certify_in.txt', DIR + '/certify_out.txt'
open(inp, 'w').write('\n'.join(lines) + '\n')
t1 = time.time()
res = subprocess.run([BIN, 'exact-turns', inp, outp], capture_output=True, text=True)
print(res.stdout.strip(), f'(wall {time.time() - t1:.0f} s)')
reads = {}
for ln in open(outp):
    parts = ln.split()
    i, y = map(int, parts[0].split(':'))
    vals = [Fraction(v) for v in parts[1:]]
    lowers, uppers = vals[0::2], vals[1::2]
    reads[(i, y)] = (max(lowers), max(uppers), lowers, uppers)
flip_right = flip_wrong = undecided = unlocked = agree = inside = 0
for i in range(len(decs)):
    cands = [reads[(i, y)] for y in range(CLASSES)]
    top = max(range(CLASSES), key=lambda y: cands[y][0])
    flips = all(cands[top][0] > cands[y][1] for y in range(CLASSES) if y != top)
    for y in range(CLASSES):
        inside += int(float(cands[y][0]) - 1e-9 <= fl[i, y] <= float(cands[y][1]) + 1e-9)
    if not flips:
        undecided += 1
        continue
    if cands[top][0] <= 1:
        unlocked += 1
        continue
    agree += int(top == ftop[i])
    if top == tg[i]:
        flip_right += 1
    else:
        flip_wrong += 1
print(f'exact: {len(decs)} decisions; the lock flips to the target at {flip_right}, to another class at {flip_wrong}; '
      f'undecided (overlapping enclosures) {undecided}; top not past one {unlocked}; exact top = float top {agree}; '
      f'float joint growth inside its exact enclosure {inside} of {len(decs) * CLASSES}')
print(f'certify: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes (python)')
