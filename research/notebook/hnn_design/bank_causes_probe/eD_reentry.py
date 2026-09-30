"""The re-entry diagnostic's requests and its float prototype (September 30; not a pinned run, not
evidence): the frozen seed-test fit (`E`, `rho` from an export) and 16 development held-out order-2
requests (seed 41 + 1,000,003, the development draw), the first of each seed pair `(x_38, x_39)` in
the draw's order, written as an export for the exact owner (`bank_causes -- reentry`), which reads
every margin used as evidence.

The float prototype replays each request's correct partial section in clock order and in the float
release's lock order (the largest gap first) and, at every insertion, reads each open station's
candidates three ways: the full placement; the enlarged denominator alone (every re-entered datum
in the span's transported mass, none of their amplitudes); and no re-entry (the open section). It
prints, per order and intervention, the first insertion at which a comparison that holds from the
open section (the target's growth above every rival's) is lost. Exterior float probe.

usage: eD_reentry.py <export with E and rho> <out>"""
from fractions import Fraction
from fit import *
import model

src, out = sys.argv[1], sys.argv[2]
lines = open(src).read().splitlines()
shape = [int(x) for x in lines[0].split()[1:]]
real = np.array([[float(Fraction(x)) for x in lines[1 + i].split()] for i in range(shape[0])])
E = real[0::2] + 1j * real[1::2]
rho_line = next(line for line in lines if line.startswith('rho '))
model.DECAY[0] = float(Fraction(rho_line.split()[1]))

rng = np.random.default_rng(41 + 1_000_003)
chosen = {}
drawn = 0
while len(chosen) < SYMBOLS ** 2:
    (req, tgt), = order2(rng, 1)
    drawn += 1
    key = (int(req[-2]), int(req[-1]))
    if key not in chosen:
        chosen[key] = (drawn - 1, [int(x) for x in req], [int(x) for x in tgt])
pairs = [chosen[key] for key in sorted(chosen)]


def denominator_counts(request, placed, station, cand):
    """The span's weights with the placed data in its transported mass, their amplitudes absent."""
    C = placement_counts(request, placed, station, cand)
    ages = [M_ST + len(request) - 1 - k for k in range(len(request))]
    ages += [M_ST - 1 - j for j in list(placed) + [station]]
    total = sum(model.DECAY[0] ** a for a in ages)
    for j, x in placed.items():
        C[(D - 1 - j) % D, x] -= model.DECAY[0] ** (M_ST - 1 - j) / total
    return C


def reads(req, placed, stations, counts):
    Cs = np.concatenate([np.stack([counts(req, placed, j, y) for y in range(CLASSES)]) for j in stations])
    return read(Cs, E)['a']


def float_release(req):
    locked, order = {}, []
    while len(locked) < M_ST:
        open_st = [j for j in range(M_ST) if j not in locked]
        a = reads(req, locked, open_st, placement_counts)
        best = None
        for k, j in enumerate(open_st):
            row = a[k]
            top = int(row.argmax())
            gap = row[top] - np.sort(row)[-2]
            if row[top] > 1 and gap > 0 and (best is None or gap > best[2]):
                best = (j, top, gap)
        if best is None:
            return [locked.get(j, -1) for j in range(M_ST)], False, order
        locked[best[0]] = best[1]
        order.append(best[0])
    return [locked[j] for j in range(M_ST)], True, order


def holds(row, t):
    return all(row[t] > row[x] for x in range(CLASSES) if x != t)


out_lines = lines[:shape[0] + 1] + [rho_line]
summary = []
for i, (index, req, tgt) in enumerate(pairs):
    sec, ok, gap_order = float_release(req)
    out_lines.append(f"pair {i} {','.join(map(str, req))} {','.join(map(str, tgt))} float "
                     f"{','.join(map(str, sec))} {int(ok)}")
    open_rows = reads(req, {}, range(M_ST), placement_counts)
    right0 = {j for j in range(M_ST) if holds(open_rows[j], tgt[j])}
    for label, order in (('clock', list(range(M_ST))), ('gap', gap_order + [j for j in range(M_ST) if j not in gap_order])):
        for name, counts in (('full', placement_counts), ('denominator', denominator_counts)):
            first = None
            for k in range(1, M_ST):
                placed = {j: tgt[j] for j in order[:k]}
                open_st = [j for j in range(M_ST) if j not in placed]
                a = reads(req, placed, open_st, counts)
                lost = [j for n, j in enumerate(open_st) if j in right0 and not holds(a[n], tgt[j])]
                if lost:
                    first = (k, order[k - 1], lost)
                    break
            summary.append((i, label, name, first))
    print(f'request {i} (draw {index}): seed pair {req[-2]},{req[-1]}; target {tgt}; float release {sec} '
          f'(right {sum(int(a == b) for a, b in zip(sec, tgt))}), lock order {gap_order}; '
          f'open-section comparisons holding at stations {sorted(right0)}', flush=True)
for i, label, name, first in summary:
    print(f'  request {i} {label} {name}: first lost ' +
          ('none' if first is None else f'at insertion {first[0]} (station {first[1]} placed): stations {first[2]}'))
with open(out, 'w') as f:
    f.write('\n'.join(out_lines) + '\n')
print(f'eD_reentry: {len(pairs)} requests from {drawn} development draws; peak {peak_bytes()} bytes')
