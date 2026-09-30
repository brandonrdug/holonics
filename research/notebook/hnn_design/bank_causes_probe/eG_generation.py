"""The release against the trained comparison: generate_by_bank's lock iteration (largest growth gap
first) at a fitted E, instrumented: which station locks first, whether its cell two back is placed,
and whether it is right; with two diagnostic orders (largest log-growth gap; the stations in time
order) to locate where the release departs from the trained decisions. Diagnostics, not laws.

usage: eG_generation.py <E.npy> <terrain> <seed> <requests>"""
from fit import *

path, tname, seed, count = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
E = np.load(path)
held = terrain(np.random.default_rng(seed), count)
t0 = time.time()


def gen(req, order):
    locked = {}
    first = None
    while len(locked) < M_ST:
        open_st = [j for j in range(M_ST) if j not in locked]
        if order == 'time':
            open_st = open_st[:1]
        Cs = np.concatenate([candidates_counts(req, locked, j) for j in open_st])
        a = read(Cs, E)['a']
        best = None
        for k, j in enumerate(open_st):
            row = a[k]
            top = int(row.argmax())
            srt = np.sort(row)
            gap = srt[-1] - srt[-2] if order == 'absolute' else np.log(srt[-1] / srt[-2])
            if row[top] > 1 and gap > 0 and (best is None or gap > best[2]):
                best = (j, top, gap)
        if best is None:
            return [locked.get(j, -1) for j in range(M_ST)], False, first
        if first is None:
            first = (best[0], best[1])
        locked[best[0]] = best[1]
    return [locked[j] for j in range(M_ST)], True, first


for order in ('absolute', 'log', 'time'):
    right = rel = first_det = first_right = exact = 0
    by_station = [0] * M_ST
    for req, tgt in held:
        sec, ok, first = gen(req, order)
        rel += int(ok)
        hits = [int(a == b) for a, b in zip(sec, tgt)]
        right += sum(hits)
        exact += int(all(hits))
        for j in range(M_ST):
            by_station[j] += hits[j]
        if first is not None:
            first_det += int(first[0] < 2)
            first_right += int(first[1] == tgt[first[0]])
    print(f'lock order {order}: released {rel} of {len(held)}; stations right {right} of {M_ST * len(held)}; exact sections {exact}; '
          f'by station {by_station}; first lock at a station whose cell two back is placed (station 0 or 1) {first_det}, first lock right {first_right}')
print(f'eG: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
