"""By station: the executed decisions at a fitted E, causal (stations < j placed at truth) and open
(nothing placed), train and held-out; separates stations whose cell two back is a request cell
(weight nu(40)) from those whose cell two back is a placed station (weight nu(v)).

usage: eS_stations.py <E.npy> <terrain> <train seed> <held seed>"""
from fit import *

path, tname, s_tr, s_he = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
E = np.load(path)
t0 = time.time()
for label, pairs in (('train', terrain(np.random.default_rng(s_tr), 256)), ('held-out', terrain(np.random.default_rng(s_he), 128))):
    for mode in ('causal', 'open'):
        decs = decisions(pairs, mode)
        Cs, tg = counts_of(decs)
        top = read(Cs, E)['a'].argmax(1)
        st = np.array([j for _, _, j, _ in decs])
        by = [int(((top == tg) & (st == j)).sum()) for j in range(M_ST)]
        print(f'{label} {mode}: right by station {by} of {len(pairs)} each')
print(f'eS: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
