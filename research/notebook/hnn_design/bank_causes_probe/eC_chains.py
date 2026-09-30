"""A diagnostic after the passage pin's seed test (not a pinned run): a fitted E and rho's executed
decisions by station on the held-out order-2 requests, with the section's stations placed at their
truth four ways: before j (teacher-forced), only the other chain (the odd stations for an even one
and the reverse), only the same chain before j, and nothing. The order-2 rule's two chains: station
2k continues x_38, station 2k + 1 continues x_39. Exact counts of a float exterior probe.

usage: eC_chains.py <E.npy> <rho file> <held-out seed>"""
from fit import *
import model

E = np.load(sys.argv[1])
model.DECAY[0] = float(open(sys.argv[2]).read())
held = order2(np.random.default_rng(int(sys.argv[3])), 128)
modes = {
    'teacher-forced (stations before j at truth)': lambda tgt, j: {i: tgt[i] for i in range(j)},
    'the other chain at truth': lambda tgt, j: {i: tgt[i] for i in range(M_ST) if i % 2 != j % 2},
    'the same chain before j at truth': lambda tgt, j: {i: tgt[i] for i in range(j) if i % 2 == j % 2},
    'nothing placed': lambda tgt, j: {},
}
for label, placed_of in modes.items():
    decs = [(req, placed_of(tgt, j), j, tgt[j]) for req, tgt in held for j in range(M_ST)]
    Cs, tg = counts_of(decs)
    top = read(Cs, E)['a'].argmax(1)
    st = np.array([j for _, _, j, _ in decs])
    by = [int(((top == tg) & (st == j)).sum()) for j in range(M_ST)]
    print(f'{label}: right by station {by} of {len(held)} each')
