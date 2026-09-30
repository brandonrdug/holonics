"""Step 1: how the certified E step moves the executed growth and the lock's margin, on the declared
order-2 field, against the margin; and the step a lock needs."""
from common import *
from dumpio import parse_learn

t0 = time.time()
Es, train = parse_learn(DIR + '/learn.dump')
E0c = Es[0][0]
E8c = Es[-1][0]
dE_all = E8c - E0c
dE_1 = Es[1][0] - Es[0][0]
fro = lambda X: float(np.sqrt((np.abs(X) ** 2).sum()))
print('||dE_1||_F in', log2cell(fro(dE_1)), ' ||dE_8 total||_F in', log2cell(fro(dE_all)), ' ||E_0||_F^2 =', fro(E0c) ** 2)

rng = np.random.default_rng(5151)
held = order2(rng, 64)
for mode in ('open', 'causal'):
    decs = decisions(held, mode)
    Cs, tg = counts_of(decs)
    r0 = read(Cs, E0c, grad=True, want_face=True)
    r8 = read(Cs, E8c)
    a0, a8, GE = r0['a'], r8['a'], r0['GE']
    nd = len(decs)
    idx = np.arange(nd)
    top = a0.argmax(1)
    srt = np.sort(a0, 1)
    runner = np.argsort(a0, 1)[:, -2]
    margin = srt[:, -1] - srt[:, -2]
    # first-order check on the whole 8-deposit step
    pred = inner(GE, dE_all[None, None])            # (nd, 5)
    exact = a8 - a0
    rel = np.abs(pred - exact).max() / np.abs(exact).max()
    print(f'\n[{mode}] decisions {nd}; executed top = target {int((top == tg).sum())}; top = termination {int((top == TERM).sum())};'
          f' face top = target {int((r0["A"].argmax(1) == tg).sum())}; face top = executed top {int((r0["A"].argmax(1) == top).sum())}')
    print(f'  first-order vs recomputed growth change over 8 deposits: largest |pred - exact| / largest |exact| in {log2cell(rel)}')
    changed = int((a8.argmax(1) != top).sum())
    print(f'  decisions changed by the 8 certified deposits: {changed} of {nd}')
    # margins
    lm = np.log(srt[:, -1] / srt[:, -2])
    print(f'  lock margin top - runner (growth units): least {dy(margin.min())}, median {dy(np.median(margin))}; in log growth (nats): least {dy(lm.min())}, median {dy(np.median(lm))}')
    # change of the margin along the actual step
    dmar = inner(GE[idx, top] - GE[idx, runner], dE_all[None])
    kappa = np.where(dmar < 0, margin / np.maximum(-dmar, 1e-300), np.inf)
    print(f'  along the actual 8-deposit step: margin shrinks at {int((dmar < 0).sum())}, grows at {int((dmar > 0).sum())};'
          f' least multiple of the step that turns a lock (first order) in {log2cell(kappa.min())}, median over shrinking in {log2cell(np.median(kappa[np.isfinite(kappa)]))}')
    # toward the target
    wrong = top != tg
    g = a0[idx, top] - a0[idx, tg]
    dg = inner(GE[idx, tg] - GE[idx, top], dE_all[None])
    print(f'  wrong decisions {int(wrong.sum())}: the step raises target-over-top at {int((dg[wrong] > 0).sum())}, lowers it at {int((dg[wrong] < 0).sum())}')
    kt = np.where(wrong & (dg > 0), g / np.maximum(dg, 1e-300), np.inf)
    fin = kt[np.isfinite(kt)]
    if len(fin):
        print(f'  multiple of the actual step to bring the target level with the top (first order): least in {log2cell(fin.min())}, median in {log2cell(np.median(fin))}')
    # minimal-norm step to lift the target to the top (first order), vs the certified step's norm
    gn = np.sqrt((np.abs(GE[idx, tg] - GE[idx, top]) ** 2).sum(axis=(1, 2)))
    need = g[wrong] / gn[wrong]
    print(f'  least-norm step lifting the target to the top (first order): least ||dE||_F in {log2cell(need.min())}, median in {log2cell(np.median(need))};'
          f' the certified step per deposit ||dE_1||_F in {log2cell(fro(dE_1))}; ratio median/||dE_1|| in {log2cell(np.median(need) / fro(dE_1))}')
    # sensitivity scale: |d a / d E| per unit Frobenius
    gnorm = np.sqrt((np.abs(GE) ** 2).sum(axis=(2, 3)))
    print(f'  ||d a/d E||_F over candidates: median in {log2cell(np.median(gnorm))}, largest in {log2cell(gnorm.max())}; growth a median {dy(np.median(a0), 4)}, largest {dy(a0.max(), 4)}')
    # the face's sensitivity and its alignment with the executed one on the same candidates
    GA = r0['GA']
    cos = inner(GA, GE) / (np.sqrt((np.abs(GA) ** 2).sum(axis=(2, 3))) * np.sqrt((np.abs(GE) ** 2).sum(axis=(2, 3))))
    print(f'  cosine between dA/dE and da/dE per candidate: quartiles {[dy(q, 8) for q in np.quantile(cos, [0.25, 0.5, 0.75])]}')
print(f'\ns1_margin: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
