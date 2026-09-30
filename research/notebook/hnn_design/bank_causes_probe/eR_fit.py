"""Representation (R) and transfer (T): search E directly for the executed bank's decision on a
terrain (float Adam on log-growth logits), then read train and held-out; alignment (A): the same
search on the face's code, read by the executed lock.

usage: eR_fit.py <terrain> <objective executed|face> <steps> <train requests> <seed> <lr> <mode causal|partition>

The placement is the one passage's (`model.placement_counts`); every step is held inside the entry
bound's box, the native move's commit guard (`hnn::executed::entry_bound`: every realified entry of
`E` within `[−8, 8]`), so the fit stays inside what the native move may adopt."""
from fit import *
import bankprobe

BOUND = 8.0

tname = sys.argv[1]
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line, 'lag2': order2_random_lag2}[tname]
objective = sys.argv[2]
steps = int(sys.argv[3])
ntrain = int(sys.argv[4])
seed = int(sys.argv[5])
lr0 = float(sys.argv[6])
mode = sys.argv[7]
t0 = time.time()
rng = np.random.default_rng(seed)
train = terrain(rng, ntrain)
held = terrain(np.random.default_rng(seed + 1_000_003), 128)
tr_c = decisions(train, 'causal')
he_c = decisions(held, 'causal')
tr_p = decisions(train, 'partition', np.random.default_rng(seed + 7))
he_p = decisions(held, 'partition', np.random.default_rng(seed + 8))
E0c, _ = bankprobe.E0()
E = E0c.copy()
opt = Adam(E.shape, lr0)
batch = 32
best = (-1, E.copy(), 0)
path = 0.0
for step in range(steps + 1):
    if step % max(steps // 8, 1) == 0:
        trc, _ = accuracy(tr_c, E)
        hec, hcert = accuracy(he_c, E)
        trp, _ = accuracy(tr_p, E)
        hep, _ = accuracy(he_p, E)
        ftr, _ = face_accuracy(tr_c, E)
        fhe, fe = face_accuracy(he_c, E)
        score = trc if mode == 'causal' else trp
        if score > best[0]:
            best = (score, E.copy(), step)
        print(f'step {step}: executed top = target: causal train {trc}/{len(tr_c)}, held-out {hec}/{len(he_c)} (certified {hcert}); '
              f'partition train {trp}/{len(tr_p)}, held-out {hep}/{len(he_p)}; face top = target causal train {ftr}, held-out {fhe}; '
              f'face top = executed top (held-out causal) {fe}; ||E - E_0||_F {dy(float(np.sqrt((np.abs(E - E0c) ** 2).sum())), 6)}; path {dy(path, 4)}; {time.time() - t0:.0f} s', flush=True)
    if step == steps:
        break
    opt.lr = lr0 * 0.5 * (1 + np.cos(np.pi * step / steps))
    idx = rng.choice(len(train), batch, replace=False)
    bdec = decisions([train[i] for i in idx], mode, rng)
    Cs, tg = counts_of(bdec)
    if objective == 'executed':
        loss, GE, _, _ = executed_loss_grad(Cs, tg, E)
    else:
        loss, GE, _ = face_loss_grad(Cs, tg, E)
    dE = opt.step(GE)
    path += float(np.sqrt((np.abs(dE) ** 2).sum()))
    E = E + dE
    E = np.clip(E.real, -BOUND, BOUND) + 1j * np.clip(E.imag, -BOUND, BOUND)
score, E, at = best
np.save(f'{DIR}/E_{tname}_{objective}_{mode}_{seed}.npy', E)
print(f'best by training ({mode}) at step {at}: {score}')
rel, right, right_all = generation_score(held, E)
print(f'generation (lock iteration) on {len(held)} held-out requests: released {rel}, stations right {right} of {8 * len(held)} among released ({right_all} counting held sections)')
rel, right, right_all = generation_score(train[:128], E)
print(f'generation on 128 training requests: released {rel}, stations right {right} of {8 * 128} among released ({right_all} counting held)')
print(f'eR_fit {sys.argv[1:]}: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
