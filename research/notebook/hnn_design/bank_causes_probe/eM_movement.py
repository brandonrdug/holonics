"""Movement (M): steps of growing size from E_0 along (a) the certified 8-deposit direction, (b) the
face's covector (its code's descent over the training batch), (c) the executed decision's own descent
(the aligned control); counts of decisions turned, turned to the target and turned away, train and
held-out (probe only, uncertified steps)."""
from fit import *
from dumpio import parse_learn
import bankprobe

t0 = time.time()
E0c, _ = bankprobe.E0()
Es, _ = parse_learn(DIR + '/learn.dump')
rng = np.random.default_rng(101)
train = order2(rng, 256)
held = order2(np.random.default_rng(101 + 1_000_003), 128)
tr_dec = decisions(train, 'causal')
he_dec = decisions(held, 'causal')
Ct, tt = counts_of(tr_dec)
Ch, th = counts_of(he_dec)
fro = lambda X: float(np.sqrt((np.abs(X) ** 2).sum()))
_, g_face, _ = face_loss_grad(Ct, tt, E0c)
_, g_exec, _, _ = executed_loss_grad(Ct, tt, E0c)
dirs = {
    'certified (E_8 - E_0)': Es[-1][0] - Es[0][0],
    'face covector descent': -g_face,
    'executed descent (aligned control)': -g_exec,
}
cos = inner(g_face, g_exec) / (fro(g_face) * fro(g_exec))
cosc = inner(dirs['certified (E_8 - E_0)'], -g_exec) / (fro(dirs['certified (E_8 - E_0)']) * fro(g_exec))
print(f'cosine(face descent, executed descent) on the training batch: {dy(cos, 10)}; cosine(certified step, executed descent): {dy(cosc, 10)}')
base_t = read(Ct, E0c, want_face=True)
base_h = read(Ch, E0c, want_face=True)
top_t, top_h = base_t['a'].argmax(1), base_h['a'].argmax(1)
ftop_t = base_t['A'].argmax(1)
print(f'at E_0: executed top = target train {int((top_t == tt).sum())}/{len(tt)}, held-out {int((top_h == th).sum())}/{len(th)}; face top = target train {int((ftop_t == tt).sum())}')
for name, U in dirs.items():
    U = U / fro(U)
    print(f'\n{name}:')
    for k in range(-9, 5):
        E = E0c + 2.0 ** k * U
        rt = read(Ct, E, want_face=True)
        rh = read(Ch, E)
        nt, nh = rt['a'].argmax(1), rh['a'].argmax(1)
        ft = rt['A'].argmax(1)
        ct = rt['cert'].all(1).sum()
        print(f'  ||dE||_F = 2^{k}: train turned {int((nt != top_t).sum())} (to target {int(((nt != top_t) & (nt == tt)).sum())}, away {int(((nt != top_t) & (top_t == tt)).sum())}), '
              f'right {int((nt == tt).sum())}; held-out turned {int((nh != top_h).sum())} (to target {int(((nh != top_h) & (nh == th)).sum())}, away {int(((nh != top_h) & (top_h == th)).sum())}), '
              f'right {int((nh == th).sum())}; face top = target train {int((ft == tt).sum())}; certified decisions train {ct}/{len(tt)}')
print(f'\neM: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
