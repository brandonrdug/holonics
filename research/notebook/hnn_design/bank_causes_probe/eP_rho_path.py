"""The float fit's first steps, one line a step (the modulus's move from one, September 30): the
same protocol as `eO_fit.py` (E by Adam, rho by the same batch's central difference under Adam,
the cosine schedule of `steps`), stopped after `stop` steps; each step prints rho before the step,
the sign and size of the float rho-gradient g (positive asks rho down), the step's largest |dE| and
E's largest entry, and the batch's decisions and loss. It answers whether the float fit's path
moves E first and rho after. Exterior float probe; nothing it prints is used as a native reading.

usage: eP_rho_path.py <terrain> <steps> <stop> <train> <seed> <lr> <lr_rho> <rho0> <batch>"""
from fit import *
import bankprobe
import model

BOUND = 8.0
tname, steps, stop, ntrain, seed = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                    int(sys.argv[4]), int(sys.argv[5]))
lr0, lr_rho, rho0, batch = float(sys.argv[6]), float(sys.argv[7]), float(sys.argv[8]), int(sys.argv[9])
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
t0 = time.time()
rng = np.random.default_rng(seed)
train = terrain(rng, ntrain)
model.DECAY[0] = rho0


def snapshots(req, E):
    """The float lock iteration's refinements (eO_fit.trajectory's order)."""
    locked, snaps = {}, []
    while len(locked) < M_ST:
        open_st = [j for j in range(M_ST) if j not in locked]
        snaps.append(dict(locked))
        Cs = np.concatenate([candidates_counts(req, locked, j) for j in open_st])
        a = read(Cs, E)['a']
        best = None
        for k, j in enumerate(open_st):
            row = a[k]
            top = int(row.argmax())
            srt = np.sort(row)
            gap = srt[-1] - srt[-2]
            if row[top] > 1 and gap > 0 and (best is None or gap > best[2]):
                best = (j, top, gap)
        if best is None:
            return snaps
        locked[best[0]] = best[1]
    return snaps


def batch_loss(decs, E):
    Cs, tg = counts_of(decs)
    loss, GE, _, _ = executed_loss_grad(Cs, tg, E)
    return loss, GE


E0c, _ = bankprobe.E0()
E = E0c.copy()
opt = Adam(E.shape, lr0)
m_r, v_r = 0.0, 0.0
for step in range(stop):
    opt.lr = lr0 * 0.5 * (1 + np.cos(np.pi * step / steps))
    idx = rng.choice(len(train), batch, replace=False)
    decs = []
    for i in idx:
        req, tgt = train[i]
        for placed in snapshots(req, E):
            for j in range(M_ST):
                if j not in placed:
                    decs.append((req, placed, j, tgt[j]))
    loss, GE = batch_loss(decs, E)
    rho = model.DECAY[0]
    eps = 1e-3
    model.DECAY[0] = min(rho + eps, 1.0)
    up, _ = batch_loss(decs, E)
    model.DECAY[0] = rho - eps
    down, _ = batch_loss(decs, E)
    g = (up - down) / (min(rho + eps, 1.0) - (rho - eps))
    m_r = 0.9 * m_r + 0.1 * g
    v_r = 0.999 * v_r + 0.001 * g * g
    t = step + 1
    d = -lr_rho * 0.5 * (1 + np.cos(np.pi * step / steps)) * (m_r / (1 - 0.9 ** t)) / (np.sqrt(v_r / (1 - 0.999 ** t)) + 1e-12)
    model.DECAY[0] = float(np.clip(rho + d, 0.05, 1.0))
    dE = opt.step(GE)
    E = E + dE
    E = np.clip(E.real, -BOUND, BOUND) + 1j * np.clip(E.imag, -BOUND, BOUND)
    print(f'step {step}: rho {rho!r} -> {model.DECAY[0]!r}; g {g!r}; decisions {len(decs)}; loss {loss!r}; '
          f'largest |dE| {np.abs(np.concatenate([dE.real, dE.imag])).max()!r}; '
          f'|E| max {np.abs(np.concatenate([E.real, E.imag])).max()!r}', flush=True)
print(f'eP_rho_path {sys.argv[1:]}: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
