"""Objective against executed behaviour, decomposed on the same candidates: the executed tick's growth,
the kicked chart's growth (Rot_v(1 + pR(c)) per crossing, lossless, the chart the face is derived
in), the face summed over members and its largest member term; top agreement and pairwise order
agreement for each link; and the direction links (certified step, face descent, executed descent)."""
from fit import *
from dumpio import parse_learn
import bankprobe

t0 = time.time()
ROT = np.array([[V.real, -V.imag], [V.imag, V.real]])


def kicked_growth(zturn, p):
    B, d = zturn.shape
    out = np.zeros((B, 4))
    trs = np.zeros((B, 4))
    dets = np.zeros((B, 4))
    for m in range(4):
        c = zturn * (1j ** ((m * np.arange(d)) % 4))[None]
        Mon = np.broadcast_to(np.eye(2), (B, 2, 2)).copy()
        for t in range(d):
            Rm = np.empty((B, 2, 2))
            Rm[:, 0, 0] = c[:, t].real
            Rm[:, 0, 1] = c[:, t].imag
            Rm[:, 1, 0] = c[:, t].imag
            Rm[:, 1, 1] = -c[:, t].real
            Mon = (ROT @ (np.eye(2) + p * Rm)) @ Mon
        out[:, m] = np.abs(np.linalg.eigvals(Mon)).max(1)
        trs[:, m] = np.trace(Mon, axis1=1, axis2=2)
        dets[:, m] = np.linalg.det(Mon)
    return out, trs, dets


def agree(x, y):
    ag = tot = 0
    for i in range(CLASSES):
        for j in range(i + 1, CLASSES):
            ag += int((np.sign(x[:, i] - x[:, j]) == np.sign(y[:, i] - y[:, j])).sum())
            tot += len(x)
    return f'{ag} of {tot}'


E0c, _ = bankprobe.E0()
settings = [('E_0', E0c)]
try:
    settings.append(('E fitted on the executed decision (order-2, causal)', np.load(DIR + '/E_order2_executed_causal_101.npy')))
except FileNotFoundError:
    pass
held = order2(np.random.default_rng(101 + 1_000_003), 64)
for label, E in settings:
    for mode in ('open', 'causal'):
        decs = decisions(held, mode)
        Cs, tg = counts_of(decs)
        z = to_turn(storage_nodes(Cs, E))
        a, _, mem, _ = joint_growth(z, P)
        kg, trs, dets = kicked_growth(z, P)
        W = z @ FW.T
        Am = P ** 2 * (np.abs(W[:, 0::2]) ** 2 + np.abs(W[:, 1::2]) ** 2)   # per member
        A = Am.sum(1)
        shp = (-1, CLASSES)
        a, ka, A, Amax = a.reshape(shp), kg.max(1).reshape(shp), A.reshape(shp), Am.max(1).reshape(shp)
        past = (np.abs(trs) > 2 * np.sqrt(np.abs(dets)))
        print(f'\n[{label} / {mode}] {len(decs)} decisions; kicked-chart members past their threshold (tr^2 > 4 det) {int(past.sum())} of {past.size}')
        print(f'  executed tick vs kicked chart:        top alike {int((a.argmax(1) == ka.argmax(1)).sum())}, pairs alike {agree(a, ka)}')
        print(f'  kicked chart vs face (members summed): top alike {int((ka.argmax(1) == A.argmax(1)).sum())}, pairs alike {agree(ka, A)}')
        print(f'  kicked chart vs largest member term:  top alike {int((ka.argmax(1) == Amax.argmax(1)).sum())}, pairs alike {agree(ka, Amax)}')
        print(f'  executed vs face:                     top alike {int((a.argmax(1) == A.argmax(1)).sum())}, pairs alike {agree(a, A)}')
        print(f'  top = target: executed {int((a.argmax(1) == tg).sum())}, kicked {int((ka.argmax(1) == tg).sum())}, face {int((A.argmax(1) == tg).sum())}, largest member term {int((Amax.argmax(1) == tg).sum())}')

# direction links on the training batch at E_0
Es, _ = parse_learn(DIR + '/learn.dump')
train = order2(np.random.default_rng(101), 256)
fro = lambda X: float(np.sqrt((np.abs(X) ** 2).sum()))
for mode in ('causal', 'partition'):
    decs = decisions(train, mode, np.random.default_rng(5))
    Ct, tt = counts_of(decs)
    _, gf, _ = face_loss_grad(Ct, tt, E0c)
    _, ge, _, _ = executed_loss_grad(Ct, tt, E0c)
    cert = Es[-1][0] - Es[0][0]
    c = lambda x, y: dy(inner(x, y) / (fro(x) * fro(y)), 10)
    print(f'\ndirections at E_0 ({mode} batch): cos(face descent, executed descent) {c(-gf, -ge)}; cos(certified 8-deposit step, face descent) {c(cert, -gf)}; '
          f'cos(certified step, executed descent) {c(cert, -ge)}')
print(f'\ne3: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
