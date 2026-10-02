"""Fit E and the source navigator's transport modulus rho on the release's own trajectory (the
passage law of September 30; the float analog of the native `executed-open` arm): every refinement
of the float lock iteration (`generate_by_bank`'s order, the largest absolute gap first) with its
open stations compared with their targets, the executed decision's log-growth logits, float Adam
on E held inside the entry bound's box, rho by a central difference of the same batch's loss held
within [1/20, 1]; the release read on the held-out requests at each eighth of the steps. The last
E is saved with its rho (`E_onpolicy_<terrain>_<seed>.npy`, `rho_onpolicy_<terrain>_<seed>.txt`).
Exterior float probe; every reading used as evidence is re-read by the exact owner
(`bank_causes -- native-release`).

usage: eO_fit.py <terrain> <steps> <train> <seed> <lr> <lr_rho> <rho0> <batch>"""
from fit import *
import bankprobe
import model

BOUND = 8.0
tname, steps, ntrain, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
lr0, lr_rho, rho0, batch = float(sys.argv[5]), float(sys.argv[6]), float(sys.argv[7]), int(sys.argv[8])
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
t0 = time.time()
rng = np.random.default_rng(seed)
train = terrain(rng, ntrain)
held = terrain(np.random.default_rng(seed + 1_000_003), 128)
model.DECAY[0] = rho0


def trajectory(req, E):
    locked = {}
    snaps = []
    first = None
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
            return [locked.get(j, -1) for j in range(M_ST)], False, snaps, first
        if first is None:
            first = (best[0], best[1])
        locked[best[0]] = best[1]
    return [locked[j] for j in range(M_ST)], True, snaps, first


def evaluate(pairs, E):
    whole = right = f01 = fright = consistent = released = 0
    for req, tgt in pairs:
        sec, ok, _, first = trajectory(req, E)
        released += int(ok)
        hits = [int(a == b) for a, b in zip(sec, tgt)]
        right += sum(hits)
        whole += int(all(hits))
        consistent += int(all(sec[j] == (sec[j - 2] + 1) % 4 for j in range(2, M_ST)))
        if first is not None:
            f01 += int(first[0] < 2)
            fright += int(first[1] == tgt[first[0]])
    return released, whole, right, f01, fright, consistent


def batch_loss(decs, E):
    Cs, tg = counts_of(decs)
    loss, GE, _, _ = executed_loss_grad(Cs, tg, E)
    return loss, GE


E0c, _ = bankprobe.E0()
E = E0c.copy()
import os
ARM = os.environ.get('ARM', 'adam')


class Arm:
    """The refit's optimizer, ablated one ingredient at a time: `adam` (the refit), `rms` (no
    momentum), `momentum` (momentum, no per-coordinate scaling), `sgd` (neither). The arms without
    per-coordinate scaling take a global step matched to Adam's first step's root-mean-square."""

    def __init__(self, shape, lr):
        self.m = np.zeros(shape, complex)
        self.v = np.zeros(shape)
        self.lr = lr
        self.t = 0
        self.scale = None

    def step(self, g):
        self.t += 1
        b1 = 0.9 if ARM in ('adam', 'momentum') else 0.0
        self.m = b1 * self.m + (1 - b1) * g
        mh = self.m / (1 - b1 ** self.t) if b1 > 0 else self.m
        if ARM in ('adam', 'rms'):
            self.v = 0.999 * self.v + 0.001 * np.abs(g) ** 2
            vh = self.v / (1 - 0.999 ** self.t)
            return -self.lr * mh / (np.sqrt(vh) + 1e-12)
        if self.scale is None:
            # Adam's first step moves every coordinate by lr; match its root-mean-square.
            self.scale = 1.0 / (np.sqrt(np.mean(np.abs(g) ** 2)) + 1e-12)
        return -self.lr * self.scale * mh


opt = Arm(E.shape, lr0)
m_r, v_r = 0.0, 0.0
for step in range(steps + 1):
    if step % max(steps // 8, 1) == 0:
        rel, whole, right, f01, fright, cons = evaluate(held, E)
        tc, _ = accuracy(decisions(held, 'causal'), E)
        print(f'step {step}: rho {model.DECAY[0]:.4f}; held-out release: released {rel}, whole {whole}, stations {right}, '
              f'first lock at 0/1 {f01}, first lock right {fright}, consistent {cons}; teacher-forced {tc}/1024; '
              f'|E| max {np.abs(np.concatenate([E.real, E.imag])).max():.3f}; {time.time() - t0:.0f} s', flush=True)
    if step == steps:
        break
    if step % 10 == 0:
        # The comparison on a fixed set of 32 training requests, each on its own trajectory.
        fixed = []
        sigs = []
        for i in range(32):
            req, tgt = train[i]
            sec, _, snaps, first = trajectory(req, E)
            sigs.append((tuple(sec), first, tuple(tuple(sorted(p.items())) for p in snaps)))
            for placed in snaps:
                for j in range(M_ST):
                    if j not in placed:
                        fixed.append((req, placed, j, tgt[j]))
        fl, _ = batch_loss(fixed, E)
        if step > 0:
            changed = sum(1 for x, y in zip(sigs, prev_sigs) if x[2] != y[2])
            sections = sum(1 for x, y in zip(sigs, prev_sigs) if x[0] != y[0])
            firsts = sum(1 for x, y in zip(sigs, prev_sigs) if x[1] != y[1])
        else:
            changed = sections = firsts = 0
        prev_sigs = sigs
        print(f'step {step}: fixed comparison {fl:.6f}; trajectories changed {changed}, sections changed {sections}, first locks changed {firsts} (of 32, since the last read)', flush=True)
    opt.lr = lr0 * 0.5 * (1 + np.cos(np.pi * step / steps))
    idx = rng.choice(len(train), batch, replace=False)
    decs = []
    for i in idx:
        req, tgt = train[i]
        _, _, snaps, _ = trajectory(req, E)
        for placed in snaps:
            for j in range(M_ST):
                if j not in placed:
                    decs.append((req, placed, j, tgt[j]))
    loss, GE = batch_loss(decs, E)
    if lr_rho > 0:
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
np.save(f'{DIR}/E_onpolicy_{tname}_{seed}_{ARM}.npy', E)
with open(f'{DIR}/rho_onpolicy_{tname}_{seed}_{ARM}.txt', 'w') as f:
    f.write(repr(model.DECAY[0]) + '\n')
print(f'rho final {model.DECAY[0]}')
print(f'eO_fit {sys.argv[1:]}: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
