"""Exterior optimizers (float, Adam) for E on (i) the executed bank's decision (log-growth logits) and
(ii) the face's code; evaluation of the executed lock (teacher-forced decisions and the generation
lock iteration of generate_by_bank)."""
from common import *

LIMIT = 2.5 / P * (1 - 1 / 64)   # the signed form 2.5 I - p R(c) >= 0 needs p|c| <= 5/2; kept inside


def executed_loss_grad(Cs, tg, E, tau=1.0, penalty=64.0):
    z = to_turn(storage_nodes(Cs, E))
    a, G, members, cert = joint_growth(z, P, want_grad=True)
    a = a.reshape(-1, CLASSES)
    logits = np.log(a) / tau
    logits -= logits.max(1, keepdims=True)
    sm = np.exp(logits)
    sm /= sm.sum(1, keepdims=True)
    n = len(tg)
    q = np.zeros_like(sm)
    q[np.arange(n), tg] = 1
    loss = -np.log(sm[np.arange(n), tg] + 1e-300).mean()
    coef = ((sm - q) / tau / a).reshape(-1) / n          # d loss / d a_y
    Gt = G * coef[:, None]
    # the signed-form barrier on every tick
    mag = np.abs(z)
    over = np.maximum(mag - LIMIT, 0)
    loss += penalty * (over ** 2).sum() / n
    Gt = Gt + penalty * 2 * over * z / np.maximum(mag, 1e-300) / n
    GE = grad_E_from_node(Cs, Gt[:, ::-1])
    return loss, GE, a, cert.reshape(-1, CLASSES).all(1)


def face_loss_grad(Cs, tg, E):
    z = to_turn(storage_nodes(Cs, E))
    A, G = face(z, P, want_grad=True)
    A = A.reshape(-1, CLASSES)
    n = len(tg)
    tot = A.sum(1)
    at = A[np.arange(n), tg]
    loss = (np.log(tot) - np.log(at)).mean()
    coef = (1 / tot)[:, None] - np.eye(CLASSES)[tg] / at[:, None]
    Gt = G * (coef.reshape(-1) / n)[:, None]
    GE = grad_E_from_node(Cs, Gt[:, ::-1])
    return loss, GE, A


class Adam:
    def __init__(self, shape, lr):
        self.m = np.zeros(shape, complex)
        self.v = np.zeros(shape)
        self.lr = lr
        self.t = 0

    def step(self, g):
        self.t += 1
        self.m = 0.9 * self.m + 0.1 * g
        self.v = 0.999 * self.v + 0.001 * np.abs(g) ** 2
        mh = self.m / (1 - 0.9 ** self.t)
        vh = self.v / (1 - 0.999 ** self.t)
        return -self.lr * mh / (np.sqrt(vh) + 1e-12)


def accuracy(decs, E, chunk=2048):
    right = 0
    cert = 0
    tops = []
    for i in range(0, len(decs), chunk // CLASSES):
        part = decs[i:i + chunk // CLASSES]
        Cs, tg = counts_of(part)
        r = read(Cs, E)
        top = r['a'].argmax(1)
        tops.append(top)
        right += int((top == tg).sum())
        cert += int(r['cert'].all(1).sum())
    return right, cert


def face_accuracy(decs, E):
    Cs, tg = counts_of(decs)
    r = read(Cs, E, want_face=True)
    return int((r['A'].argmax(1) == tg).sum()), int((r['A'].argmax(1) == r['a'].argmax(1)).sum())


def generate(req, E, p=P):
    """generate_by_bank's lock iteration in float: every unlocked station's candidates read; a station
    locks when its top exceeds every other and its growth passes one; the largest gap locks."""
    locked = {}
    while len(locked) < M_ST:
        open_st = [j for j in range(M_ST) if j not in locked]
        Cs = np.concatenate([candidates_counts(req, locked, j) for j in open_st])
        a = read(Cs, E, p)['a']
        best = None
        for k, j in enumerate(open_st):
            row = a[k]
            top = int(row.argmax())
            runner = np.sort(row)[-2]
            gap = row[top] - runner
            if row[top] > 1 and gap > 0 and (best is None or gap > best[2]):
                best = (j, top, gap)
        if best is None:
            return [locked.get(j, -1) for j in range(M_ST)], False
        locked[best[0]] = best[1]
    return [locked[j] for j in range(M_ST)], True


def generation_score(pairs, E):
    released = right = right_all = 0
    for req, tgt in pairs:
        sec, ok = generate(req, E)
        hits = sum(int(a == b) for a, b in zip(sec, tgt))
        right_all += hits
        if ok:
            released += 1
            right += hits
    return released, right, right_all
