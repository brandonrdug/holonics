#!/usr/bin/env -S python3 -I
"""A host control for the pumped carry (the lead, November 19; Neon's note of that day §2): whether a carry that can reflect as well as
turn holds order a commuting carry cannot, at matched parameters, before any arm. Outside the machine; floats, a ruler.

The carry on C circles, each a real plane: `q_t = M(u_t) q_(t−1) + v(u_t)`, read by a linear face `z_t = W [q_t] + c` over the symbols.
- commuting (today's carry): `M(u) = ρ(u) R(θ(u))`, a turn and a scale, so every two moves commute (the abelian scan);
- pumped: `M(u) = ρ(u) R(θ(u)) + σ(u) R(φ(u)) F`, `F` the reflection `diag(1, −1)`, the carry's `α z + β z̄`, whose moves do not commute.
Both scale so `‖M‖ < 1` (a passive carrier): `ρ = 0.98 sigmoid(·)`, and on the pumped carry `ρ + σ ≤ 0.98` by a shared softmax.
The commuting carry gets 2C circles where the pumped one has C, so both hold the same count of parameters a symbol (4 a circle against 2).

The task: Dyck-2 (two bracket kinds, depth at most D), next-symbol prediction. Read at the places where the next symbol must close: the
mass the face gives the right closer among the two closers (`agree`), and its share over 0.9 (`sure`), by depth; a planted readout
(the true stack) reads 1.0. Trained by full backpropagation through time with Adam, the same steps and seeds for both.

Usage: pumped_carry_control.py CIRCLES DEPTH LENGTH STEPS [SEEDS]"""
import sys, math, numpy as np

OPEN, CLOSE = (0, 1), (2, 3)    # ( [ ) ]

def dyck(rng, n, depth):
    s, stack = [], []
    while len(s) < n:
        can_open = len(stack) < depth and len(s) + len(stack) + 2 <= n
        if stack and (not can_open or rng.random() < 0.5):
            s.append(CLOSE[stack.pop()])
        elif can_open:
            k = rng.integers(2); stack.append(k); s.append(OPEN[k])
        else:
            break
    while stack:
        s.append(CLOSE[stack.pop()])
    return s

def batch(rng, b, n, depth):
    seqs = [dyck(rng, n, depth) for _ in range(b)]
    L = max(len(x) for x in seqs)
    X = np.full((b, L), 4); 
    for i, x in enumerate(seqs):
        X[i, :len(x)] = x
    return X    # 4 is the end, read as a fifth symbol

class Model:
    def __init__(self, rng, C, pumped):
        self.C, self.pumped, A = C, pumped, 5
        s = 0.5
        self.p = {"a": rng.normal(0, s, (A, C)), "th": rng.uniform(-math.pi, math.pi, (A, C)), "v": rng.normal(0, s, (A, C, 2)),
                  "W": rng.normal(0, 1 / math.sqrt(2 * C), (2 * C, A)), "c": np.zeros(A)}
        if pumped:
            self.p["b"] = rng.normal(0, s, (A, C)); self.p["ph"] = rng.uniform(-math.pi, math.pi, (A, C)); self.p["r"] = np.zeros((A, C))
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}; self.s2 = {k: np.zeros_like(v) for k, v in self.p.items()}; self.t = 0

    def mats(self, u):
        p = self.p
        if self.pumped:
            # ρ, σ and a rest share 0.98 by a softmax: ρ + σ < 0.98
            e = np.stack([p["a"][u], p["b"][u], p["r"][u]], -1); e = np.exp(e - e.max(-1, keepdims=True)); w = 0.98 * e / e.sum(-1, keepdims=True)
            rho, sig = w[..., 0], w[..., 1]
        else:
            rho, sig = 0.98 / (1 + np.exp(-p["a"][u])), 0 * p["a"][u]
        th = p["th"][u]; ct, st = np.cos(th), np.sin(th)
        M = np.empty(u.shape + (self.C, 2, 2))
        M[..., 0, 0], M[..., 0, 1], M[..., 1, 0], M[..., 1, 1] = rho * ct, -rho * st, rho * st, rho * ct
        if self.pumped:
            ph = p["ph"][u]; cp, sp = np.cos(ph), np.sin(ph)
            # σ R(φ) F = σ [[cos φ, sin φ], [sin φ, −cos φ]]
            M[..., 0, 0] += sig * cp; M[..., 0, 1] += sig * sp; M[..., 1, 0] += sig * sp; M[..., 1, 1] -= sig * cp
        return M, rho, sig

    def forward(self, X):
        B, L = X.shape
        q = np.zeros((B, self.C, 2)); Q = np.zeros((B, L, self.C, 2)); Ms = []
        for t in range(L):
            M, _, _ = self.mats(X[:, t]); Ms.append(M)
            q = np.einsum("bcij,bcj->bci", M, q) + self.p["v"][X[:, t]]
            Q[:, t] = q
        z = Q.reshape(B, L, -1) @ self.p["W"] + self.p["c"]
        return z, Q, Ms

    def loss_grad(self, X):
        B, L = X.shape
        z, Q, Ms = self.forward(X[:, :-1])
        y = X[:, 1:]
        z = z - z.max(-1, keepdims=True); pz = np.exp(z); pz /= pz.sum(-1, keepdims=True)
        mask = (X[:, :-1] != 4).astype(float)
        n = mask.sum()
        loss = -(np.log(pz[np.arange(B)[:, None], np.arange(L - 1)[None], y] + 1e-12) * mask).sum() / n
        dz = pz.copy(); dz[np.arange(B)[:, None], np.arange(L - 1)[None], y] -= 1; dz *= mask[..., None] / n
        g = {k: np.zeros_like(v) for k, v in self.p.items()}
        Qf = Q.reshape(B, L - 1, -1)
        g["W"] = np.einsum("bti,bto->io", Qf, dz); g["c"] = dz.sum((0, 1))
        dQ = (dz @ self.p["W"].T).reshape(B, L - 1, self.C, 2)
        dq = np.zeros((B, self.C, 2))
        dM = []
        for t in range(L - 2, -1, -1):
            dq = dq + dQ[:, t]
            u = X[:, t]
            np.add.at(g["v"], u, dq)
            qprev = Q[:, t - 1] if t > 0 else np.zeros((B, self.C, 2))
            dMt = np.einsum("bci,bcj->bcij", dq, qprev)    # dL/dM
            dM.append((t, dMt))
            dq = np.einsum("bcij,bci->bcj", Ms[t], dq)
        # the matrices' parameters
        for t, dMt in dM:
            u = X[:, t]
            p = self.p
            th = p["th"][u]; ct, st = np.cos(th), np.sin(th)
            if self.pumped:
                e = np.stack([p["a"][u], p["b"][u], p["r"][u]], -1); e = np.exp(e - e.max(-1, keepdims=True)); w = e / e.sum(-1, keepdims=True)
                rho, sig = 0.98 * w[..., 0], 0.98 * w[..., 1]
            else:
                s_ = 1 / (1 + np.exp(-p["a"][u])); rho = 0.98 * s_
            dR = dMt[..., 0, 0] * ct - dMt[..., 0, 1] * st + dMt[..., 1, 0] * st + dMt[..., 1, 1] * ct          # dL/dρ
            dth = rho * (-dMt[..., 0, 0] * st - dMt[..., 0, 1] * ct + dMt[..., 1, 0] * ct - dMt[..., 1, 1] * st)
            np.add.at(g["th"], u, dth)
            if self.pumped:
                ph = p["ph"][u]; cp, sp = np.cos(ph), np.sin(ph)
                dS = dMt[..., 0, 0] * cp + dMt[..., 0, 1] * sp + dMt[..., 1, 0] * sp - dMt[..., 1, 1] * cp
                dph = sig * (-dMt[..., 0, 0] * sp + dMt[..., 0, 1] * cp + dMt[..., 1, 0] * cp + dMt[..., 1, 1] * sp)
                np.add.at(g["ph"], u, dph)
                # softmax: d w_i = w_i (δ_ij − w_j)
                dw = np.stack([dR, dS, np.zeros_like(dR)], -1) * 0.98
                de = w * (dw - (dw * w).sum(-1, keepdims=True))
                np.add.at(g["a"], u, de[..., 0]); np.add.at(g["b"], u, de[..., 1]); np.add.at(g["r"], u, de[..., 2])
            else:
                np.add.at(g["a"], u, dR * 0.98 * s_ * (1 - s_))
        return loss, g

    def step(self, g, lr=0.01):
        self.t += 1
        for k in self.p:
            self.m[k] = 0.9 * self.m[k] + 0.1 * g[k]; self.s2[k] = 0.999 * self.s2[k] + 0.001 * g[k] ** 2
            mh, sh = self.m[k] / (1 - 0.9 ** self.t), self.s2[k] / (1 - 0.999 ** self.t)
            self.p[k] -= lr * mh / (np.sqrt(sh) + 1e-8)

def read(model, X):
    z, _, _ = model.forward(X[:, :-1])
    z = z - z.max(-1, keepdims=True); pz = np.exp(z); pz /= pz.sum(-1, keepdims=True)
    B, L = X.shape
    agree, depths = [], []
    for b in range(B):
        stack = []
        for t in range(L - 1):
            s = X[b, t]
            if s in OPEN: stack.append(OPEN.index(s))
            elif s in CLOSE and stack: stack.pop()
            nxt = X[b, t + 1]
            if nxt in CLOSE:
                want = CLOSE[stack[-1]] if stack else nxt
                other = CLOSE[1 - CLOSE.index(want)]
                agree.append(pz[b, t, want] / (pz[b, t, want] + pz[b, t, other])); depths.append(len(stack))
    agree, depths = np.array(agree), np.array(depths)
    return agree, depths

def main():
    C, depth, n, steps = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    seeds = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    for pumped in (False, True):
        for seed in range(seeds):
            rng = np.random.default_rng(seed)
            model = Model(rng, C if pumped else 2 * C, pumped)
            for it in range(steps):
                X = batch(rng, 32, n, depth)
                loss, g = model.loss_grad(X)
                model.step(g)
            test = np.random.default_rng(1000 + seed)
            agree, depths = read(model, batch(test, 256, n, depth))
            by = " ".join(f"d{d}={agree[depths == d].mean():.3f}" for d in range(1, depth + 1) if (depths == d).any())
            params = sum(v.size for k, v in model.p.items() if k not in ("W", "c"))
            print(f"PUMPED_CONTROL carry={'pumped' if pumped else 'commuting'} circles={model.C} params_a_symbol={params // 5} seed={seed} depth={depth} length={n} steps={steps} train_loss={loss:.4f} agree={agree.mean():.3f} sure={(agree > 0.9).mean():.3f} by_depth: {by}", flush=True)

main()
