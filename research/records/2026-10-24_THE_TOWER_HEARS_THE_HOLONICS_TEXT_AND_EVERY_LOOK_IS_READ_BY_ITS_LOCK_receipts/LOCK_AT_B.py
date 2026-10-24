"""Does the tower's own state mark the place where a sum's units are crossed? Among the cells of the
held-out equations where a digit arrives, level 0's state before it arrives (hcont2, the full mode
read of every cell, modes/dev_full_p7.txt) is read for the cells where a second operand's units
arrive (B) against every other digit arrival. In residues first: each mode's phase in 16 sectors,
and each pair of loud modes' relative phase in 16 sectors, scored by the information the sector
carries about B (bits) and by the best single sector's recall and precision. Beside it, for scale
only, a straight-line separator fitted on half the lines and read on the other half."""
import math, collections, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
text = open("htext2/dev_arithmetic.txt", "rb").read()
role, info = tm.probe_roles(text)
line_of = np.cumsum([0] + [1 if x == 10 else 0 for x in text])  # line index of each position
H, B, S, L = [], [], [], []
for i, _, _, levels in tm.parse("modes/dev_full_p7.txt", True):
    if not (48 <= text[i] <= 57):
        continue
    H.append([complex(m[0], m[1]) for m in levels[0]])
    r = role.get(i + 1, ())
    B.append("B" in r); S.append("B" in r and info[i + 1][0] == "+"); L.append(line_of[i])
H, B, S, L = np.array(H), np.array(B), np.array(S), np.array(L)
print(f"digit arrivals {len(H)}; second operand's units arrivals (B) {B.sum()}, of them sums {S.sum()}")
energy = (np.abs(H) ** 2).mean(0); order = np.argsort(-energy); share = energy / energy.sum()
print("loudest modes at digit arrivals (mode: share of energy):", ", ".join(f"{k}: {share[k]:.3f}" for k in order[:8]))

def info_bits(sector, target):
    n = len(target); p1 = target.mean()
    h = -(p1 * math.log2(p1) + (1 - p1) * math.log2(1 - p1))
    cond = 0.0; best = (0, 0, 0)
    for s in np.unique(sector):
        m = sector == s; q = target[m].mean()
        if 0 < q < 1: cond += m.mean() * -(q * math.log2(q) + (1 - q) * math.log2(1 - q))
        rec, prec = target[m].sum() / target.sum(), q
        if rec * prec > best[0] * best[1]: best = (rec, prec, s)
    return h - cond, h, best

for name, target in (("B, all three operations", B), ("B of sums", S)):
    rows = []
    for k in range(H.shape[1]):
        sec = np.floor((np.angle(H[:, k]) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
        g, h, best = info_bits(sec, target); rows.append((g, f"mode {k}", best))
    loud = order[:12]
    for x in range(len(loud)):
        for y in range(x + 1, len(loud)):
            j, k = loud[x], loud[y]
            sec = np.floor((np.angle(H[:, j] * np.conj(H[:, k])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
            g, h, best = info_bits(sec, target); rows.append((g, f"modes {j}-{k}", best))
    rows.sort(key=lambda r: -r[0])
    print(f"{name}: H = {h:.3f} bits; the most informative phases:")
    for g, lab, (rec, prec, s) in rows[:6]:
        print(f"  {lab}: {g:.3f} bits ({g / h:.2f} of H); best sector {s}: recall {rec:.2f}, precision {prec:.2f}")
    # for scale only: a straight-line separator, fitted on the even lines and read on the odd
    X = np.hstack([H.real, H.imag]) / 2**14
    tr, te = L % 2 == 0, L % 2 == 1
    A = np.hstack([X, np.ones((len(X), 1))])
    w = np.linalg.solve(A[tr].T @ A[tr] + np.eye(A.shape[1]), A[tr].T @ target[tr].astype(float))
    score = A[te] @ w; t = target[te]
    rank = np.argsort(-score); k = t.sum()
    prec_at_k = t[rank[:k]].mean()
    print(f"  straight-line separator, odd lines: of the {k} highest scores, {prec_at_k:.2f} are {name}")
