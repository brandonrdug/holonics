# Exterior read: the ring's face at the held-out units cells, read by nearest mean direction with
# each cell left out (the outside read of the record). usage: AT_FILE...
import sys, numpy as np
for p in sys.argv[1:]:
    rows = [l.split() for l in open(p) if l.startswith("FORMS")]
    y = np.array([int(r[2]) for r in rows]); x = np.array([[float(v) for v in r[3:5]] for r in rows])
    z = x[:, 0] + 1j * x[:, 1]; u = z / np.maximum(np.abs(z), 1e-9)
    classes = sorted(set(y)); right = 0
    sums = {c: u[y == c].sum() for c in classes}; counts = {c: (y == c).sum() for c in classes}
    for i in range(len(y)):
        best, arg = None, None
        for c in classes:
            m = sums[c] - (u[i] if y[i] == c else 0)
            if counts[c] - (y[i] == c) == 0: continue
            s = (u[i] * np.conj(m)).real / max(abs(m), 1e-12)
            if best is None or s > best: best, arg = s, c
        right += arg == y[i]
    turns = {chr(c): np.degrees(np.angle(sums[c])) % 360 for c in classes}
    print(p, "outside read", right, "of", len(y), " mean turns", " ".join(f"{k}:{v:.0f}" for k, v in turns.items()))
