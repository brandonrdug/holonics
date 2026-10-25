"""Where the units' demand is lost on its way to B through the modes' own readers.

FOUND_BY_MODES_AT_B.py found no units crossing at B against G_h, the covector the tower's reverse
sends to level 0's modes (the demand a value placed in a mode meets, carried back through the
mode's own moves from every later read of it). Here the exact crossing chi_1(c0) is scored by its
two channels' canonical share (at most 2) against:
- at the sums' U cells (the cell that codes the result's units; char/block{c}_umode.txt,
  char/block{c}_ucov.txt): every mode's covector G (128), one mode's alone (2 coordinates), and the
  input covector y (64);
- at the sums' B cells (char/block{c}_dmode.txt, _dcov.txt): the same.
If U's own demand on a mode already carries the units' character and B's does not, the transport
loses it; if U's does not, the mode's existing readers do not read the units there, and a value
placed in the mode has no reader at U."""
import importlib.util, time
import numpy as np
t0 = time.time()
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
chi = lambda k, d: np.exp(2j * np.pi * k * np.asarray(d) / 10)

def rows(path):
    out = {}
    for line in open(path):
        if line.startswith("FORMS "):
            p = line.split(); out[int(p[1])] = (int(p[2]), np.array([int(x) for x in p[3:]], dtype=float) / 2**24)
    return out

GU, YU, CU, GB, YB, CB = [], [], [], [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    gm, yv = rows(f"char/block{c}_umode.txt"), rows(f"char/block{c}_ucov.txt")
    for i in gm:
        GU.append(gm[i][1]); YU.append(yv[i][1]); CU.append(text[i + 1] - 48)
    gm, yv = rows(f"char/block{c}_dmode.txt"), rows(f"char/block{c}_dcov.txt")
    for i in gm:
        r = role.get(i + 1, ()); f = info.get(i + 1)
        if "B" in r and f and f[0] == "+":
            GB.append(gm[i][1]); YB.append(yv[i][1]); CB.append(f[3])
GU, YU, CU, GB, YB, CB = map(np.array, (GU, YU, CU, GB, YB, CB))
print(f"U cells {len(CU)} (units 0..9: {np.bincount(CU, minlength=10).min()} to {np.bincount(CU, minlength=10).max()} each); B cells {len(CB)}; read in {time.time() - t0:.1f} s")

def share(c, y):
    C = np.stack([c.real, c.imag], 1); C = C - C.mean(0)
    Y = y.T @ y
    R, G = C.T @ y, C.T @ C
    return np.trace(np.linalg.solve(Y, R.T) @ np.linalg.solve(G, R))

for name, G, Y, C0 in [("U", GU, YU, CU), ("B", GB, YB, CB)]:
    x = chi(1, C0)
    per = np.array([share(x, G[:, 2 * m:2 * m + 2]) for m in range(64)])
    top = np.argsort(per)[::-1][:5]
    print(f"at {name}: chi_1(c0) against every mode's covector {share(x, G):.4f}; against the input covector {share(x, Y):.4f}; "
          f"one mode's alone, the five largest: {', '.join(f'{m} {per[m]:.4f}' for m in top)}; modes 16 {per[16]:.4f}, 41 {per[41]:.4f}; median {np.median(per):.4f}")
    e = (G**2).sum(0); e = e[0::2] + e[1::2]
    print(f"   the demand's energy by mode, the five largest: {', '.join(f'{m} {e[m] / e.sum():.3f}' for m in np.argsort(e)[::-1][:5])}; modes 16 {e[16] / e.sum():.4f}, 41 {e[41] / e.sum():.4f}")
print(f"done in {time.time() - t0:.1f} s")
