# Exterior read: each mode's per-cell move lambda_t at the held-out units cells, before and after a
# pass; the turn's change in radians and in the line's widths (1-|lambda|). usage: before after [mode]
import sys, numpy as np
def load(p):
    out = []
    for line in open(p):
        if not line.startswith("MODES"): continue
        lv = [seg for seg in line.split() if seg.startswith("L0=")][0][3:]
        out.append([[int(v) for v in m.split(",")] for m in lv.split(";")])
    return np.array(out, dtype=np.float64)  # cells x modes x 10
a, b = load(sys.argv[1]), load(sys.argv[2])
la = (a[:, :, 6] + 1j * a[:, :, 7]) / 2**30
lb = (b[:, :, 6] + 1j * b[:, :, 7]) / 2**30
turn = np.angle(lb * np.conj(la))           # cells x modes
width = 1 - np.abs(la)
mean_turn = np.angle(np.exp(1j * turn).mean(0))
spread = np.abs(np.exp(1j * turn).mean(0))
w = np.median(width, 0)
order = np.argsort(-np.abs(mean_turn) / w)
print("mode  width(1-|l|)  memory  mean turn change rad  in widths  coherence")
for k in list(order[:8]) + ([int(sys.argv[3])] if len(sys.argv) > 3 else []):
    print(f"{k:4d}  {w[k]:.2e}  {1/w[k]:8.0f}  {mean_turn[k]:+.4f}  {mean_turn[k]/w[k]:+9.1f}  {spread[k]:.3f}")
print(f"median over modes of |turn change|/width: {np.median(np.abs(mean_turn)/w):.2f}")
