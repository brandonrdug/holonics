"""charge_t.py STATE [STATE ...]: a ruler on the host (never machinery; floats, analysis only) for G105 (d), the triads' return's charge: the rms of
w_triad over both lanes' rows (all D rows, its 2J columns) against the rms of W's plain contacts' columns over the first lane's rows, as G87's W
line read the circles' columns against the plain ones. The plain contacts are the first f/2 - C of each half (columns e and f/2 + e for e < f/2 - C);
the first lane's rows are rows 0 to D/lanes. Both families are on the material's grain, so the ratio needs no unit; each rms is also printed in the
family's own unit (entry / 2^24). Reads the layout through tools/state_travel.py (the directory in HOLONICS_TOOLS, default tools), which knows the
hnn-field-v14f head. One thread; reads a saved state, writes nothing."""
import os, sys
sys.path.insert(0, os.environ.get("HOLONICS_TOOLS", "tools"))
import numpy as np
import state_travel

MAT = 24
for path in sys.argv[1:]:
    d, theta = state_travel.state(path)
    fam, _ = state_travel.layout(d)
    at = {name: (start, shape) for name, start, shape, _ in fam}
    dw, f, lanes, c, j = d["width"], d["contacts"], d["lanes"], d.get("carry", 0), d.get("triads", 0)
    rows = dw // lanes if lanes > 1 else dw
    plain = f // 2 - c
    w0, ws = at["w"]
    w = theta[w0:w0 + dw * f].reshape(dw, f).astype(np.float64)
    cols = np.r_[0:plain, f // 2:f // 2 + plain]
    wp = w[:rows][:, cols]
    rms_w = float(np.sqrt((wp ** 2).mean()))
    if j > 0:
        t0, _ = at["w_triad"]
        wt = theta[t0:t0 + dw * 2 * j].reshape(dw, 2 * j).astype(np.float64)
        rms_t = float(np.sqrt((wt ** 2).mean()))
        n_t = wt.size
    else:
        rms_t, n_t = float("nan"), 0
    ratio = rms_t / rms_w if rms_w > 0 else float("nan")
    print(f"CHARGE {os.path.basename(os.path.dirname(path)) or '.'}/{os.path.basename(path)} triads={j} circles={c} w_triad_entries={n_t} "
          f"w_triad_rms={rms_t:.6g} ({rms_t / 2 ** MAT:.6g} in its unit) w_plain_entries={wp.size} w_plain_rms={rms_w:.6g} "
          f"({rms_w / 2 ** MAT:.6g} in its unit) ratio={ratio:.4f}")
