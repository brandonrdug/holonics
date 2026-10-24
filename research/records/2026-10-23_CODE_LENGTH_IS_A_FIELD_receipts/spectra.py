# Coincidence spectrum of the passage bytes (Kasiski/Friedman) and the power spectrum of the code signal.
# usage: python3 -I spectra.py PASSAGE RUNDIR OUT.json
import json, sys, numpy as np
b = np.frombuffer(open(sys.argv[1], "rb").read(), np.uint8)
R = sys.argv[2]
N = len(b)
cnt = np.bincount(b, minlength=256); p = cnt / N; floor = float((p ** 2).sum())
lags = sorted(set(list(range(1, 1025)) + [int(round(2 ** (k / 16))) for k in range(160, 16 * 21)]))
ic = [float((b[:-l] == b[l:]).mean()) for l in lags]
res = {"bytes": N, "ic_floor": floor, "lags": lags, "ic": ic}
# code signal: node bits a byte; periodogram by FFT, power summed in bins of 1/8 octave of frequency
W = np.fromfile(R + "/whole.f32", "<f4").reshape(-1, 4, 3).sum(1)[:, 1].astype(np.float64)
for name, x in (("code", W), ("lock saving", np.fromfile(R + "/whole.f32", "<f4").reshape(-1, 4, 3).sum(1)[:, 0].astype(np.float64) - W)):
    x = x - x.mean()
    n2 = 1 << int(np.ceil(np.log2(len(x))))
    F = np.fft.rfft(x, n2); P = (F.real ** 2 + F.imag ** 2) / len(x)
    f = np.arange(len(P)) / n2          # cycles a byte
    edges = 2.0 ** (np.arange(-22 * 8, 1) / 8)
    idx = np.digitize(f, edges)
    pb = np.bincount(idx, weights=P, minlength=len(edges) + 1); nb = np.bincount(idx, minlength=len(edges) + 1)
    keep = nb[1:len(edges)] > 0
    centers = np.sqrt(edges[:-1] * edges[1:])[keep]; dens = (pb[1:len(edges)] / np.maximum(nb[1:len(edges)], 1))[keep]
    m = (centers > 1e-4) & (centers < 0.05)
    slope = float(np.polyfit(np.log2(centers[m]), np.log2(dens[m]), 1)[0])
    top = np.argsort(P[1:])[::-1][:12] + 1
    res[name] = {"freq": centers.tolist(), "power": dens.tolist(), "slope_1e-4_to_0.05": slope,
                 "peaks_period_bytes": [float(n2 / k) for k in top], "variance": float(x.var())}
json.dump(res, open(sys.argv[3], "w"))
e = np.array(ic) / floor
print("IC floor (independent draws) %.5f; IC at lags 1..8: %s" % (floor, " ".join("%.4f" % x for x in ic[:8])))
for lo, hi in ((1, 8), (9, 64), (65, 512), (513, 4096), (4097, 65536), (65537, 1 << 21)):
    s = [i for i, l in enumerate(lags) if lo <= l <= hi]
    print("  lags %7d-%-7d IC/floor mean %.3f min %.3f max %.3f" % (lo, hi, e[s].mean(), e[s].min(), e[s].max()))
for name in ("code", "lock saving"):
    print(name, "spectral slope (log2 power per log2 frequency, 1e-4..0.05 cycles a byte): %.3f; strongest periods (bytes): %s" % (res[name]["slope_1e-4_to_0.05"], ", ".join("%.1f" % x for x in res[name]["peaks_period_bytes"][:8])))
