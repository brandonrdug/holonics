# Exterior analysis: the best additive-in-past readout (what a linear field's linear features can carry)
import sys, numpy as np
ITERS = int(sys.argv[1]); sys.argv = sys.argv[1:]
data = b"".join(open(p,'rb').read() for p in sys.argv[1:])
d = np.array([x for b in data for x in (b>>6,(b>>4)&3,(b>>2)&3,b&3)], dtype=np.int64)
L = 6
def feats(s, phase_dependent):
    n = len(s); idx = np.arange(L, n); ph = idx % 4
    cols = []
    for lag in range(1, L+1):
        u = s[idx-lag]
        cols.append((ph*4+u) + (lag-1)*16 if phase_dependent else u + (lag-1)*4)
    width = L*(16 if phase_dependent else 4)
    cols.append(width + ph)  # frame bias
    return np.stack(cols,1), width+4, s[idx]
def fit(phase_dependent):
    cut = int(len(d)*0.8)//4*4
    Xtr, W, ytr = feats(d[:cut], phase_dependent); Xte, _, yte = feats(d[cut:], phase_dependent)
    Wt = np.zeros((W,4)); m = np.zeros_like(Wt); v = np.zeros_like(Wt)
    def logits(X): return Wt[X].sum(1)
    import time; t0=time.time()
    for t in range(1, ITERS+1):
        z = logits(Xtr); z -= z.max(1,keepdims=True); p = np.exp(z); p /= p.sum(1,keepdims=True)
        p[np.arange(len(ytr)), ytr] -= 1; g = np.zeros_like(Wt)
        for j in range(Xtr.shape[1]):
            for c in range(4): g[:,c] += np.bincount(Xtr[:,j], weights=p[:,c], minlength=W)
        g /= len(ytr); m = .9*m+.1*g; v = .999*v+.001*g*g
        Wt -= 0.1*(m/(1-.9**t))/(np.sqrt(v/(1-.999**t))+1e-9)
    print('  %d iters %.1f s' % (ITERS, time.time()-t0), flush=True)
    z = logits(Xte); z -= z.max(1,keepdims=True); lp = z - np.log(np.exp(z).sum(1,keepdims=True))
    return -lp[np.arange(len(yte)), yte].mean()/np.log(2)
print("additive lags 1..6 + frame bias:           %.3f bits/digit" % fit(False))
print("additive lags 1..6, weights by frame phase: %.3f bits/digit" % fit(True))
