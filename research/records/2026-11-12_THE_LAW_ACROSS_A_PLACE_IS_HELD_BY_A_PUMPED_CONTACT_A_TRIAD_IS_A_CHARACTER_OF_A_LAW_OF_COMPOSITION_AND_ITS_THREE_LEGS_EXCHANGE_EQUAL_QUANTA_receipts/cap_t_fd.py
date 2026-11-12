# The ruler's own check (host, floats): cap_t.py's analytic gradients against central differences at three triads. Run with
# CAP_T_SYNTH=1 on the drawn law (no passage), or on the passage beside yard.py. Log: cap_t_fd.log.txt.
import numpy as np, sys, runpy
sys.argv = ['cap_t.py', '1', '3', '0']
g = runpy.run_path('cap_t.py', run_name='x')
a, b, U, V, W, grads, Lc, Rc, cnt, N = (g[k] for k in ('a', 'b', 'U', 'V', 'W', 'grads', 'Lc', 'Rc', 'cnt', 'N'))
def loss():
    Z = (a[Lc].astype(np.float64) + b[Rc] + ((U[Lc] * V[Rc]) @ W.T).real); Z -= Z.max(1, keepdims=True)
    return -float((cnt * (Z - np.log(np.exp(Z).sum(1, keepdims=True)))).sum()) / N
_, G = grads()
for name, p, gp in (('a', a, G[0]), ('U', U, G[2]), ('V', V, G[3]), ('W', W, G[4])):
    idx = (1, 2) if p.ndim == 2 else (1,)
    for part, delta in (('re', 1e-3), ('im', 1e-3j)):
        if part == 'im' and not np.iscomplexobj(p): continue
        p[idx] += delta; lp = loss(); p[idx] -= 2 * delta; lm = loss(); p[idx] += delta
        fd = (lp - lm) / 2e-3; an = gp[idx].real if part == 're' else gp[idx].imag
        print(name, part, 'fd %.6f analytic %.6f' % (fd, an))
