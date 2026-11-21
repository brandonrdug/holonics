"""A planted tick for the leak's balance (host, synthetic; no state of the machine is read).

One lane of n places, read at unit power. The tick adds g(r) = r* + B (r - r*) to the lane, B a transverse block with
planted exponents nu_j (a third released, a third held, a third boosted, the extremes of the lead's read) and a shear
that raises its largest singular value to about six. The lane's store: x <- x/(1 + d) + g, d its friction.
Read: (1) the built tick (d = 0) against the power laws, (2) a scan of the leak for the rate of contraction and the
cosine of successive moves of the ray, (3) the friction deposited by that cosine from zero, (4) the same with a planted
flip (nu = -1.5), (5) the same with the arrivals jittered.
"""
import numpy as np
rng = np.random.default_rng(20261121)
n = 97

def planted(nu_min=-0.54, nu_max=0.19, flip=None, shear=6.0, sparse=False):
    m = n - 1
    third = m // 3
    nus = np.concatenate([np.linspace(nu_min, -0.02, third), np.linspace(-0.02, 0.02, third), np.linspace(0.02, nu_max, m - 2 * third)])
    if flip is not None:
        nus[0] = flip
    rng.shuffle(nus)
    U = np.triu(rng.standard_normal((m, m)), 1)
    if sparse:
        keep = np.zeros((m, m)); idx = rng.permutation(m - 1)[:6]
        for i in idx:
            keep[i, i + 1] = 1.0
        U = U * keep
    T = np.diag(nus) + U
    # scale the shear so the top singular value is the asked one
    lo, hi = 0.0, 10.0
    for _ in range(60):
        mid = (lo + hi) / 2
        s = np.linalg.svd(np.diag(nus) + mid * U, compute_uv=False)[0]
        lo, hi = (mid, hi) if s < shear else (lo, mid)
    T = np.diag(nus) + lo * U
    Qm, _ = np.linalg.qr(rng.standard_normal((m, m)))
    Bt = Qm @ T @ Qm.T
    B = np.zeros((n, n)); B[1:, 1:] = Bt
    return B, nus

def run(B, d, ticks, jitter=0.0, x0=None, seed=0):
    r_star = np.zeros(n); r_star[0] = 1.0
    g_rng = np.random.default_rng(seed)
    x = x0.copy()
    rays = [x / np.linalg.norm(x)]
    fills = []
    for k in range(ticks):
        r = x / np.linalg.norm(x)
        g = r_star + B @ (r - r_star)
        if jitter:
            e = g_rng.standard_normal(n); e[0] = 0.0
            g = g + jitter * e / np.sqrt(n)
        fills.append(np.linalg.norm(x) / np.linalg.norm(g))
        x = x / (1.0 + d) + g
        rays.append(x / np.linalg.norm(x))
    return np.array(rays), np.array(fills)

def moves(rays):
    return rays[1:] - rays[:-1]

def cos_pairs(mv, lo=1):
    num = sum(float(mv[k] @ mv[k - 1]) for k in range(lo, len(mv)))
    den = sum(float(np.linalg.norm(mv[k]) * np.linalg.norm(mv[k - 1])) for k in range(lo, len(mv)))
    return num / den

def opening(seed):
    r = np.random.default_rng(1000 + seed)
    x0 = r.standard_normal(n) * 0.35; x0[0] = 1.0
    return x0

B, nus = planted()
print(f"PLANT n={n} nu in [{nus.min():+.2f}, {nus.max():+.2f}] top_singular={np.linalg.svd(B, compute_uv=False)[0]:.2f} max_abs_eig={np.abs(np.linalg.eigvals(B[1:,1:])).max():.2f}")

# (1) the built tick
rays, fills = run(B, 0.0, 400, x0=opening(0))
mv = moves(rays); nm = np.linalg.norm(mv, axis=1)
for k in (50, 100, 200, 399):
    F = fills[k - 1]
    print(f"BUILT k={k} fill={fills[k]:.1f} move_ratio={nm[k]/nm[k-1]:.4f} law (F+nu_max)/(F+2)={(F+nus.max())/(F+2):.4f} cos_successive={float(mv[k]@mv[k-1])/(nm[k]*nm[k-1]):+.3f}")
print(f"BUILT 17 ticks: cos of successive moves pooled from tick 1: {cos_pairs(moves(run(B,0.0,17,x0=opening(0))[0])):+.3f}; ray's distance from the fixed ray at ticks 4, 17, 400: " + " ".join(f"{np.degrees(np.arccos(min(1,rays[k][0]))):.2f}" for k in (4, 17, 400)) + " degrees")

# (2) a scan of the leak
print("SCAN delta fill_at_rest late_rate(law) late_rate(read) cos_late cos_pooled_17 cos_pooled_4 worst_transient")
emin, emax = 1 - nus.max(), 1 - nus.min()
for delta in (0.125, 0.25, 0.5, 0.75, 0.80, 0.85, 0.90, 1.0):
    d = delta / (1 - delta) if delta < 1 else 1e12
    rays, fills = run(B, d, 60, x0=opening(0))
    dev = np.array([np.linalg.norm(r - np.eye(n)[0]) for r in rays])
    live = [k for k in range(20, 60) if dev[k] > 1e-13 and dev[k - 1] > 1e-13]
    rate = float(np.exp(np.mean([np.log(dev[k] / dev[k - 1]) for k in live[-10:]]))) if len(live) >= 10 else float('nan')
    mv = moves(rays)
    late = [k for k in range(8, 40) if np.linalg.norm(mv[k]) > 1e-12]
    cl = np.mean([float(mv[k] @ mv[k - 1]) / (np.linalg.norm(mv[k]) * np.linalg.norm(mv[k - 1])) for k in late[-8:]]) if late else float('nan')
    c17 = np.mean([cos_pairs(moves(run(B, d, 17, x0=opening(s))[0])) for s in range(16)])
    c4 = np.mean([cos_pairs(moves(run(B, d, 4, x0=opening(s))[0])) for s in range(16)])
    law = max(abs(1 - delta * emin), abs(1 - delta * emax))
    print(f"SCAN {delta:.3f} {fills[-1]:.3f} {law:.3f} {rate:.3f} {cl:+.3f} {c17:+.3f} {c4:+.3f} {dev.max()/dev[0]:.2f}")
print(f"SCAN law: the late cosine changes sign at delta*=2/(eps_min+eps_max)={2/(emin+emax):.3f}, rate there {(emax-emin)/(emax+emin):.3f}")

# (3)-(5) the friction deposited by the cosine of successive moves of the ray, from zero
def deposit(B, ticks, jitter=0.0, laps=400, eta=0.05, label=""):
    u = 0.0   # the store's word: delta = u, d = u/(1-u); founded at zero
    trace = []
    for lap in range(laps):
        d = u / (1 - u)
        cs = [cos_pairs(moves(run(B, d, ticks, jitter=jitter, x0=opening(lap * 8 + s), seed=lap * 8 + s)[0])) for s in range(8)]
        c = float(np.mean(cs))
        u = min(0.98, max(0.0, u + eta * c))
        trace.append((u, c))
    us = np.array([t[0] for t in trace[-100:]]); cs = np.array([t[1] for t in trace[-100:]])
    first = trace[0][1]
    print(f"DEPOSIT {label} ticks={ticks} jitter={jitter}: first cosine at zero {first:+.3f}; rests at delta={us.mean():.3f} (spread {us.std():.3f}), Q={1/us.mean():.2f}, cosine there {cs.mean():+.3f}")
    return us.mean()

deposit(B, 17, label="planted")
deposit(B, 4, label="planted")
Bf, nf = planted(flip=-1.5)
print(f"FLIP planted nu_min={nf.min():+.2f}: a replacement (delta=1) multiplies it by {nf.min():+.2f} a tick; law delta*={2/((1-nf.max())+(1-nf.min())):.3f}")
deposit(Bf, 17, label="flip")
deposit(Bf, 4, label="flip")
for j in (0.05, 0.2, 0.5):
    deposit(B, 17, jitter=j, label="jittered")

Bs, ns = planted(sparse=True)
print(f"SPARSE planted: six entries above the diagonal, top_singular={np.linalg.svd(Bs, compute_uv=False)[0]:.2f}")
rays, fills = run(Bs, 0.0, 400, x0=opening(0)); mv = moves(rays); nm = np.linalg.norm(mv, axis=1)
for k in (8, 16, 50, 200):
    F = fills[k - 1]
    print(f"SPARSE BUILT k={k} fill={fills[k]:.1f} move_ratio={nm[k]/nm[k-1]:.4f} law={(F+ns.max())/(F+2):.4f} cos={float(mv[k]@mv[k-1])/(nm[k]*nm[k-1]):+.3f}")
for delta in (0.25, 0.5, 0.75, 0.85, 1.0):
    d = delta / (1 - delta) if delta < 1 else 1e12
    rays, fills = run(Bs, d, 60, x0=opening(0))
    dev = np.array([np.linalg.norm(r - np.eye(n)[0]) for r in rays])
    live = [k for k in range(8, 60) if dev[k] > 1e-13 and dev[k - 1] > 1e-13]
    rate = float(np.exp(np.mean([np.log(dev[k] / dev[k - 1]) for k in live[-10:]])))
    t12 = next((k for k in range(len(dev)) if dev[k] <= dev[4] * 2.0**-12), None)
    law = max(abs(1 - delta * (1 - ns.max())), abs(1 - delta * (1 - ns.min())))
    c17 = np.mean([cos_pairs(moves(run(Bs, d, 17, x0=opening(s_))[0])) for s_ in range(16)])
    print(f"SPARSE SCAN delta={delta:.2f} law={law:.3f} read={rate:.3f} cos_pooled_17={c17:+.3f} first_tick_2^-12_below_tick_4={t12}")
deposit(Bs, 17, label="sparse")
deposit(Bs, 4, label="sparse")
# the full shear's ticks to a tolerance
for delta in (0.5, 0.75, 0.85):
    d = delta / (1 - delta)
    rays, fills = run(B, d, 200, x0=opening(0))
    dev = np.array([np.linalg.norm(r - np.eye(n)[0]) for r in rays])
    t12 = next((k for k in range(len(dev)) if dev[k] <= dev[4] * 2.0**-12), None)
    print(f"FULL SCAN delta={delta:.2f} first_tick_2^-12_below_tick_4={t12}")
