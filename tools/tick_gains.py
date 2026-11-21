"""A ruler for the tick's gains (the lattice record of November 20, §6.1's read before any leak is built): the eigenvalues of one site's
block of the tick's reading-then-writing map, read by central differences on the host (`the_ticks_gains_by_finite_differences` writes
`probe_k{k}_t{t}.txt`: the site's opening and settled blocks, each entry's `eps`, and for each entry `d` the block's `x+ - x-` after the
tick), each eigenvalue's distance from one multiplied by the site's fill in ticks, `nu = (lambda - 1) * fill`.

Two fills are read: the tick count `k + 1` (the opening and `k` ticks summed), and each lane's own, `|x^k_l| / |x^(k+1)_l - x^k_l|` (the
state over one tick's current), the site's the median of its lanes'. The rays: the eigenvalues within `RAY` of one. Outside the machine;
floats on the host, a ruler.

Usage: python3 -I tick_gains.py DIR [GUESS]"""
import sys, os, re, glob
import numpy as np

RAY = 0.01


def read(path):
    head = None
    cols = {}
    for line in open(path):
        parts = line.split()
        if parts[0] == 'k':
            head = dict(zip(parts[0::2], map(int, parts[1::2])))
        elif parts[0] in ('before', 'after', 'eps'):
            head[parts[0]] = np.array(list(map(int, parts[1:])), dtype=np.float64)
        elif parts[0] == 'col':
            cols[int(parts[1])] = np.array(list(map(int, parts[2:])), dtype=np.float64)
    dw = head['dw']
    J = np.zeros((dw, dw))
    for d in range(dw):
        J[:, d] = cols[d] / (2.0 * head['eps'][d])
    return head, J


def main():
    root = sys.argv[1]
    files = sorted(glob.glob(os.path.join(root, 'probe_k*_t*.txt')), key=lambda p: tuple(map(int, re.findall(r'\d+', os.path.basename(p)))))
    table = {}
    for path in files:
        head, J = read(path)
        k, t, dw, lanes = head['k'], head['t'], head['dw'], head['lanes']
        lw = dw // lanes
        x0, x1 = head['before'], head['after']
        fills = []
        for l in range(lanes):
            a, b = x0[l * lw:(l + 1) * lw], x1[l * lw:(l + 1) * lw]
            step = np.linalg.norm(b - a)
            fills.append(np.linalg.norm(a) / step if step > 0 else float('inf'))
        fill_lane = float(np.median(fills))
        lam = np.linalg.eigvals(J)
        dist = np.abs(lam - 1.0)
        order = np.argsort(dist)
        rays = int(np.sum(dist < RAY))
        rest = dist[dist >= RAY]
        # nu on the real part (a turn's imaginary part is read beside it)
        nu_k = (lam.real - 1.0) * (k + 1)
        nu_f = (lam.real - 1.0) * fill_lane
        # lane-diagonal blocks: each lane's own gains
        lane_rays = []
        for l in range(lanes):
            ll = np.linalg.eigvals(J[l * lw:(l + 1) * lw, l * lw:(l + 1) * lw])
            lane_rays.append(int(np.sum(np.abs(ll - 1.0) < RAY)))
        cross = np.linalg.norm(J - np.kron(np.eye(lanes), np.ones((lw, lw))) * J) / max(np.linalg.norm(J - np.eye(dw)), 1e-30)
        table[(t, k)] = dict(lam=lam, dist=dist, nu_k=nu_k, nu_f=nu_f, fill_lane=fill_lane, fills=fills, open=head['open'])
        q = lambda v, p: float(np.percentile(v, p)) if len(v) else float('nan')
        print(f"GAINS t={t} open={head['open']} k={k} fill_ticks={k + 1} fill_lanes_median={fill_lane:.2f} fill_lanes=[{' '.join(f'{f:.1f}' for f in fills)}]"
              f" rays_within_{RAY}={rays} lane_block_rays=[{' '.join(map(str, lane_rays))}] complex={int(np.sum(np.abs(lam.imag) > 1e-9))}"
              f" max_abs={np.max(np.abs(lam)):.4f} min_abs={np.min(np.abs(lam)):.4f}"
              f" dist_rest_p10={q(rest, 10):.4f} p50={q(rest, 50):.4f} p90={q(rest, 90):.4f}"
              f" off_lane_share={cross:.3f}")
        nearest = ' '.join(f'{lam[i].real:.4f}{lam[i].imag:+.4f}i' for i in order[:10])
        print(f"GAINS_NEAREST_ONE t={t} k={k} {nearest}")
        top = np.argsort(-np.abs(lam))[:6]
        print(f"GAINS_LARGEST t={t} k={k} {' '.join(f'{lam[i].real:.4f}{lam[i].imag:+.4f}i' for i in top)}")
    # across ticks: sorted nu at matched ranks
    sites = sorted({t for t, _ in table})
    for t in sites:
        ks = sorted(k for tt, k in table if tt == t)
        if len(ks) < 2:
            continue
        for name in ('nu_k', 'nu_f'):
            sv = {k: np.sort(table[(t, k)][name]) for k in ks}
            line = []
            for a, b in zip(ks, ks[1:]):
                va, vb = sv[a], sv[b]
                mask = (np.abs(va) > 1e-6) & (np.abs(vb) > 1e-6)
                rel = np.abs(vb[mask] - va[mask]) / np.maximum(np.abs(va[mask]), np.abs(vb[mask]))
                line.append(f"{a}->{b}:median_rel_diff={np.median(rel):.3f},within_quarter={np.mean(rel < 0.25):.3f}")
            m = np.abs(sv[ks[-1]])
            m = m[m > 1e-6]
            spread = np.percentile(m, 90) / np.percentile(m, 10) if len(m) else float('nan')
            quart = [f"{k}:p10={np.percentile(sv[k], 10):.3f},p50={np.percentile(sv[k], 50):.3f},p90={np.percentile(sv[k], 90):.3f}" for k in ks]
            print(f"NU t={t} fill={name[3:]} {' '.join(line)} spread_p90_over_p10={spread:.2f} {' '.join(quart)}")
        # the split by nu on the lanes' fill: kept (|nu| under each bound), released (nu below), amplified (nu above)
        for k in ks:
            v = table[(t, k)]['nu_f']
            cuts = ' '.join(f"|nu|<{c}:{int(np.sum(np.abs(v) < c))}" for c in (0.005, 0.01, 0.02, 0.05))
            print(f"SPLIT t={t} k={k} {cuts} released_nu<-0.02:{int(np.sum(v < -0.02))} amplified_nu>0.02:{int(np.sum(v > 0.02))} of {len(v)}"
                  f" min_nu={v.min():.3f} max_nu={v.max():.3f}")
        # the distances' halving from one tick to the next of the read
        for a, b in zip(ks, ks[1:]):
            da = np.median(table[(t, a)]['dist'][table[(t, a)]['dist'] >= RAY])
            db = np.median(table[(t, b)]['dist'][table[(t, b)]['dist'] >= RAY])
            print(f"HALVING t={t} {a}->{b} median_dist {da:.4f} -> {db:.4f} ratio={db / da:.3f}")


if __name__ == '__main__':
    main()
