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


if __name__ == '__main__' and '--leak' not in sys.argv and '--polygons' not in sys.argv:
    main()


def leak(root):
    """`--leak`: the first descent of a leak founded at zero, `M = Σ λ^(k+1) x^kᵀ` (`grad_all.txt`, `grad_t{t}.txt`), against the tick's own
    block at its last tick (`probe_k{k}_t{t}.txt`): each eigenvalue's first-order change under `J − ηM`, `−(W M V)_jj` with `W = V⁻¹`, by the
    mode's kind on the lanes' fill (boosted `ν > 0.02`, held `|ν| ≤ 0.02`, released `ν < −0.02`)."""
    def mat(path):
        return np.array([[float(v) for v in line.split()] for line in open(path)])
    m_all = mat(os.path.join(root, 'grad_all.txt'))
    sv = np.linalg.svd(m_all, compute_uv=False)
    print(f"LEAK_M region top_singular_share={sv[0] ** 2 / np.sum(sv ** 2):.3f} top5={' '.join(f'{v / sv[0]:.3f}' for v in sv[:5])}")
    for path in sorted(glob.glob(os.path.join(root, 'probe_k*_t*.txt'))):
        head, J = read(path)
        k, t, dw, lanes = head['k'], head['t'], head['dw'], head['lanes']
        lw = dw // lanes
        x0, x1 = head['before'], head['after']
        fill = float(np.median([np.linalg.norm(x0[l * lw:(l + 1) * lw]) / max(np.linalg.norm(x1[l * lw:(l + 1) * lw] - x0[l * lw:(l + 1) * lw]), 1e-30) for l in range(lanes)]))
        lam, V = np.linalg.eig(J)
        W = np.linalg.inv(V)
        nu = (lam.real - 1.0) * fill
        kinds = {'boosted': nu > 0.02, 'held': np.abs(nu) <= 0.02, 'released': nu < -0.02}
        for name, M in (('region', m_all), ('site', mat(os.path.join(root, f'grad_t{t}.txt')))):
            d = -np.einsum('ij,jk,ki->i', W, M, V)
            d = d / max(np.max(np.abs(d)), 1e-300)
            parts = []
            for kind, mask in kinds.items():
                if mask.sum() == 0:
                    parts.append(f"{kind}:0")
                    continue
                parts.append(f"{kind}:n={int(mask.sum())},lowered={np.mean(d[mask].real < 0):.2f},median_abs={np.median(np.abs(d[mask])):.3f}")
            print(f"LEAK t={t} open={head['open']} k={k} fill={fill:.2f} M={name} {' '.join(parts)}")


if __name__ == '__main__' and '--leak' in sys.argv:
    leak(sys.argv[1])
    sys.exit(0)


def polygons(root):
    """`--polygons`: each site map's grains (its singular values on the material's grain `2^(-24)`), counted by octave, the polygon's breaks
    (the sorted ranks where the octave changes) and, for the square `read`, the rates (its eigenvalues' moduli) against the grains: the
    cumulative sums of `log2` of each, where they touch (the part splits there, `hodge.newton-above-hodge-is-a-mixing`)."""
    for path in sorted(glob.glob(os.path.join(root, 'map_*.txt'))):
        name = os.path.basename(path)[4:-4]
        lines = open(path).read().split('\n')
        rows, cols = map(int, lines[0].split())
        A = np.array([[float(v) for v in l.split()] for l in lines[1:1 + rows]]) / 2.0 ** 24
        sv = np.linalg.svd(A, compute_uv=False)
        sv = sv[sv > 0]
        o = np.floor(np.log2(sv)).astype(int)
        counts = {k: int(np.sum(o == k)) for k in range(o.max(), o.min() - 1, -1)}
        occupied = [c for c in counts.values() if c > 0]
        breaks = [int(np.sum(o > k)) for k in range(o.max(), o.min() - 1, -1)]
        breaks = [b for b in breaks if 0 < b < len(sv)]
        on32 = [b for b in breaks if b % 32 == 0]
        print(f"POLY {name} {rows}x{cols} rank={len(sv)} top={sv[0]:.3f} octaves(high..low)={' '.join(f'{k}:{c}' for k, c in counts.items())}"
              f" fullest_over_emptiest={max(occupied) / min(occupied):.1f} breaks={breaks} on_multiple_of_32={on32}")
        if rows == cols:
            lam = np.sort(np.abs(np.linalg.eigvals(A)))[::-1]
            lam = lam[lam > 0]
            n = min(len(lam), len(sv))
            newton, hodge = np.cumsum(np.log2(lam[:n])), np.cumsum(np.log2(sv[:n]))
            gap = hodge - newton
            touches = [i + 1 for i in range(n - 1) if gap[i] < 0.05]
            lo = np.floor(np.log2(lam)).astype(int)
            lcounts = {k: int(np.sum(lo == k)) for k in range(lo.max(), lo.min() - 1, -1)}
            print(f"POLY {name} rates(high..low)={' '.join(f'{k}:{c}' for k, c in lcounts.items())} hodge_minus_newton_at(32,64,96,128,160,192)="
                  f"{' '.join(f'{gap[i - 1]:.2f}' for i in (32, 64, 96, 128, 160, 192) if i <= n)} ends={hodge[-1]:.2f},{newton[-1]:.2f} touches_within_0.05={touches[:20]}")


if __name__ == '__main__' and '--polygons' in sys.argv:
    polygons(sys.argv[1])
    sys.exit(0)
