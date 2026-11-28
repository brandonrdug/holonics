#!/usr/bin/env -S python3 -I
"""rise_store_ruler.py SAMPLE_ROWS SAMPLE_CODES ROWS OUT [depth:K] J…: a ruler (the lead, November 28; the formal thread's fallback (a) of
01:29 UTC, taken when G-Z66 missed at 03:23 UTC). The rise cut's mean news after a run held as a store on the level's unit-store
addressing, so its capacity is read before the store is built into the engine.

SAMPLE_CODES is a `read-reach … law` output, as `tools/rise_cut_ruler.py` reads it; the cut on ROWS reads its octets alone. For each `J` given:

    key      χ_j(u) = Π_(d=1..|u|) ζ_j(d, u_(|u|−d))     on J circles, ζ_j(d, a) a turn drawn once from the gene (`Units`' form)
    read     r(F, χ) = Re⟨χ, F⟩ / J
    charge   M_k ← M_k + (ν − r(M_k, χ)) / (n̂ + 1) · χ,  C_k ← C_k + χ,  n̂ = r(C_k, χ)⁺   for the runs of k = 1, 2 octets ending
             at a place (k = 1..K with `depth:K`), ν her code at the next place, over the sample in its order (the delta charge cooled by its own count)
    join     ν̂(t) = Σ_k c_k r(M_k, χ_k) / Σ_k c_k,  c_k = r(C_k, χ_k)⁺ (`plain`), or c_k = (r(C_k, χ_k) − b_k)⁺ with b_k = ‖C_k‖ / (J√2),
             the scatter a key no charge met reads (`over`); beside it a tree of residuals: `T_k` charged as `M_k` toward
             `ν − μ − Σ_(i<k) r(T_i, χ_i)` (μ the running mean of her news), read `ν̂ = μ + Σ_k r(T_k, χ_k)` (`tree`); the mean store
             with its rate floored by a leaky count, `1/(min(n̂, τ) + 1)` for τ = 16, 64 (`floor<τ>`, joined as `plain`); and a store whose
             entries are shared at a residue: a run's word on the two largest primes under J, a sum and a count at each residue, read at
             the ring whose count is least (`ring`, joined by that count)

and an end stands after `t` where `ν̂` rises (`rise`) or peaks (`peak`), each to `OUT/J<J>/<join>_<form>/cut.tsv`. Beside it, the store's
read error against the sample's own means over its runs of one and two octets (`rms` and the share of runs read within a tenth of a nat). Outside the machine;
floats at the exterior.
"""
import math
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rise_cut_ruler import codes_of, rows_of  # noqa: E402

NATS = math.log(2) / (1 << 20)
GENE = 0x5EED_0128
FLOORS = (16, 64)


def cut_of(nu):
    n = len(nu)
    rise = [p > 0 and nu[p] is not None and nu[p - 1] is not None and nu[p] > nu[p - 1] for p in range(n)]
    anchors = {'rise': [0], 'peak': [0]}
    for p in range(n - 1):
        if rise[p]:
            anchors['rise'].append(p + 1)
            if not (p + 1 < n and rise[p + 1]):
                anchors['peak'].append(p + 1)
    return anchors


def main():
    sample, sample_codes, rows, out = sys.argv[1:5]
    words = sys.argv[5:]
    depth = next((int(w[6:]) for w in words if w.startswith('depth:')), 2)
    circles = [int(w) for w in words if not w.startswith('depth:')]
    DEPTHS = tuple(range(1, depth + 1))
    st = rows_of(sample)
    sc = codes_of(sample_codes, len(st))
    texts = rows_of(rows)
    meetings = []
    total, count = defaultdict(float), defaultdict(int)
    for r, t in enumerate(st):
        c = sc[r]
        for p in range(len(t) - 1):
            if p + 1 in c:
                nu = c[p + 1] * NATS
                meetings.append((t[max(p - depth + 1, 0):p + 1], nu))
                for k in DEPTHS:
                    if p - k + 1 >= 0:
                        s = t[p - k + 1:p + 1]
                        total[s] += nu
                        count[s] += 1
    print(f"RISE_STORE sample_meetings={len(meetings)} runs={len(count)} by_depth={','.join(str(sum(1 for s in count if len(s) == k)) for k in DEPTHS)}")
    for J in circles:
        rng = np.random.default_rng(GENE)
        phase = rng.random((2, 256, J)) * 2 * math.pi
        if depth > 2:
            phase = np.concatenate([phase, rng.random((depth - 2, 256, J)) * 2 * math.pi])
        zr, zi = np.cos(phase), np.sin(phase)
        M = [[np.zeros(J), np.zeros(J)] for _ in DEPTHS]
        C = [[np.zeros(J), np.zeros(J)] for _ in DEPTHS]
        T = [[np.zeros(J), np.zeros(J)] for _ in DEPTHS]
        F = {tau: [[np.zeros(J), np.zeros(J)] for _ in DEPTHS] for tau in FLOORS}
        primes = [q for q in range(2 * J, 2, -1) if q < J and all(q % d for d in range(2, int(q ** 0.5) + 1))][:2]
        RS = [[np.zeros(q) for q in primes] for _ in DEPTHS]
        RN = [[np.zeros(q) for q in primes] for _ in DEPTHS]

        def word(run, k):
            return sum(run[-d] << (8 * (d - 1)) for d in range(1, k + 1))

        def ring_read(k, w):
            i = min(range(len(primes)), key=lambda i: RN[k][i][w % primes[i]])
            n_ = RN[k][i][w % primes[i]]
            return (RS[k][i][w % primes[i]] / n_ if n_ > 0 else 0.0), n_
        mu, seen = 0.0, 0

        def chis(run):
            out = []
            cr, ci = np.ones(J), np.zeros(J)
            for d in range(1, len(run) + 1):
                a = run[-d]
                cr, ci = cr * zr[d - 1, a] - ci * zi[d - 1, a], cr * zi[d - 1, a] + ci * zr[d - 1, a]
                out.append((cr, ci))
            return out

        def read(F, ch):
            return (np.dot(ch[0], F[0]) + np.dot(ch[1], F[1])) / J

        for run, nu in meetings:
            base = mu
            for k, ch in enumerate(chis(run)):
                n_hat = max(read(C[k], ch), 0.0)
                w = (nu - read(M[k], ch)) / (n_hat + 1.0)
                M[k][0] += w * ch[0]
                M[k][1] += w * ch[1]
                rt = read(T[k], ch)
                w = (nu - base - rt) / (n_hat + 1.0)
                T[k][0] += w * ch[0]
                T[k][1] += w * ch[1]
                base += rt
                for tau, Ft in F.items():
                    w = (nu - read(Ft[k], ch)) / (min(n_hat, tau) + 1.0)
                    Ft[k][0] += w * ch[0]
                    Ft[k][1] += w * ch[1]
                wd = word(run, k + 1)
                for i, q in enumerate(primes):
                    RS[k][i][wd % q] += nu
                    RN[k][i][wd % q] += 1
                C[k][0] += ch[0]
                C[k][1] += ch[1]
            seen += 1
            mu += (nu - mu) / seen
        bg = [math.sqrt(float(np.dot(c[0], c[0]) + np.dot(c[1], c[1]))) / (J * math.sqrt(2)) for c in C]
        err, terr = [], []
        for s, n in count.items():
            if len(s) > 2:
                continue
            ch = chis(s)
            err.append((read(M[len(s) - 1], ch[-1]) - total[s] / n, n))
            terr.append((mu + sum(read(T[k], x) for k, x in enumerate(ch)) - total[s] / n, n))
        ferr = {tau: [] for tau in F}
        rerr = []
        for s_, n in count.items():
            if len(s_) > 2:
                continue
            ch = chis(s_)
            for tau, Ft in F.items():
                ferr[tau].append((read(Ft[len(s_) - 1], ch[-1]) - total[s_] / n, n))
            rerr.append((ring_read(len(s_) - 1, word(s_, len(s_)))[0] - total[s_] / n, n))
        for name, e_ in [('mean', err), ('tree', terr), ('ring', rerr)] + [(f'floor{tau}', e) for tau, e in ferr.items()]:
            rms = math.sqrt(sum(e * e * n for e, n in e_) / sum(n for _, n in e_))
            within = sum(n for e, n in e_ if abs(e) <= 0.1) / sum(n for _, n in e_)
            print(f"RISE_STORE J={J} depth={depth} store={name} background={','.join(f'{b:.1f}' for b in bg)} rms_by_meeting={rms:.4f} "
                  f"within_tenth_by_meeting={within:.3f} runs_within_tenth={sum(1 for e, _ in e_ if abs(e) <= 0.1) / len(e_):.3f}")
        lines = defaultdict(list)
        ends = defaultdict(int)
        for r, t in enumerate(texts):
            n = len(t)
            nus = {'plain': [], 'over': [], 'tree': [], 'ring': [], **{f'floor{tau}': [] for tau in F}}
            for p in range(n):
                ch = chis(t[max(p - depth + 1, 0):p + 1])
                num = defaultdict(float)
                den = defaultdict(float)
                run = t[max(p - depth + 1, 0):p + 1]
                for k, x in enumerate(ch):
                    m, c = read(M[k], x), read(C[k], x)
                    for join, w in (('plain', max(c, 0.0)), ('over', max(c - bg[k], 0.0))):
                        num[join] += w * m
                        den[join] += w
                    for tau, Ft in F.items():
                        num[f'floor{tau}'] += max(c, 0.0) * read(Ft[k], x)
                        den[f'floor{tau}'] += max(c, 0.0)
                    rm, rn = ring_read(k, word(run, k + 1))
                    num['ring'] += rn * rm
                    den['ring'] += rn
                for join in nus:
                    if join == 'tree':
                        continue
                    nus[join].append(num[join] / den[join] if den[join] > 0 else None)
                nus['tree'].append(mu + sum(read(T[k], x) for k, x in enumerate(ch)))
            for join, nu in nus.items():
                for form, a in cut_of(nu).items():
                    ends[(join, form)] += len(a)
                    lines[(join, form)].append(f"{r}\t{n}\t{','.join(map(str, a))}\n")
        places = sum(len(t) for t in texts)
        for (join, form), ls in sorted(lines.items()):
            d = f'{out}/J{J}d{depth}/{join}_{form}'
            os.makedirs(d, exist_ok=True)
            with open(f'{d}/cut.tsv', 'w') as f:
                f.writelines(ls)
            print(f"RISE_STORE J={J} depth={depth} join={join} form={form} places={places} anchors={ends[(join, form)]} "
                  f"places_an_epoch={places / max(ends[(join, form)], 1):.2f}")


if __name__ == '__main__':
    main()
