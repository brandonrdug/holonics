"""Alignment (A) over many settings: the face's top against the executed growth's top, and pairwise
order agreement, across E scales (perturbative to past the recorded regime), modes and terrains.
Also what the executed member growth reads: rank agreement of ln rho_m with p|W_m| (first power,
the averaged pump) and with p^2(|W+|^2+|W-|^2) (the face's member term)."""
from common import *
import bankprobe

t0 = time.time()
E0c, _ = bankprobe.E0()
rng = np.random.default_rng(424242)


def pair_agree(x, y):
    """fraction of candidate pairs (within a decision) ordered alike by x and y"""
    agree = tot = 0
    for i in range(CLASSES):
        for j in range(i + 1, CLASSES):
            sx = np.sign(x[:, i] - x[:, j])
            sy = np.sign(y[:, i] - y[:, j])
            agree += int((sx == sy).sum())
            tot += len(sx)
    return agree, tot


def spearman(x, y):
    rx = np.argsort(np.argsort(x))
    ry = np.argsort(np.argsort(y))
    return np.corrcoef(rx, ry)[0, 1]


terrains = {'order2': order2, 'alternation': alternation, 'line': spectral_line}
print('setting | decisions | face top = executed top | pairs ordered alike | executed top = target | face top = target | largest growth')
for tname, terr in terrains.items():
    pairs = terr(rng, 32)
    for mode in ('open', 'causal'):
        decs = decisions(pairs, mode)
        Cs, tg = counts_of(decs)
        for label, E in [('E_0 (declared, entries 1/2)', E0c)] + [
                (f'Gaussian E, entry scale 2^{k}', 2.0 ** k * (rng.standard_normal(E0c.shape) + 1j * rng.standard_normal(E0c.shape)) / np.sqrt(2))
                for k in (-6, -4, -2, -1, 0)]:
            r = read(Cs, E, want_face=True)
            a, A = r['a'], r['A']
            ag, tot = pair_agree(A, a)
            ok = r['cert'].all()
            print(f'{tname}/{mode}/{label} | {len(decs)} | {int((A.argmax(1) == a.argmax(1)).sum())} | {ag} of {tot} | '
                  f'{int((a.argmax(1) == tg).sum())} | {int((A.argmax(1) == tg).sum())} | {dy(a.max(), 2)}{"" if ok else " (some tick uncertified)"}')

# what a member's executed growth reads, on the declared E_0 order-2 open candidates
pairs = order2(rng, 32)
decs = decisions(pairs, 'open')
Cs, tg = counts_of(decs)
for label, E in [('E_0', E0c), ('E_0/8', E0c / 8), ('E_0/32', E0c / 32)]:
    z = to_turn(storage_nodes(Cs, E))
    W = z @ FW.T
    print(f'\n[{label}] member log-growth against the resonance amplitudes (Spearman rank correlation over {len(z)} candidates):')
    for m in range(4):
        rho, _, _ = member_growth(z, m, P)
        Wp, Wm = np.abs(W[:, 2 * m]), np.abs(W[:, 2 * m + 1])
        s1 = spearman(np.log(rho), np.maximum(Wp, Wm))
        s2 = spearman(np.log(rho), Wp ** 2 + Wm ** 2)
        s3 = spearman(np.log(rho), np.abs(z.sum(1)))
        print(f'  member {m}: with max(|W+|,|W-|) {dy(s1, 8)}; with |W+|^2+|W-|^2 {dy(s2, 8)}; with the standing sum |sum_t z_t| {dy(s3, 8)}; ln rho range [{dy(np.log(rho).min(), 4)}, {dy(np.log(rho).max(), 4)}]')
print(f'\neA1: {time.time() - t0:.0f} s, peak {peak_bytes()} bytes')
