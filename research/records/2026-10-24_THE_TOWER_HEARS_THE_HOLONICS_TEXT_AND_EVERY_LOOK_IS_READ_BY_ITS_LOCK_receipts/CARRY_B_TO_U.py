"""Which of level 0's modes carry a value placed at B to U the same way, whatever the result's length?

Between the second operand's units arriving (cell pb) and the cell that codes the result's units
(U, cell pu - 1), each mode moves at every cell by its own move and pump, h -> lambda h + beta conj(h)
(the real 2x2 [[Re l + Re b, Im b - Im l], [Im l + Im b, Re l - Re b]]), read at cells pb+1 .. pu-1
(char/block{c}_bufull.txt, on 2^-30). The cells are the '=' and the result's digits before its units,
so a two-digit result gives two moves and a three-digit result three. A value placed in a mode at B
reaches U as the product of those moves.

Here the value placed at B is the exact crossing chi_1(c0) (a label: the ceiling of any form at B).
For each mode it is carried to U through that sum's own moves, and read there:
- how much of chi_1(c0) the carried value holds, pooled over the lengths and within each (a
  straight-line fit of its two channels, fitted on even lines, read on odd);
- its share of U's own tension (U's input covectors, as U_FORMS.py);
- its gain (rms modulus after the carry);
- how far the mean carries of the two lengths differ, relative to their size.
Beside each: how much of chi_1(b0) and chi_1(a0) the mode itself holds at U (its state before the
arrival at U, as U_FORMS.py), to see whether the strands ride the modes that carry the same way.
Also a check that the moves read are the moves applied: carried = M before at every cell read.
Uses U_FORMS.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("# references")])

# the sums in U_FORMS's order, with their cells pb and pu
order = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    info, start = {}, 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, cc_ = m_.groups()
            pu = start + len(line) - 1
            info[pu - 1] = (start + len(a_) + len(b_), pu)
        start += len(line) + 1
    for line in open(f"char/block{c}_ucov.txt"):
        if line.startswith("FORMS "):
            order.append((c,) + info[int(line.split()[1])])
assert len(order) == len(S_)

moves, worst = {}, 0.0
for c in range(8):
    for i, _, _, lev in tm.parse(f"char/block{c}_bufull.txt", True):
        md = np.array(lev[0], dtype=float)                        # 64 x 10
        lam = (md[:, 6] + 1j * md[:, 7]) / 2**30
        bet = (md[:, 8] + 1j * md[:, 9]) / 2**30
        before = (md[:, 0] + 1j * md[:, 1]) / 2**24
        carried = (md[:, 2] + 1j * md[:, 3]) / 2**24
        r = np.abs(carried - (lam * before + bet * before.conj())).max() / (np.abs(carried).max() + 1e-30)
        worst = max(worst, r)
        moves[(c, i)] = (lam, bet)
print(f"moves read at {len(moves)} cells; the largest departure of carried from the move applied to before, relative: {worst:.2e}", flush=True)

n, NM = len(order), 64
LEN = np.array([pu - pb - 1 for _, pb, pu in order])
v0 = chi(1, C0)
W = np.zeros((n, NM), dtype=complex)
for s, (c, pb, pu) in enumerate(order):
    h = np.full(NM, v0[s])
    for i in range(pb + 1, pu):
        lam, bet = moves[(c, i)]
        h = lam * h + bet * h.conj()
    W[s] = h

def held_in(x, t, m):
    tr, te = m & (LN % 2 == 0), m & (LN % 2 == 1)
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    Wt = np.linalg.lstsq(A[tr], t[tr], rcond=None)[0]
    r = t[te] - A[te] @ Wt
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()

def mean_carry(m, k, L):
    """the mean real 2x2 carry of mode k over the sums of length L (from the carries of 1 and i)"""
    sel = np.flatnonzero(LEN == L)
    P = np.zeros((2, 2))
    for col, u in enumerate((1.0, 1j)):
        acc = 0j
        for s in sel:
            c, pb, pu = order[s]
            h = u
            for i in range(pb + 1, pu):
                lam, bet = moves[(c, i)]
                h = lam[k] * h + bet[k] * np.conj(h)
            acc += h
        acc /= len(sel)
        P[:, col] = [acc.real, acc.imag]
    return P

allm = np.ones(n, bool)
print(f"sums {n}: result of one digit {int((LEN == 1).sum())}, two {int((LEN == 2).sum())}, three {int((LEN == 3).sum())}", flush=True)
rows = []
for k in range(NM):
    w = W[:, k]
    hk = S_[:, 2 * k] + 1j * S_[:, 2 * k + 1]
    rows.append((held_in(w, v0, allm), k, held_in(w, v0, LEN == 2), held_in(w, v0, LEN == 3), share(w), math.sqrt((np.abs(w)**2).mean()),
                 held_frac(hk, chi(1, B0)), held_frac(hk, chi(1, A0))))
rows.sort(key=lambda r: -r[0])
print("mode: the carried crossing holds chi_1(c0) pooled / two digits / three digits; its share of U's tension; gain; "
      "the two lengths' mean carries differ by; the mode at U holds chi_1(b0), chi_1(a0)", flush=True)
for r in rows[:12] + rows[-4:]:
    hp, k, h2, h3, sh, g, hb, ha = r
    P2, P3 = mean_carry(allm, k, 2), mean_carry(allm, k, 3)
    d = np.linalg.norm(P2 - P3) / math.sqrt((np.linalg.norm(P2)**2 + np.linalg.norm(P3)**2) / 2 + 1e-30)
    print(f"   mode {k}: {hp:.3f} / {h2:.3f} / {h3:.3f}; share {sh:.4f}; gain {g:.3f}; differ by {d:.3f}; at U holds b0 {hb:.3f}, a0 {ha:.3f}", flush=True)
hp = np.array([r[0] for r in rows])
print(f"modes whose carried crossing holds at least 0.9 pooled: {int((hp >= 0.9).sum())}; at least 0.5: {int((hp >= 0.5).sum())}; median {np.median(hp):.3f}", flush=True)
hb = {r[1]: r[6] for r in rows}
top_b = sorted(hb, key=lambda k: -hb[k])[:8]
print("the modes holding most of chi_1(b0) at U: " + ", ".join(f"{k} (b0 {hb[k]:.3f}, carried crossing pooled {dict((r[1], r[0]) for r in rows)[k]:.3f})" for k in top_b), flush=True)
print(f"done in {time.time() - t0:.1f} s")
