"""Does the units crossing's demand reach B with a phase that depends on how far U is?

At U the exact crossing chi_1(c0) holds 1.86 of its two channels' 2 at the region's own loudness;
pooled over the sums' B cells it holds 0.39. The covector at B is the downstream error carried back
to B's input. U's error reaches B through the cells between them: the '=' and the result's digits
before its units, so the number of those cells (the result's length) sets how far the demand
travels. If the transport turns it by an amount that depends on that distance, the demand is
coherent within one distance and cancels when distances are pooled.

Here the sums' B cells (8,986) are split by the result's length, a label of the passage read from
the text after B. In each part the exact crossing's share is read in the part's own Y_r, beside a
foil: the same characters permuted among the part's cells (a fixed permutation), which holds what
any two channels of that many cells hold by chance. Also read: the second operand's units character
chi_1(b0), the class arriving at B, as a reference. Uses REGION_SHARE.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

lens = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    pos = {}
    start = 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, c_ = m_.groups()
            pos[start + len(a_) + len(b_)] = len(c_)
        start += len(line) + 1
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            lens.append(pos.get(int(line.split()[1]), -1))
LEN = np.array(lens)

def share_in(m, t):
    y = Yv[m]; Yi = np.linalg.inv(y.T @ y)
    c = t[m] - t[m].mean()
    Cm = np.stack([c.real, c.imag], 1)
    R, G = Cm.T @ y, Cm.T @ Cm
    return np.trace(Yi @ R.T @ np.linalg.pinv(G) @ R)

def foil(m, t):
    idx = np.flatnonzero(m)
    perm = idx[np.argsort((np.arange(len(idx)) * 7919) % len(idx))]
    tf = t.copy(); tf[idx] = t[perm]
    return share_in(m, tf)

x1, xb = chi(1, C0), chi(1, B0)
print(f"the sums' B cells, pooled ({int(SB.sum())}): chi_1(c0) share {share_in(SB, x1):.4f} (foil {foil(SB, x1):.4f}); chi_1(b0) {share_in(SB, xb):.4f}", flush=True)
for L in sorted(set(LEN[SB])):
    m = SB & (LEN == L)
    if m.sum() < 200:
        print(f"   result length {L}: {int(m.sum())} cells, too few for a 64-dimensional tension", flush=True)
        continue
    print(f"   result length {L}: {int(m.sum())} cells; chi_1(c0) share {share_in(m, x1):.4f} (foil {foil(m, x1):.4f}); chi_1(b0) {share_in(m, xb):.4f}", flush=True)
print(f"done in {time.time() - t0:.1f} s")
