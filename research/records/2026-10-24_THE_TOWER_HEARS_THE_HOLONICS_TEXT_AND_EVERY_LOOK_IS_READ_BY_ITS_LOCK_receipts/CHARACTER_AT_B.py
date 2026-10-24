"""Does the state a sum's second operand meets at B (level 0's modes before it arrives) carry the
first operand's units as a phase, in a straight-line read? An exterior reading of the tower hcont2
(pass 7 of the mixed pair tower): the true sums' B cells of the training equation block (eight
parts, each read from rest) and of the held-out equations. Each coordinate is released to 2^-10 of
the state's unit and the fits carry one unit of ridge, as the probe's do.

Read: (1) the operand a0 by the argmax of ten indicator fits; (2) the characters
z_k = exp(2 pi i k a0 / 10), k = 1, 3, by complex least squares (with and without a constant): the
held-out share of the character's variance the read carries, and a0 decoded as the nearest root;
(3) the one complex form this suggests, c = z_1^ * chi_1(b0) (the read times the arriving digit's
character), its units decoded by angle and by the probe's own indicator fit from (Re c, Im c);
(4) two such forms, k = 1 and 3."""
import sys, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)

def load(text_path, modes_path):
    text = open(text_path, "rb").read()
    role, info = tm.probe_roles(text)
    X, F = [], []
    for i, _, _, levels in tm.parse(modes_path, True):
        f = info[i + 1]
        assert f[0] == "+" and "B" in role[i + 1] and text[i] - 48 == f[2]
        X.append([v for m in levels[0] for v in m[:2]]); F.append(f[1:])
    return np.array(X, dtype=float) / 2**14, np.array(F)

parts = [load(f"modes/block{c}.txt", f"char/block{c}_full.txt") for c in range(8)]
Xt = np.vstack([p[0] for p in parts]); Ft = np.vstack([p[1] for p in parts])
Xd, Fd = load("htext2/dev_arithmetic.txt", "char/dev_full.txt")
print(f"train B cells {len(Xt)}, held out {len(Xd)}, coordinates {Xt.shape[1]}")

def ridge(X, Y, const=True):
    A = np.hstack([X, np.ones((len(X), 1))]) if const else X
    W = np.linalg.solve(A.T @ A + np.eye(A.shape[1]), A.T @ Y)
    return lambda Z: (np.hstack([Z, np.ones((len(Z), 1))]) if const else Z) @ W

def indicators(Xtr, labels_tr, Xte, labels_te):
    pred = ridge(Xtr, np.eye(10)[labels_tr])(Xte).argmax(1)
    return int((pred == labels_te).sum())

def nearest(z, k):
    # the root e^(2 pi i k d / 10) nearest z, as d
    d = np.arange(10)
    roots = np.exp(2j * np.pi * k * d / 10)
    return np.abs(z[:, None] - roots[None, :]).argmin(1)

print(f"a0 by indicators from the state before b0 arrives: {indicators(Xt, Ft[:,0], Xd, Fd[:,0])} of {len(Xd)}")
reads = {}
for k in (1, 3):
    for const in (True, False):
        zt, zd = np.exp(2j*np.pi*k*Ft[:,0]/10), np.exp(2j*np.pi*k*Fd[:,0]/10)
        f = ridge(Xt, np.stack([zt.real, zt.imag], 1), const)
        pt, pd = f(Xt), f(Xd)
        zhat_t, zhat_d = pt[:,0] + 1j*pt[:,1], pd[:,0] + 1j*pd[:,1]
        share = 1 - np.sum(np.abs(zd - zhat_d)**2) / np.sum(np.abs(zd - zd.mean())**2)
        share_t = 1 - np.sum(np.abs(zt - zhat_t)**2) / np.sum(np.abs(zt - zt.mean())**2)
        ok = int((nearest(zhat_d, k) == Fd[:,0]).sum())
        mag = np.abs(zhat_d)
        print(f"k={k} constant={const}: character share train {1000*share_t:.0f} held out {1000*share:.0f} per mille; a0 as the nearest root {ok} of {len(Xd)}; |z^| quartiles {np.percentile(mag,25):.2f} {np.median(mag):.2f} {np.percentile(mag,75):.2f}")
        reads[(k, const)] = (zhat_t, zhat_d)

def form_units(ks, const):
    ct, cd = [], []
    for k in ks:
        zt, zd = reads[(k, const)]
        ct.append(zt * np.exp(2j*np.pi*k*Ft[:,1]/10)); cd.append(zd * np.exp(2j*np.pi*k*Fd[:,1]/10))
    angle = int((nearest(cd[0], ks[0]) == Fd[:,2]).sum())
    Ct = np.stack([v for c in ct for v in (c.real, c.imag)], 1); Cd = np.stack([v for c in cd for v in (c.real, c.imag)], 1)
    probe = indicators(Ct, Ft[:,2], Cd, Fd[:,2])
    return angle, probe

for ks in ((1,), (3,), (1, 3)):
    for const in (False, True):
        angle, probe = form_units(ks, const)
        print(f"forms k={ks} constant={const}: c0 at B by the first form's angle {angle}, by the probe's indicator fit {probe} of {len(Xd)}")
# the exact characters, for the scale of what an exact read gives (the sum's units are their product)
print(f"c0 from the exact a0 character times b0's: {int((nearest(np.exp(2j*np.pi*(Fd[:,0]+Fd[:,1])/10),1)==Fd[:,2]).sum())} of {len(Xd)}")
