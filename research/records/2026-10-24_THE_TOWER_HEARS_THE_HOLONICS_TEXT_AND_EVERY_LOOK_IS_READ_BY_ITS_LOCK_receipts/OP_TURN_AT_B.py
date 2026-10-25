"""Does the operator turn the first operand's strand at B?

RING_AFTER_RELATION.py: read after `=` on the sums' lines, the ring form founded at B holds 0.748 of
chi_1(c0); after `=` on every line, 0.029. A difference's units turn the other way,
chi_1(a0 - b0) = chi_1(a0) conj(chi_1(b0)), so one crossing reads a sum's units and a difference's
wrong ones. Here the outside form's state read at B (char/ideal_quiet.txt, fitted on the sums'
first operand) is read on each operation's B cells against chi_1(a0) and against its conjugate
(|corr|^2 of a straight-line fit, the state read uncentred): whether the operator's arrival has
already reflected the strand, so the same form would cross a difference correctly. Uses
REGION_SHARE.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("def geneig_top")])
r = F @ a_ideal
for op in "+-*":
    q = ROLE & (OP == op)
    x, t = r[q], chi(1, A0[q])
    def held(target):
        A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
        W = np.linalg.lstsq(A, np.stack([target.real, target.imag], 1), rcond=None)[0]
        res = np.stack([target.real, target.imag], 1) - A @ W
        return 1 - (res**2).sum() / ((np.stack([target.real, target.imag], 1) - np.stack([target.real, target.imag], 1).mean(0))**2).sum()
    zz = np.vdot(t, x) / len(x)
    print(f"{op}: B cells {q.sum()}; the state read holds chi_1(a0) {held(t):.3f}, its conjugate {held(np.conj(t)):.3f}; mean of read times conj chi_1(a0): |{abs(zz):.3f}| at {np.degrees(np.angle(zz)):.0f} degrees")
