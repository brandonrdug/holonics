# C1: the tick's global power balance, exact at every tick.
#   lossless elements and transit           : P is constant;
#   contact dissipation                     : P(t) - P(t+1) equals the dissipation;
#   passive element part W_s and the learned
#   contrast port W_c (R3 C1)               : P(t+1) - P(t) = -dissipation + resist + Pi_c, where
#       resist = (h/2) sum_r Y_r <xbar_r, W_s,r xbar_r> <= 0 and Pi_c = (h/2) sum_r Y_r <xbar_r, W_c,r c_r>,
#       the contrast ports' power, which has no sign.
# Field: six rings of realified widths 4,2,4,6,2,4 (d_g != d_h, so U_a is a proper partial isometry),
# the six-cycle plus the chord 0-3; channel widths below every end's width.
from fractions import Fraction as F
import random
from field import Field, exact

widths = [4, 2, 4, 6, 2, 4]
edges = [(0, 1, 2), (1, 2, 1), (2, 3, 3), (3, 4, 2), (4, 5, 1), (5, 0, 2), (0, 3, 2)]

def run(dissipative, resist=False, contrast=False, ticks=8, seed=11, start=4):
    # contrast: False, or the scale of W_c's entries (rationals up to 3 in size, times the scale)
    f = Field(widths, edges, seed=seed, dissipative=dissipative, resist=resist, contrast=contrast)
    rng = random.Random(start)
    s, a, z = f.zero()
    s = [[F(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(n)] for n in widths]
    for key in a:
        a[key] = [F(rng.randint(-3, 3), rng.randint(1, 3)) for _ in a[key]]
    z = [([F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(c['k'])],
          [F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(c['k'])]) for c in f.contacts]
    state = (s, a, z)
    P = [f.power(state)]
    terms = []
    for _ in range(ticks):
        state, _ = f.tick(state)
        P.append(f.power(state))
        terms.append(dict(f.last))
    return P, terms

P, T = run(False)
print("lossless: P constant exactly:", all(p == P[0] for p in P), " P =", exact(P[0]),
      " (bits of P:", P[0].numerator.bit_length() + P[0].denominator.bit_length(), ")")
P, T = run(True)
print("dissipative: P(t) - P(t+1) == dissipation(t) exactly at every tick:",
      all(P[t] - P[t + 1] == T[t]['diss'] for t in range(len(T))))
print("dissipative: P over ticks:", "; ".join(exact(p) for p in P))

# the contrast port alone (lossless contacts, W_s = 0): the power changes by exactly Pi_c
P, T = run(False, contrast=F(1, 8))
print("contrast port W_c != 0, otherwise lossless: P(t+1) - P(t) == Pi_c(t) exactly at every tick:",
      all(P[t + 1] - P[t] == T[t]['contrast'] for t in range(len(T))))
print("   Pi_c over ticks:", "; ".join(exact(t['contrast']) for t in T))
# every term at once: dissipative contacts, passive W_s, contrast port W_c
P, T = run(True, resist=True, contrast=F(1, 8))
print("dissipation + W_s + W_c: P(t+1) - P(t) == -dissipation + resist + Pi_c exactly at every tick:",
      all(P[t + 1] - P[t] == -T[t]['diss'] + T[t]['resist'] + T[t]['contrast'] for t in range(len(T))))
print("   resist <= 0 at every tick:", all(t['resist'] <= 0 for t in T))
# Pi_c has no sign: over 8 starting states and 8 ticks each
signs = set()
for start in range(8):
    _, T = run(True, resist=True, contrast=F(1, 8), start=start)
    signs |= {(t['contrast'] > 0) - (t['contrast'] < 0) for t in T}
print("   signs of Pi_c seen over 8 starting states x 8 ticks:", sorted(signs))
# a large contrast port makes the word active: the change grows within the word
P, T = run(True, resist=True, contrast=F(1))
print("W_c entries 8x larger: balance exact:",
      all(P[t + 1] - P[t] == -T[t]['diss'] + T[t]['resist'] + T[t]['contrast'] for t in range(len(T))),
      "; P(8)/P(0) =", exact(P[-1] / P[0]))
