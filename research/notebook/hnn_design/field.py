# Exact reference of the revised step-4 tick (THE_REBUILD, Step 4 design).
#   junction : parallel adaptor (point Swing about the participation anchor), weights Y_r (own
#              storage port) and G_a = kappa_a * Y_a (one exponent per CONTACT, both ends).
#   element  : (I - K/2) s' = (I + K/2) b + W_c c,  b = 2v - s (the Swing's reflected storage wave),
#              c = v - s (the junction contrast),  K_r = W_s + sum sigma A_rho  (W_s passive, A_rho skew).
#              The contrast port W_c drives inside the midpoint (Holon/Cayley.drive_balance):
#                1/2|s'|^2 - 1/2|b|^2 = <xbar, W_s xbar> + <xbar, W_c c>,  xbar = (b + s')/2.
#   transit  : contact a = (g -> h) with channel C^k, partial matchings iota_g, iota_h (0/1),
#              U_a = iota_h iota_g^T a partial isometry, U_a^T its reverse; the untransmitted
#              part of each outgoing wave reflects back to its own junction.  On the channel the
#              contact is a series two-port with state z = (u displacement, w slip rate),
#              energy E = 1/2 w'Cw + 1/2 u'Ku, dissipation D, midpoint step of length h:
#                M w_mid = 2Cw + h(alpha_g - alpha_h) - hKu,  M = 2C + (2h/G)I + hD + (h^2/2)K
#                w' = 2 w_mid - w,  u' = u + h w_mid
#                alpha_g_out = alpha_g - (2/G) w_mid,  alpha_h_out = alpha_h + (2/G) w_mid
#   power    : P = (h/4)[sum_r Y_r|s_r|^2 + sum_(r,a) G_a|a_ra|^2] + sum_a E_a
#              P(t+1) = P(t) - h sum_a w_mid' D_a w_mid + (h/2) sum_r Y_r <xbar_r, W_s,r xbar_r>
#                            + (h/2) sum_r Y_r <xbar_r, W_c,r c_r>          (exact)
#              the last term is the contrast ports' power Pi_c, which has no sign.
#   Defaults (resist=False, contrast=False) draw exactly what the earlier scripts drew: W_s = W_c = 0.
from fractions import Fraction as F
import random

def bits(x):
    x = F(x)
    return x.numerator.bit_length() + x.denominator.bit_length()

def vbits(v):
    return max((bits(x) for x in v), default=0)

# The print: every reading exact, never a decimal (a decimal is a collapse).  A short ratio prints
# whole with its integer quotient and remainder; a longer one prints as its integer quotient q plus
# its remainder's exact enclosure between the last continued-fraction convergent with denominator
# at most 2^12 and the nearest semiconvergent on its other side within the same bound, with the
# exact ratio's size in bits.
# [agent-inferred] SHORT_BITS and CONVERGENT_DENOMINATOR are presentation bounds, never a law.
SHORT_BITS = 64
CONVERGENT_DENOMINATOR = 1 << 12

def enclose(x):
    """The exact enclosure (lo, hi) of x by its convergent and semiconvergent within the bound."""
    x = F(x)
    (p0, q0), (p1, q1) = (0, 1), (1, 0)
    rest = x
    while True:
        a = rest.numerator // rest.denominator
        p2, q2 = a * p1 + p0, a * q1 + q0
        if q2 > CONVERGENT_DENOMINATOR:
            break
        (p0, q0), (p1, q1) = (p1, q1), (p2, q2)
        if rest == a:
            return F(p1, q1), F(p1, q1)
        rest = 1 / (rest - a)
    t = (CONVERGENT_DENOMINATOR - q0) // q1
    near, other = F(p1, q1), F(p0 + t * p1, q0 + t * q1)
    return min(near, other), max(near, other)

def exact(x):
    """n; n/d (q rem r over d); or, past SHORT_BITS, 'q + e, e in [lo, hi]' with the ratio's bits."""
    x = F(x)
    q, r = divmod(x.numerator, x.denominator)
    if bits(x) > SHORT_BITS:
        lo, hi = enclose(F(r, x.denominator))
        return f"{q} + e, e in [{lo}, {hi}] (an exact ratio of {bits(x)} bits)"
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x} ({q} rem {r} over {x.denominator})"

def solve(A, b):
    n = len(A)
    M = [list(map(F, row)) + [F(b[i])] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]

def matvec(A, x):
    return [sum(a * b for a, b in zip(row, x)) for row in A]

def eye(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]

def rr(rng, lo=-3, hi=3, dmax=3):
    return F(rng.randint(lo, hi), rng.randint(1, dmax))

def gram(rng, k, scale=1):
    c = [[rr(rng) for _ in range(k)] for _ in range(k)]
    return [[scale * sum(c[i][l] * c[j][l] for l in range(k)) for j in range(k)] for i in range(k)]

def skew(rng, n):
    K = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            v = rr(rng)
            K[i][j] = v
            K[j][i] = -v
    return K

class Field:
    """rings: list of realified widths n_r; contacts: list of (g, h, k, sel_g, sel_h)."""

    def __init__(self, widths, edges, seed=1, h=F(1), dissipative=False, per_ring_beta=False,
                 stiff=True, store=True, resist=False, contrast=False):
        rng = random.Random(seed)
        self.n = widths
        self.h = h
        self.Yr = [F(rng.randint(1, 5), rng.randint(1, 5)) for _ in widths]
        self.cay = []
        skews = []
        for n in widths:
            K = skew(rng, n)
            skews.append(K)
            self.cay.append(self._cayley(K, n))
        self.contacts = []
        for (g, hh, k) in edges:
            sel_g = sorted(rng.sample(range(widths[g]), k))
            sel_h = sorted(rng.sample(range(widths[hh]), k))
            beta_Q = 2 * rng.randint(0, 2)                   # beta_a * Q_a on the lattice, L = 1
            kappa = F(2) ** (-(beta_Q // 2))                 # one exponent per contact
            Ya = F(rng.randint(1, 5), rng.randint(1, 5))
            C = gram(rng, k) if store else [[F(0)] * k for _ in range(k)]
            Kc = gram(rng, k) if stiff else [[F(0)] * k for _ in range(k)]
            D = gram(rng, k, F(1, 4)) if dissipative else [[F(0)] * k for _ in range(k)]
            self.contacts.append(dict(g=g, h=hh, k=k, sg=sel_g, sh=sel_h, G=kappa * Ya,
                                      C=C, K=Kc, D=D))
        self.inc = {r: [ai for ai, c in enumerate(self.contacts) if r in (c['g'], c['h'])]
                    for r in range(len(widths))}
        # the ring element's passive part W_s = -f f* and its contrast port W_c, drawn from their
        # own generator so that the defaults above are unchanged
        rng2 = random.Random(7919 * seed + 1)
        zero = lambda n: [[F(0)] * n for _ in range(n)]
        self.Ws = [gram(rng2, n, F(-1, 4)) if resist else zero(n) for n in widths]
        cs = F(contrast) if contrast else F(0)          # contrast: False, or the entries' scale
        self.Wc = [[[cs * rr(rng2) for _ in range(n)] for _ in range(n)] if contrast else zero(n)
                   for n in widths]
        self.Lc = []                        # (I - K/2)^-1 W_c, so that s' = Cay b + Lc c
        for r, n in enumerate(widths):
            K = [[skews[r][i][j] + self.Ws[r][i][j] for j in range(n)] for i in range(n)]
            if resist:
                self.cay[r] = self._cayley(K, n)
            L = [[(1 if i == j else 0) - K[i][j] / 2 for j in range(n)] for i in range(n)]
            cols = [solve(L, [self.Wc[r][i][j] for i in range(n)]) for j in range(n)]
            self.Lc.append([[cols[j][i] for j in range(n)] for i in range(n)])
        self.active = bool(resist or contrast)
        self.last = dict(diss=F(0), resist=F(0), contrast=F(0))

    @staticmethod
    def _cayley(K, n):
        L = [[(1 if i == j else 0) - K[i][j] / 2 for j in range(n)] for i in range(n)]
        R = [[(1 if i == j else 0) + K[i][j] / 2 for j in range(n)] for i in range(n)]
        # Cay = L^-1 R, built column by column (exact)
        cols = [solve(L, [R[i][j] for i in range(n)]) for j in range(n)]
        return [[cols[j][i] for j in range(n)] for i in range(n)]

    def zero(self):
        s = [[F(0)] * n for n in self.n]
        a = {}
        for ai, c in enumerate(self.contacts):
            a[(c['g'], ai)] = [F(0)] * self.n[c['g']]
            a[(c['h'], ai)] = [F(0)] * self.n[c['h']]
        z = [([F(0)] * c['k'], [F(0)] * c['k']) for c in self.contacts]
        return s, a, z

    def energy(self, c, z):
        u, w = z
        return (sum(w[i] * c['C'][i][j] * w[j] for i in range(c['k']) for j in range(c['k'])) / 2
                + sum(u[i] * c['K'][i][j] * u[j] for i in range(c['k']) for j in range(c['k'])) / 2)

    def power(self, state):
        s, a, z = state
        P = sum(self.Yr[r] * sum(x * x for x in s[r]) for r in range(len(self.n)))
        P += sum(self.contacts[ai]['G'] * sum(x * x for x in a[(r, ai)]) for (r, ai) in a)
        P = self.h / 4 * P
        return P + sum(self.energy(c, z[ai]) for ai, c in enumerate(self.contacts))

    def tick(self, state):
        s, a, z = state
        h = self.h
        out = {}
        s2 = []
        resist = F(0)
        contrast = F(0)
        for r, n in enumerate(self.n):
            tot = self.Yr[r] + sum(self.contacts[ai]['G'] for ai in self.inc[r])
            v = [(self.Yr[r] * s[r][i] + sum(self.contacts[ai]['G'] * a[(r, ai)][i]
                                             for ai in self.inc[r])) / tot for i in range(n)]
            for ai in self.inc[r]:
                out[(r, ai)] = [2 * v[i] - a[(r, ai)][i] for i in range(n)]
            b = [2 * v[i] - s[r][i] for i in range(n)]
            sn = matvec(self.cay[r], b)
            if self.active:
                c = [v[i] - s[r][i] for i in range(n)]
                sn = [x + y for x, y in zip(sn, matvec(self.Lc[r], c))]
                xb = [(x + y) / 2 for x, y in zip(b, sn)]
                resist += self.h / 2 * self.Yr[r] * sum(x * y for x, y in zip(xb, matvec(self.Ws[r], xb)))
                contrast += self.h / 2 * self.Yr[r] * sum(x * y for x, y in zip(xb, matvec(self.Wc[r], c)))
            s2.append(sn)
        a2 = {}
        z2 = []
        diss = F(0)
        for ai, c in enumerate(self.contacts):
            g, hh, k, G = c['g'], c['h'], c['k'], c['G']
            bg, bh = out[(g, ai)], out[(hh, ai)]
            ag = [bg[i] for i in c['sg']]
            ah = [bh[i] for i in c['sh']]
            u, w = z[ai]
            M = [[2 * c['C'][i][j] + (2 * h / G if i == j else 0) + h * c['D'][i][j]
                  + h * h / 2 * c['K'][i][j] for j in range(k)] for i in range(k)]
            rhs = [2 * sum(c['C'][i][j] * w[j] for j in range(k)) + h * (ag[i] - ah[i])
                   - h * sum(c['K'][i][j] * u[j] for j in range(k)) for i in range(k)]
            wm = solve(M, rhs)
            z2.append(([u[i] + h * wm[i] for i in range(k)], [2 * wm[i] - w[i] for i in range(k)]))
            diss += h * sum(wm[i] * c['D'][i][j] * wm[j] for i in range(k) for j in range(k))
            ng = list(bg)                       # untransmitted part reflects straight back
            nh = list(bh)
            for idx, i in enumerate(c['sg']):
                ng[i] = ag[idx] - 2 / G * wm[idx]
            for idx, i in enumerate(c['sh']):
                nh[i] = ah[idx] + 2 / G * wm[idx]
            a2[(g, ai)] = ng
            a2[(hh, ai)] = nh
        self.last = dict(diss=diss, resist=resist, contrast=contrast)
        return (s2, a2, z2), diss

    def state_bits(self, state):
        s, a, z = state
        return max([vbits(x) for x in s] + [vbits(x) for x in a.values()]
                   + [max(vbits(u), vbits(w)) for u, w in z])
