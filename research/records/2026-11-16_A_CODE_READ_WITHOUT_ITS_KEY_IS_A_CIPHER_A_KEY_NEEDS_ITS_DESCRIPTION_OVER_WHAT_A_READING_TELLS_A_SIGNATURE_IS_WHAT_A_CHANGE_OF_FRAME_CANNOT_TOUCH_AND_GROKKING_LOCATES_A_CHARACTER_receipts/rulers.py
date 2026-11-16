import itertools, math, numpy as np
from math import comb, log2, gcd
# 1. Prime-ring uncertainty (Chebotarev minors, Tao 2005): every square minor of the p-point DFT is nonzero for p prime.
def min_minor(n, kmax):
    W = np.exp(-2j*np.pi*np.outer(range(n), range(n))/n)
    m = 1e9
    for k in range(1, kmax+1):
        for R in itertools.combinations(range(n), k):
            for C in itertools.combinations(range(n), k):
                d = abs(np.linalg.det(W[np.ix_(R, C)]))
                m = min(m, d)
    return m
for p in (5, 7):
    mm = min_minor(p, p)
    assert mm > 1e-6, (p, mm); print(f"Z_{p}: smallest |minor| over every square minor = {mm:.4f} (none vanish)")
mm = min_minor(8, 4); assert mm < 1e-9; print(f"Z_8: some 2x2..4x4 minor vanishes (min {mm:.1e})")
# the comb on a composite ring hides from half the modes
n = 16; f = np.zeros(n); f[0] = 1; f[8] = -1
F = np.fft.fft(f); even = [k for k in range(n) if abs(F[k]) < 1e-12]
assert even == list(range(0, n, 2)); print("Z_16: delta_0 - delta_8 vanishes at every even mode:", even == list(range(0,16,2)))
# support sums: prime p => |supp f| + |supp fhat| >= p+1 ; comb on n=12 gives 4+3
n = 12; f = np.array([1.0 if i % 3 == 0 else 0 for i in range(n)]); F = np.fft.fft(f)
s1, s2 = int((abs(f) > 1e-12).sum()), int((abs(F) > 1e-9).sum()); assert (s1, s2) == (4, 3); print("Z_12 comb: supports", s1, s2, "sum", s1+s2, "< 13")
# every nonzero mode of Z_p is a faithful character; on Z_n only modes coprime to n are
p = 97; assert all(len({(k*a) % p for a in range(p)}) == p for k in range(1, p))
n = 96; faithful = sum(1 for k in range(1, n) if len({(k*a) % n for a in range(n)}) == n); assert faithful == 32
print(f"Z_97: all 96 nonzero modes faithful; Z_96: only {faithful} of 95 (phi(96)=32)")
# 2. Dyadic source: Huffman output bits are fair given every prefix (Cooper-Fickes Thm 3.3)
code = {'a': '0', 'b': '10', 'c': '110', 'd': '111'}; prob = {'a': .5, 'b': .25, 'c': .125, 'd': .125}
from collections import defaultdict
L = 6; P = defaultdict(float)
for seq in itertools.product('abcd', repeat=L):
    s = ''.join(code[x] for x in seq); w = math.prod(prob[x] for x in seq)
    for j in range(L):  # first L bits are always defined (each symbol >= 1 bit)
        P[(s[:j], s[j])] += w
for j in range(L):
    for pre in {k[0] for k in P if len(k[0]) == j}:
        a, b = P[(pre, '0')], P[(pre, '1')]
        assert abs(a - b) < 1e-12, (pre, a, b)
print("dyadic Huffman: every output bit fair given its prefix (first 6 bits, all prefixes)")
q = {'a': .4, 'b': .3, 'c': .2, 'd': .1}; P1 = sum(q[x] for x in 'bcd'); print(f"non-dyadic (.4,.3,.2,.1) same code: first bit P(1) = {P1:.2f}")
# 3. Frames: frame potential = tr S^2; Schur-Horn: squared norms majorized by the spectrum of S
rng = np.random.default_rng(1)
for _ in range(200):
    k, N = 4, 9; Fm = rng.normal(size=(k, N)) + 1j*rng.normal(size=(k, N))
    S = Fm @ Fm.conj().T; G = Fm.conj().T @ Fm
    assert abs(np.sum(abs(G)**2) - np.trace(S @ S).real) < 1e-8
    lam = np.sort(np.linalg.eigvalsh(S))[::-1]; r = np.sort(np.sum(abs(Fm)**2, 0))[::-1]
    lam_p = np.concatenate([lam, np.zeros(N-k)])
    assert abs(r.sum() - lam.sum()) < 1e-8 and all(np.cumsum(r)[l] <= np.cumsum(lam_p)[l] + 1e-9 for l in range(N))
print("frames: FP = tr S^2 and norms majorized by the spectrum, 200 random 4x9 frames")
# tight frame minimizes FP at fixed total power: FP >= (sum r)^2 / k
# 4. Barrington: a commutator of two 5-cycles is a 5-cycle (AND by words); abelian words cannot
def comp(p, q): return tuple(p[q[i]] for i in range(5))  # p after q
def inv(p): r = [0]*5; [r.__setitem__(p[i], i) for i in range(5)]; return tuple(r)
def cyc(c):
    p = list(range(5))
    for i in range(len(c)): p[c[i]] = c[(i+1) % len(c)]
    return tuple(p)
a, b = cyc([0,1,2,3,4]), cyc([0,2,4,3,1]); c = comp(comp(a, b), comp(inv(a), inv(b)))
def order(p):
    e = tuple(range(5)); q = p; k = 1
    while q != e: q = comp(p, q); k += 1
    return k
assert order(c) == 5; print("S5: [a,b] of two 5-cycles is a 5-cycle; identity whenever either is the identity")
# 5. Unicity (Shannon): Enigma key ~ rotor order x start x ring x plugboard
plug = math.factorial(26)//(math.factorial(6)*math.factorial(10)*2**10)
HK = log2(60) + log2(26**3) + log2(26**2) + log2(plug); D = log2(26) - 1.5
print(f"Enigma key {HK:.1f} bits; redundancy {D:.2f} bits/letter; unicity ~ {HK/D:.0f} letters; plugboard {plug}")
# 6. Sparse key's description: log2 C(n,k) vs k log2(n/k)
for n_, k_ in ((1024, 10), (4096, 32)):
    print(f"n={n_} k={k_}: log2 C(n,k) = {log2(comb(n_,k_)):.1f} bits; k log2(n/k) = {k_*log2(n_/k_):.1f}")
print("ban = log2 10 =", round(log2(10), 3), "bits; deciban =", round(log2(10)/10, 3))
# 7. Participation: modes (tr S)^2 / tr S^2 never exceed places (sum r)^2 / sum r^2 (Schur-convexity of the square under majorization)
for _ in range(200):
    k, N = 4, 12; Fm = rng.normal(size=(k, N)) + 1j*rng.normal(size=(k, N)); Fm[:, :6] *= rng.uniform(.1, 3, size=6)
    S = Fm @ Fm.conj().T; r = np.sum(abs(Fm)**2, 0)
    Nm = np.trace(S).real**2 / np.trace(S @ S).real; Np = r.sum()**2 / (r**2).sum()
    assert Nm <= Np + 1e-9 and Nm <= k + 1e-9
v = rng.normal(size=4); par = np.outer(v, rng.uniform(.5, 2, size=12)); S = par @ par.T
assert abs(np.trace(S)**2 / np.trace(S @ S) - 1) < 1e-9
print("participation: modes <= places on 200 frames; parallel places occupy one mode")
# 8. A founding's criterion is a unicity distance: N/2 log2(1/(1-rho)) >= log2|P| + 1/2 log2 N
def unicity_n(rho, P):
    N = 1
    while N / 2 * log2(1 / (1 - rho)) < log2(P) + 0.5 * log2(N): N += 1
    return N
for rho, P in ((1/4, 64), (1/16, 64), (1/64, 4096)):
    print(f"rho={rho:.4f} pool {P}: founds at N = {unicity_n(rho, P)} places")
