"""The receiver's grain from its reading count, and the lattices that follow (record §3).

L_R is the least integer with 2 L_R^2 >= N ln 2, decided at both ends of an enclosure of ln 2.
The enclosure is computed here from ln 2 = sum_(k>=1) 1/(k 2^k): the partial sum S_K is a lower
bound and the tail is below 1/((K+1) 2^K), so ln 2 lies in [S_K, S_K + 1/((K+1) 2^K)]. The lattices follow the code's rules:
L_l = ceil(log2(2 L_R X_l)) (hnn/field.rs lattice_exponent); D_c = ceil(log2(8 L_R X_w w e_max)),
L_c = 2 D_c, L_w = ceil(log2(4 L_R X_w e_max 3)) (hnn/chart.rs WordLattice::by_rule), with
campaign 1's X_w = 22, w = 26, e_max = 4. Exact integers and ratios only.
"""
from fractions import Fraction

K = 60
LO = sum(Fraction(1, k * 2**k) for k in range(1, K + 1))
HI = LO + Fraction(1, (K + 1) * 2**K)


def grain(n):
    g = 1
    while 2 * g * g < n * HI:
        g += 1
    assert 2 * g * g >= n * LO and 2 * (g - 1) ** 2 < n * LO, "the enclosure does not decide"
    return g


def ceil_log2(x):
    return (x - 1).bit_length()


FAN_IN = [("Element/Standing(0)", 10), ("Element/Standing(1)", 14), ("Element/Standing(2), R", 22),
          ("Element/Standing(3)", 26), ("Channel(0), (3)", 10), ("Channel(1)", 14),
          ("Channel(2)", 22), ("SourcePort(0) at population 6,148", 6148)]
for label, n in [("one window, A = 2", 2), ("aeon on prose (proxy)", 1100),
                 ("aeon on uniform bytes", 1190), ("declared population n* = 6,148", 6148),
                 ("whole pinned cut", 171754), ("declared tolerance (for comparison)", None)]:
    g = 16 if n is None else grain(n)
    lattices = ", ".join(f"{k} {ceil_log2(2 * g * x)}" for k, x in FAN_IN)
    d_c = ceil_log2(8 * g * 22 * 26 * 4)
    l_w = ceil_log2(4 * g * 22 * 4 * 3)
    print(f"{label}: N = {n}, L_R = {g}; {lattices}; D_c {d_c}, L_c {2 * d_c}, L_w {l_w}")

# Readings needed for the contacts' largest measured shift 7/2^18 (contact-loop record §11):
# N >= 2 / (ln 2 * delta^2).
delta = Fraction(7, 2**18)
need = 2 / (delta * delta * HI)
print(f"readings to resolve 7/2^18 at one bit: more than {need.numerator // need.denominator} "
      f"(between 2^{(need.numerator // need.denominator).bit_length() - 1} and "
      f"2^{(need.numerator // need.denominator).bit_length()})")
