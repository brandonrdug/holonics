"""Exact symbolic checks of the motion record's identities.

The record: research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md.
Every check is exact, over symbols or rationals (sympy), and nothing is floated. All but one are
symbolic identities. The exception is the receiver's split of a rate (`receiver_split`, §3.2): it
checks the split, its uniqueness data, the energy law and rechart covariance on 20 seeded rational
cases (`random.seed(7)`, entries `p/q` with `|p| ≤ 9`, `1 ≤ q ≤ 5`), exactly on each case. That
check samples; it is evidence on those cases, not a proof. `Geometry/Motion` proves the split in Lean.
Run: python3 motion_identities.py  (needs sympy). Each line prints the identity's name and True.
"""
import random

import sympy as sp


def check(name, ok):
    print(f"{name}: {bool(ok)}")
    assert ok, name


def quadratic_kinds():
    al, be, ga, q, p = sp.symbols("alpha beta gamma q p", real=True)
    H = (al * p**2 + 2 * be * p * q + ga * q**2) / 2
    X = sp.Matrix([[sp.diff(H, p, q), sp.diff(H, p, p)], [-sp.diff(H, q, q), -sp.diff(H, q, p)]])
    check("3.1 generator [[b, a], [-g, -b]]", X == sp.Matrix([[be, al], [-ga, -be]]))
    check("3.1 X^2 = -(det X) I", sp.expand(X * X + X.det() * sp.eye(2)) == sp.zeros(2))
    m, h = sp.symbols("m h", positive=True)
    Xf = X.subs({al: 1 / m, be: 0, ga: 0})
    check("3.1 free fall is a shear", Xf**2 == sp.zeros(2) and sp.eye(2) + h * Xf == sp.Matrix([[1, h / m], [0, 1]]))


def iwasawa():
    a, b, c = sp.symbols("a b c", real=True)
    d = (1 + b * c) / a
    M = sp.Matrix([[a, b], [c, d]])
    r = sp.sqrt(a**2 + c**2)
    K = sp.Matrix([[a / r, -c / r], [c / r, a / r]])
    N = sp.Matrix([[1, (a * b + c * d) / r**2], [0, 1]])
    check("3.1 Iwasawa M = K A N", sp.simplify(K * sp.diag(r, 1 / r) * N - M) == sp.zeros(2))
    check("3.1 K orthogonal", sp.simplify(K.T * K) == sp.eye(2))


def receiver_split():
    random.seed(7)
    rat = lambda: sp.Rational(random.randint(-9, 9), random.randint(1, 5))
    ok = True
    for _ in range(20):
        L = sp.Matrix(3, 3, lambda i, j: rat() if i > j else (abs(rat()) + 1 if i == j else 0))
        G = L * L.T
        A = sp.Matrix(3, 3, lambda i, j: rat())
        dag = G.inv() * A.T * G
        T, B = (A - dag) / 2, (A + dag) / 2
        x = sp.Matrix(3, 1, lambda i, j: rat())
        ok &= T + B == A and G * T + T.T * G == sp.zeros(3) and G * B == B.T * G
        ok &= (A * x).T * G * x + x.T * G * (A * x) == 2 * x.T * G * B * x
        S = sp.Matrix(3, 3, lambda i, j: rat()) + 10 * sp.eye(3)
        A2, G2 = S.inv() * A * S, S.T * G * S
        dag2 = G2.inv() * A2.T * G2
        ok &= (A2 - dag2) / 2 == S.inv() * T * S
    check("3.2 split, uniqueness data, energy, rechart covariance (20 rational cases)", ok)
    t = sp.symbols("t")
    G = sp.Matrix(2, 2, lambda i, j: sp.Function(f"g{min(i, j)}{max(i, j)}")(t))
    A = sp.Matrix(2, 2, sp.symbols("A0:4"))
    x = sp.Matrix([sp.Function("x0")(t), sp.Function("x1")(t)])
    f = sp.Matrix(sp.symbols("f0 f1"))
    E = (x.T * G * x)[0] / 2
    Edot = sp.diff(E, t).subs({sp.Derivative(x[i], t): (A * x + f)[i] for i in range(2)})
    rhs = (x.T * (A.T * G + G * A + G.diff(t)) * x)[0] / 2 + (x.T * G * f)[0]
    check("3.2 energy with moving metric and forcing", sp.simplify(Edot - rhs) == 0)


def port_hamiltonian():
    j, r1, r2, r3, q1, q2, q3 = sp.symbols("j r1 r2 r3 q1 q2 q3")
    J = sp.Matrix([[0, j], [-j, 0]])
    R = sp.Matrix([[r1, r2], [r2, r3]])
    Q = sp.Matrix([[q1, q2], [q2, q3]])
    A = (J - R) * Q
    dag = Q.inv() * A.T * Q
    check("3.3 turn JQ, boost -RQ", sp.simplify((A - dag) / 2 - J * Q) == sp.zeros(2)
          and sp.simplify((A + dag) / 2 + R * Q) == sp.zeros(2))


def point_mass():
    vx, vy, Fx, Fy = sp.symbols("vx vy Fx Fy", real=True)
    m = sp.symbols("m", positive=True)
    v, F = vx + sp.I * vy, Fx + sp.I * Fy
    wdot = F / (m * v)
    power = sp.re(sp.conjugate(v) * F)
    check("3.3 power m|v|^2 Re(w')", sp.simplify(power - m * (vx**2 + vy**2) * sp.re(wdot)) == 0)
    check("3.3 signed turn rate", sp.simplify(sp.im(wdot) - sp.im(sp.conjugate(v) * F) / (m * (vx**2 + vy**2))) == 0)


def pivots():
    z, k, b = sp.symbols("z k b")
    O = b / (1 - k)
    check("3.4 complex pivot", sp.simplify(k * z + b - O - k * (z - O)) == 0)
    c, s = sp.Rational(4, 5), sp.Rational(3, 5)
    M = sp.Matrix([[c, -s, 0], [s, c, 0], [0, 0, 1]])
    bb = sp.Matrix([2, -1, sp.Rational(7, 3)])
    bpar = sp.Matrix([0, 0, bb[2]])
    o1, o2 = sp.symbols("o1 o2")
    Ov = sp.Matrix([o1, o2, 0])
    Ov = Ov.subs(sp.solve(list(((sp.eye(3) - M) * Ov - (bb - bpar))[:2]), [o1, o2]))
    y = sp.Matrix(sp.symbols("y1 y2 y3"))
    check("3.4 screw: turn about an axis, free fall along it", sp.simplify(M * y + bb - (Ov + M * (y - Ov) + bpar)) == sp.zeros(3, 1))
    Sh = sp.Matrix([[1, 1], [0, 1]])
    orbit = sp.zeros(2, 1)
    for _ in range(6):
        orbit = Sh * orbit + sp.Matrix([0, 1])
    check("3.4 shear orbit (n(n-1)/2, n) at n = 6", orbit == sp.Matrix([15, 6]))


def multiplier():
    z, a, bb, c, d = sp.symbols("z a bb c d")
    m = (a * z + bb) / (c * z + d)
    disc = sp.sqrt((a - d) ** 2 + 4 * bb * c)
    z1, z2 = (a - d + disc) / (2 * c), (a - d - disc) / (2 * c)
    mu1, mu2 = c * z1 + d, c * z2 + d
    check("3.5 multiplier is a cross ratio", sp.simplify(sp.together((m - z1) * (z - z2) * mu1 - mu2 * (z - z1) * (m - z2))) == 0)
    K = mu2 / mu1
    check("3.5 K + 1/K + 2 = tr^2/det", sp.simplify(K + 1 / K + 2 - (a + d) ** 2 / (a * d - bb * c)) == 0)
    check("3.5 K = -1 at trace zero", sp.simplify((K + 1).subs(d, -a)) == 0)
    check("3.5 K = m'(z1)", sp.simplify(sp.diff(m, z).subs(z, z1) - K) == 0)


def path():
    t = sp.symbols("t")
    w = sp.Function("w")(t)
    v = sp.exp(w)
    Y = [sp.Integer(1)]
    ok = True
    for n in range(1, 7):
        Y.append(sp.expand(sp.diff(Y[-1], t) + sp.diff(w, t) * Y[-1]))
        ok &= sp.simplify(sp.diff(v, t, n) - v * Y[n]) == 0
    check("3.6 x^(n+1) = v Y_n with the Bell recursion, n <= 6", ok)
    r, v0, x0 = sp.symbols("r v0 x0")
    xt = x0 + v0 * (sp.exp(r * t) - 1) / r
    check("3.6 constant rate: spiral about x0 - v0/r", sp.simplify((xt - (x0 - v0 / r)) - sp.exp(r * t) * v0 / r) == 0)
    l = sp.symbols("l", positive=True)
    ph = sp.Function("phi")(t)
    x = l * sp.exp(sp.I * ph)
    xd = sp.diff(x, t)
    check("3.6 pendulum rate", sp.simplify(sp.diff(xd, t) / xd - (sp.diff(ph, t, 2) / sp.diff(ph, t) + sp.I * sp.diff(ph, t))) == 0)


def sling_and_disk():
    a, b, c, e, d = sp.symbols("a b c e d", real=True)
    vi, V, k = a + sp.I * b, c + sp.I * e, sp.cos(d) + sp.I * sp.sin(d)
    vo = V + k * (vi - V)
    lhs = sp.expand(sp.expand_complex(vo * sp.conjugate(vo) - vi * sp.conjugate(vi)))
    rhs = sp.expand(sp.expand_complex(2 * sp.re(sp.conjugate(V) * (vo - vi))))
    check("3.8 sling speed change", sp.simplify(lhs - rhs) == 0)
    th = sp.symbols("theta", real=True)
    check("7 chord |k - 1|^2 = 4 sin^2(theta/2)", sp.simplify(sp.expand_complex(sp.Abs(sp.exp(sp.I * th) - 1) ** 2) - 4 * sp.sin(th / 2) ** 2) == 0)


def lifts():
    def E(i, j):
        m = sp.zeros(4)
        m[i, j] = 1
        return m
    Kx, Ky, Jz = E(0, 1) + E(1, 0), E(0, 2) + E(2, 0), E(2, 1) - E(1, 2)
    check("5.6 two boosts leave a turn", Kx * Ky - Ky * Kx == -Jz)
    x = sp.Matrix(sp.symbols("x1 x2 x3"))
    A = sp.Matrix(3, 3, sp.symbols("a0:9"))
    S, T = (A + A.T) / 2, (A - A.T) / 2
    grad = sp.Matrix([sp.diff((x.T * S * x)[0] / 2, v) for v in x])
    curl = lambda F: sp.Matrix([sp.diff(F[2], x[1]) - sp.diff(F[1], x[2]),
                                sp.diff(F[0], x[2]) - sp.diff(F[2], x[0]),
                                sp.diff(F[1], x[0]) - sp.diff(F[0], x[1])])
    check("5.4 linear Helmholtz", sp.simplify(grad - S * x) == sp.zeros(3, 1) and sp.simplify(curl(S * x)) == sp.zeros(3, 1)
          and sp.simplify(sum(sp.diff((T * x)[i], x[i]) for i in range(3))) == 0)
    M = sp.Matrix([[2, 1], [1, 1]])
    Q = sp.Matrix([[2, -1], [-1, -2]])
    check("5.2 [[2,1],[1,1]] holds x^2 - xy - y^2", M.T * Q * M == Q)
    t = sp.symbols("t")
    Ef = sp.Matrix([sp.Function(f"E{i}")(t, *x) for i in range(3)])
    Bf = sp.Matrix([sp.Function(f"B{i}")(t, *x) for i in range(3)])
    F = Ef + sp.I * Bf
    subs = {**{sp.Derivative(Ef[i], t): curl(Bf)[i] for i in range(3)},
            **{sp.Derivative(Bf[i], t): -curl(Ef)[i] for i in range(3)}}
    check("5.4 vacuum Maxwell is i dF/dt = curl F", sp.simplify((sp.I * F.diff(t) - curl(F)).subs(subs)) == sp.zeros(3, 1))
    be, th = sp.symbols("beta theta", real=True)
    check("5.7 Wick exchanges turn and boost", sp.expand(sp.I * (be + sp.I * th)) == -th + sp.I * be)


if __name__ == "__main__":
    quadratic_kinds()
    iwasawa()
    receiver_split()
    port_hamiltonian()
    point_mass()
    pivots()
    multiplier()
    path()
    sling_and_disk()
    lifts()
