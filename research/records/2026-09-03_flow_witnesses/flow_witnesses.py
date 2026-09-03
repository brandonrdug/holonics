"""Exact witnesses for research/records/2026-09-03_THE_SEAMS_ARE_LOCAL_OPTIMA_OF_THE_THREAD_ENERGY_THE_PRIMES_ARE_THE_MISSING_HALF_AND_THE_FLOW_BINDS_THE_INTEGER_EVENTS.md
Observer computation (sympy over Q and exact algebraics); it is apparatus outside the engine.
Run: /home/b/scratch/huggingface/.venv/bin/python -u research/records/2026-09-03_flow_witnesses/flow_witnesses.py
No float determines any reported result: bisection probes are exact rationals, counts are Sturm counts."""
import sys, time
import sympy as sp
from sympy import Rational as Q
x, t, v, u, L = sp.symbols('x t v u L', real=True)
T0 = time.time()
def heat(p, tt):
    d = sp.Poly(p, x).degree(); out = sp.Integer(0)
    for k in range(d//2 + 1):
        out += (-tt)**k / sp.factorial(k) * sp.diff(p, x, 2*k)
    return sp.expand(out)

print("== A. heat_{1/2} X^n = He_n; Stieltjes gradient == 0 at its zeros; self-similar dilation ==", flush=True)
tt = sp.symbols('tt', positive=True)
for n in range(2, 6):
    h = heat(x**n, Q(1,2)); He = sp.expand(sp.hermite_prob(n, x))
    assert sp.expand(h - He) == 0
    roots = sp.Poly(He, x).all_roots(); assert all(r.is_real for r in roots)
    grads = [sp.simplify(rj/2 - sum(1/(rj-rk) for rk in roots if rk != rj)) for rj in roots]
    assert all(g == 0 for g in grads), grads
    lhs = heat(x**n, tt); rhs = sp.expand((2*tt)**sp.Rational(n,2) * sp.hermite_prob(n, x/sp.sqrt(2*tt)))
    assert sp.simplify(lhs - rhs) == 0
    print(f"  n={n}: heat_(1/2) x^n == He_n exactly; grad[sum x_j^2/4 - sum_{{j<k}} log|x_j-x_k|] == 0 at all roots; heat_t x^n == (2t)^(n/2) He_n(x/sqrt(2t))", flush=True)

print("== B. binding defect, running abscissa, and the kernel as translates (symbolic, exact) ==", flush=True)
m, k = sp.symbols('m k', positive=True)
assert sp.expand(t*(sp.log(m)+sp.log(k))**2 - (t*sp.log(m)**2 + t*sp.log(k)**2 + 2*t*sp.log(m)*sp.log(k))) == 0
print("  exp(t log(mk)^2) = exp(t log m^2) exp(t log k^2) exp(2 t log m log k)", flush=True)
assert sp.expand(t*(v - L)**2 - (t*v**2 - 2*t*v*L + t*L**2)) == 0
print("  exp(t(v-log n)^2) = exp(t v^2) n^(-2tv) exp(t log n^2)", flush=True)
nn = sp.exp(L)  # n = e^L
phi = lambda w: (2*sp.pi**2*sp.exp(sp.Rational(9,2)*w) - 3*sp.pi*sp.exp(sp.Rational(5,2)*w))*sp.exp(-sp.pi*sp.exp(2*w))
term_n = (2*sp.pi**2*nn**4*sp.exp(sp.Rational(9,2)*u) - 3*sp.pi*nn**2*sp.exp(sp.Rational(5,2)*u))*sp.exp(-sp.pi*nn**2*sp.exp(2*u))
rhs = nn**Q(-1,2)*phi(u+L)
d = sp.simplify(sp.powsimp(sp.expand(term_n - rhs), force=True))
assert d == 0, d
print("  Phi_n(u) = n^(-1/2) phi(u + log n): the de Bruijn kernel is one profile translated to the integer events", flush=True)

print("== C. polynomial thresholds by exact bisection (Sturm counts over Q) ==", flush=True)
def nonreal(p, tt):
    q = sp.Poly(heat(p, tt), x); return q.degree() - sp.count_roots(q)
def bracket(p, H, steps=30):
    """exact rational bracket (lo, hi] with lo < lambda(p) <= hi.  H = max pair height (exact).
    hi starts at a rational >= H^2/2, real-rooted there by PairDescent; the real-rooted times are an up-set."""
    hi = sp.Rational(sp.ceiling(H**2/2 * 4 + 1), 4)
    assert nonreal(p, hi) == 0, "PairDescent bound violated"
    lo = sp.Integer(0); assert nonreal(p, lo) > 0
    for _ in range(steps):
        mid = (lo+hi)/2
        if nonreal(p, mid) == 0: hi = mid
        else: lo = mid
    return lo, hi
def pair(a, b): return sp.expand((x-a)**2 + b**2)
def reals(*rs):
    out = sp.Integer(1)
    for r in rs: out *= (x**2 - r**2)
    return out
cases = [
    ("p=x^2+1 ; q=(x-3)^2+1",                    pair(0,1), 1, pair(3,1), 1),
    ("p=x^2+1 ; q=x^2+4",                        pair(0,1), 1, pair(0,2), 2),
    ("p=(x^2+1)(x^2-4) ; q=(x^2+1)(x^2-4)",      sp.expand(pair(0,1)*reals(2)), 1, sp.expand(pair(0,1)*reals(2)), 1),
    ("p=x^2+1 ; q=((x-2)^2+4)(x^2-1)(x^2-9)",    pair(0,1), 1, sp.expand(pair(2,2)*reals(1,3)), 2),
    ("p=x^2+1 ; q=(x^2+4)(x^2-9)(x^2-16)",       pair(0,1), 1, sp.expand(pair(0,2)*reals(3,4)), 2),
    ("p=x^2+1 ; q=(x^2+9)(x^2-1)(x^2-4)(x^2-9)", pair(0,1), 1, sp.expand(pair(0,3)*reals(1,2,3)), 3),

    ("p=x^2+1 ; q=x^2+(11/10)^2  [pairs nearly level: maximal lift]",  pair(0,1), 1, pair(0,Q(11,10)), Q(11,10)),
    ("p=x^2+1 ; q=(x-1/2)^2+(11/10)^2  [nearly level, offset]",     pair(0,1), 1, pair(Q(1,2),Q(11,10)), Q(11,10)),
    ("p=x^2+1 ; q=(x^2+(11/10)^2)(x^2-4)(x^2-9)  [level pair, reals lower q's own threshold]", pair(0,1), 1, sp.expand(pair(0,Q(11,10))*reals(2,3)), Q(11,10)),
    ("p=x^2+1 ; q=(x^2+(6/5)^2)(x^2-1/4)^2  [close reals lower q's threshold below p's]", pair(0,1), 1, sp.expand(pair(0,Q(6,5))*reals(Q(1,2))**2), Q(6,5)),
    ("p=(x^2+1)(x^2-1/4)^3 ; q=(x^2+(6/5)^2)(x^2-1/4)^3",  sp.expand(pair(0,1)*reals(Q(1,2))**3), 1, sp.expand(pair(0,Q(6,5))*reals(Q(1,2))**3), Q(6,5)),
    ("p=x^2+1 ; q=(x^2+4)(x^2-1/4)^4  [high pair, dense close reals]", pair(0,1), 1, sp.expand(pair(0,2)*reals(Q(1,2))**4), 2),
]
for name, p, Hp, q, Hq in cases:
    t0 = time.time()
    lp, hp = bracket(p, Hp); lq, hq = bracket(q, Hq); lpq, hpq = bracket(sp.expand(p*q), max(Hp, Hq))
    mx_lo, mx_hi = max(lp, lq), max(hp, hq)
    if lpq >= mx_hi: rel = "lambda(pq) > max(lambda p, lambda q)   [BINDING: the composite lands later than either constituent]"
    elif hpq <= mx_lo: rel = "lambda(pq) < max(lambda p, lambda q)   [the composite lands earlier than the slower constituent]"
    else: rel = "undecided at this width (brackets overlap)"
    print(f"  {name}   [{time.time()-t0:.1f}s]", flush=True)
    print(f"     lambda(p) in ({lp}, {hp}]  ~{sp.N(hp,8)} ; lambda(q) in ({lq}, {hq}]  ~{sp.N(hq,8)} ; lambda(pq) in ({lpq}, {hpq}]  ~{sp.N(hpq,8)}", flush=True)
    print(f"     {rel}", flush=True)
print(f"total {time.time()-T0:.1f}s")
