"""Exact checks for the one face law across operations (exterior read; integers and exact
rationals only).

For an operation T and a face q, q is conserved by T when q(T(x, y)) is a function of
(q(x), q(y)); otherwise some pair of face values has a plural fibre. For each instance this
script counts the face-value pairs whose fibre is plural, and for the string instance it
computes the right-congruence classes that refine the face (Myhill-Nerode) and the
four-cycle census of the seam.
"""
import itertools, json
from fractions import Fraction


def fibres(pairs, op, q):
    """Map (q(x), q(y)) -> set of q(op(x, y)) over the given operand pairs."""
    fib = {}
    for x, y in pairs:
        fib.setdefault((q(x), q(y)), set()).add(q(op(x, y)))
    plural = sum(1 for v in fib.values() if len(v) > 1)
    return len(fib), plural


out = {}

# 1. Words under concatenation over the alphabet {t, h, a}.
A = "tha"
words = ["".join(w) for n in range(0, 5) for w in itertools.product(A, repeat=n)]
pairs = [(x, y) for x in words for y in words]
cat = lambda x, y: x + y
faces = {
    "length": len,
    "length mod 2": lambda w: len(w) % 2,
    "count of a mod 3": lambda w: w.count("a") % 3,
    "last letter": lambda w: w[-1:] ,
    "contains th": lambda w: "th" in w,
    "contains th, ends t, starts h": lambda w: ("th" in w, w.endswith("t"), w.startswith("h")),
    "contains th, ends t, starts h, empty": lambda w: ("th" in w, w.endswith("t"),
                                                       w.startswith("h"), w == ""),
}
out["concatenation"] = {name: dict(zip(("face_pairs", "plural_fibres"), fibres(pairs, cat, q)))
                        for name, q in faces.items()}

# Right congruence refining "contains th": x ~ x' iff for every suffix s, xs and x's agree.
member = lambda w: "th" in w
long_words = ["".join(w) for n in range(0, 7) for w in itertools.product(A, repeat=n)]
suffixes = ["".join(w) for n in range(0, 5) for w in itertools.product(A, repeat=n)]
classes = {}
for w in long_words:
    sig = tuple(member(w + s) for s in suffixes)
    classes.setdefault(sig, []).append(w)
out["contains_th_right_congruence"] = {
    "words": len(long_words), "suffixes": len(suffixes), "classes": len(classes),
    "class_examples": sorted(min(v, key=lambda w: (len(w), w)) for v in classes.values()),
}

# Two-sided (syntactic) congruence: x ~ x' iff for every context (u, v), uxv and ux'v agree.
contexts = ["".join(w) for n in range(0, 4) for w in itertools.product(A, repeat=n)]
sclasses = {}
for w in long_words:
    sig = tuple(member(u + w + v) for u in contexts for v in contexts)
    sclasses.setdefault(sig, []).append(w)
out["contains_th_syntactic_congruence"] = {
    "words": len(long_words), "contexts_per_side": len(contexts), "classes": len(sclasses),
    "class_examples": sorted(min(v, key=lambda w: (len(w), w)) for v in sclasses.values()),
}

# Four-cycle of G(x, y) = [xy contains th] over unit squares of words of length 1..2,
# restricted to x, y that do not contain th themselves (so only the seam can bind).
short = [w for w in words if 1 <= len(w) <= 2 and "th" not in w]
G = lambda x, y: int("th" in x + y)
nonzero, straddle, total = 0, 0, 0
for x, x2 in itertools.combinations(short, 2):
    for y, y2 in itertools.combinations(short, 2):
        total += 1
        s = G(x, y) - G(x, y2) - G(x2, y) + G(x2, y2)
        if s != 0:
            nonzero += 1
            seam = lambda u, v: u.endswith("t") and v.startswith("h")
            if seam(x, y) or seam(x, y2) or seam(x2, y) or seam(x2, y2):
                straddle += 1
out["contains_th_four_cycle"] = {"rectangles": total, "nonzero": nonzero,
                                 "nonzero_with_a_t_h_seam": straddle}

# 2. 2x2 integer matrices with entries in {-1, 0, 1} under the product.
ents = (-1, 0, 1)
mats = [((a, b), (c, d)) for a, b, c, d in itertools.product(ents, repeat=4)]
mul = lambda X, Y: tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2))
                         for i in range(2))
det = lambda X: X[0][0] * X[1][1] - X[0][1] * X[1][0]
tr = lambda X: X[0][0] + X[1][1]
mpairs = [(X, Y) for X in mats for Y in mats]
out["matrix_product"] = {
    "matrices": len(mats),
    "det": dict(zip(("face_pairs", "plural_fibres"), fibres(mpairs, mul, det))),
    "trace": dict(zip(("face_pairs", "plural_fibres"), fibres(mpairs, mul, tr))),
    "trace and det": dict(zip(("face_pairs", "plural_fibres"),
                              fibres(mpairs, mul, lambda X: (tr(X), det(X))))),
    "trace of product equals Frobenius pairing on every pair":
        all(tr(mul(X, Y)) == sum(X[i][k] * Y[k][i] for i in range(2) for k in range(2))
            for X, Y in mpairs),
}

# 3. Polynomials of degree <= 2 with coefficients in {-1, 0, 1} under the product,
#    read at the point 2: value, derivative alone, and the jet (value, derivative).
coeffs = list(itertools.product((-1, 0, 1), repeat=3))
pmul = lambda f, g: tuple(sum(f[i] * g[k - i] for i in range(len(f)) if 0 <= k - i < len(g))
                          for k in range(len(f) + len(g) - 1))
val = lambda f, x=2: sum(c * x ** i for i, c in enumerate(f))
der = lambda f, x=2: sum(i * c * x ** (i - 1) for i, c in enumerate(f) if i > 0)
ppairs = [(f, g) for f in coeffs for g in coeffs]
out["polynomial_product_at_2"] = {
    "polynomials": len(coeffs),
    "value": dict(zip(("face_pairs", "plural_fibres"), fibres(ppairs, pmul, val))),
    "derivative": dict(zip(("face_pairs", "plural_fibres"), fibres(ppairs, pmul, der))),
    "jet (value, derivative)": dict(zip(("face_pairs", "plural_fibres"),
                                        fibres(ppairs, pmul, lambda f: (val(f), der(f))))),
    "leibniz holds on every pair":
        all(der(pmul(f, g)) == der(f) * val(g) + val(f) * der(g) for f, g in ppairs),
}

# 4. Permutations of four points under composition: sign and cycle type.
perms = list(itertools.permutations(range(4)))
comp = lambda p, s: tuple(p[s[i]] for i in range(4))
def sign(p):
    return (-1) ** sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])
def cycle_type(p):
    seen, lens = set(), []
    for i in range(4):
        if i not in seen:
            n, j = 0, i
            while j not in seen:
                seen.add(j); j = p[j]; n += 1
            lens.append(n)
    return tuple(sorted(lens))
spairs = [(p, s) for p in perms for s in perms]
out["permutation_composition"] = {
    "permutations": len(perms),
    "sign": dict(zip(("face_pairs", "plural_fibres"), fibres(spairs, comp, sign))),
    "cycle type": dict(zip(("face_pairs", "plural_fibres"), fibres(spairs, comp, cycle_type))),
}

# 5. Typed application: types are base symbols or arrows; the type face of an application
#    is the arrow's codomain when its domain matches (cancellation, as B/A times A is B).
base = ["N", "B"]
types = base + [(a, b) for a in base for b in base] + [((a, b), c) for a in base for b in base
                                                        for c in base]
def apply_type(f, x):
    if isinstance(f, tuple) and f[0] == x:
        return f[1]
    return None
tpairs = [(f, x) for f in types for x in types]
typed = [(f, x) for f, x in tpairs if apply_type(f, x) is not None]
out["typed_application"] = {
    "types": len(types), "pairs": len(tpairs), "well_typed": len(typed),
}

print(json.dumps(out, indent=1, default=str))
