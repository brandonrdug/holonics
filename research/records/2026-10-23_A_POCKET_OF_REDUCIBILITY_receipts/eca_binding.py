"""Which of the 256 elementary cellular automaton rules are one crossing, and in which chart.

A rule is f(l, c, r) in {0,1}. Two receiving charts:
- GF(2) phase chart: f is one crossing (superposition holds, the rule is additive) exactly when every
  mixed difference of f vanishes mod 2, i.e. its algebraic normal form (Zhegalkin polynomial) has
  degree <= 1. The degree is the order of the binding the rule needs (2 = a pair contact, 3 = a
  triple).
- Threshold (locked-sheet, Ising) chart: f is one crossing when f = [w_l l + w_c c + w_r r >= t]
  for integer weights, i.e. a single locked sheet reading a weighted sum (Goto's parametron gate).
Exact integer work; the threshold search is over weights and thresholds in -3..3, which is
complete for 3-input threshold functions (all are realizable with |w| <= 2, |t| <= 3).
"""
import itertools, json

inputs = list(itertools.product((0, 1), repeat=3))  # (l, c, r)

def table(rule):
    # Wolfram numbering: neighbourhood value 4l+2c+r indexes the bit of the rule number
    return {x: (rule >> (4 * x[0] + 2 * x[1] + x[2])) & 1 for x in inputs}

def anf(f):
    # Moebius transform over GF(2): coefficient of monomial S = XOR over subsets of S
    coeff = {}
    for S in inputs:
        s = 0
        for x in inputs:
            if all(x[i] <= S[i] for i in range(3)):
                s ^= f[x]
        coeff[S] = s
    return coeff

def degree(c):
    return max((sum(S) for S, v in c.items() if v), default=-1)

thresholds = set()
for w in itertools.product(range(-3, 4), repeat=3):
    for t in range(-4, 5):
        f = tuple(1 if w[0] * l + w[1] * c + w[2] * r >= t else 0 for (l, c, r) in inputs)
        thresholds.add(f)

rows = {}
deg_count = {}
for rule in range(256):
    f = table(rule)
    d = degree(anf(f))
    key = tuple(f[x] for x in inputs)
    rows[rule] = {"anf_degree": d, "threshold": key in thresholds}
    deg_count[d] = deg_count.get(d, 0) + 1

affine = sorted(r for r, v in rows.items() if v["anf_degree"] <= 1)
thr = sorted(r for r, v in rows.items() if v["threshold"])
both = sorted(set(affine) & set(thr))
def mono(rule):
    c = anf(table(rule))
    names = []
    for S, v in sorted(c.items(), key=lambda kv: (sum(kv[0]), kv[0])):
        if v:
            names.append("1" if sum(S) == 0 else "".join(n for n, s in zip("lcr", S) if s))
    return " + ".join(names) if names else "0"

out = {
    "rules": 256,
    "anf degree counts (-1 = rule 0)": {str(k): v for k, v in sorted(deg_count.items())},
    "one crossing in GF(2) (affine)": affine,
    "count affine": len(affine),
    "count threshold (one locked sheet)": len(thr),
    "affine and threshold": both,
    "one crossing in either chart": len(set(affine) | set(thr)),
    "named rules": {r: {"anf": mono(r), "degree": rows[r]["anf_degree"], "threshold": rows[r]["threshold"]}
                    for r in (30, 90, 110, 150, 184, 232, 54, 22, 126)},
}

# Conserved count (a face kept by every step: T_q = identity on sum x_i), checked on every cyclic
# configuration of length 1..12.
def step(rule, x):
    n = len(x)
    return tuple((rule >> (4 * x[(i - 1) % n] + 2 * x[i] + x[(i + 1) % n])) & 1 for i in range(n))

conserving = []
for rule in range(256):
    if all(sum(step(rule, x)) == sum(x)
           for n in range(1, 13) for x in itertools.product((0, 1), repeat=n)):
        conserving.append(rule)

# The additive rule's jump: rule 90 iterated 2^k times is x_(i-2^k) + x_(i+2^k) (Frobenius:
# (s^-1 + s)^(2^k) = s^(-2^k) + s^(2^k) over GF(2)); checked on every cyclic configuration of
# length 16 for k = 0..3.
def jump_holds(k, n=16):
    for x in itertools.product((0, 1), repeat=n):
        y = x
        for _ in range(2 ** k):
            y = step(90, y)
        if y != tuple(x[(i - 2 ** k) % n] ^ x[(i + 2 ** k) % n] for i in range(n)):
            return False
    return True

out2 = {"count-conserving rules (cyclic, lengths 1..12)": conserving,
        "rule 90 jump 2^k steps, k = 0..3, length 16": [jump_holds(k) for k in range(4)]}
out.update(out2)
print(json.dumps(out, indent=1))
