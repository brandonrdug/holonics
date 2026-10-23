# Exact carry fibre of a result's leading digit given the operands' leading face (k leading digits and
# lengths), by interval enclosure (radix.leading-fibre), over the passage's single-operation integer
# calculations; and the trailing face's fibre (always one digit for + - *).
# usage: python3 -I fibre.py PASSAGE OUT_JSON
import json, re, sys, math, collections
passage = open(sys.argv[1], "rb").read()
op_re = re.compile(rb"^(\d+)([-+*])(\d+)$")
def lead_digits(lo, hi):
    # distinct leading digits of the integers in [lo, hi], lo >= 1
    s = set(); d = 10 ** (len(str(lo)) - 1)
    while d <= hi:
        a, b = max(lo, d), min(hi, 10 * d - 1)
        if a <= b:
            for q in range(a // d, b // d + 1): s.add(q)
        if len(s) == 9: break
        d *= 10
    return s
def face(x, k):
    # interval of operands sharing x's k leading digits and its length
    n = len(x)
    if n <= k: v = int(x); return v, v
    A = int(x[:k]); u = 10 ** (n - k)
    return A * u, (A + 1) * u - 1
tot = collections.defaultdict(lambda: [0, 0.0, 0, 0])   # (op, k) -> calcs, sum log2 fibre, fibre==1, result in fibre
for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", passage):
    o = op_re.match(m.group(1)); r = m.group(2)
    if not o or not re.fullmatch(rb"\d+", r) or int(r) == 0: continue
    x, op, y = o.group(1).decode(), o.group(2).decode(), o.group(3).decode()
    for k in (1, 2):
        (xl, xh), (yl, yh) = face(x, k), face(y, k)
        if op == "+": lo, hi = xl + yl, xh + yh
        elif op == "*": lo, hi = xl * yl, xh * yh
        else: lo, hi = max(1, xl - yh), xh - yl
        if hi < 1: continue
        f = lead_digits(max(lo, 1), hi)
        t = tot[(op, k)]; t[0] += 1; t[1] += math.log2(len(f)); t[2] += len(f) == 1; t[3] += int(chr(r[0])) in f
out = {}
for (op, k), (n, s, one, inside) in sorted(tot.items()):
    out["%s k=%d" % (op, k)] = {"calculations": n, "mean log2 fibre": s / n, "fibre one digit": one / n, "result inside fibre": inside / n}
    print("%s k=%d  %5d calcs  mean log2 fibre %.4f  exact %.4f  result inside %.4f" % (op, k, n, s / n, one / n, inside / n))
json.dump(out, open(sys.argv[2], "w"), indent=1)
