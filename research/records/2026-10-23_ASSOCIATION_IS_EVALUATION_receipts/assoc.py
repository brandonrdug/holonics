# Result digits of the passage's calculations <<expr=result>>: the lens's code by place, for
# expressions met earlier in the passage against unmet ones; and the faces' own information budget.
# usage: python3 -I assoc.py PASSAGE CELLS_F32 OUT_JSON
import json, re, sys, math, collections
import numpy as np
passage = open(sys.argv[1], "rb").read()
cells = np.fromfile(sys.argv[2], np.float32).reshape(-1, 3)   # base, node, ring bits per cell
assert cells.shape[0] == 4 * len(passage)
ring = cells[:, 2].reshape(-1, 4).sum(1).astype(np.float64)   # the lens's bits per byte (ring arm)
base = cells[:, 0].reshape(-1, 4).sum(1).astype(np.float64)
seen_expr, seen_pair = set(), set()
acc = collections.defaultdict(lambda: [0, 0.0, 0.0])          # key -> count, ring bits, base bits
op_re = re.compile(rb"^(\d+)([-+*/])(\d+)$")
faces = collections.defaultdict(collections.Counter)          # face key -> Counter(result face)
def add(key, i):
    a = acc[key]; a[0] += 1; a[1] += ring[i]; a[2] += base[i]
n_calc = n_int = 0
for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", passage):
    e, r = m.group(1), m.group(2)
    n_calc += 1
    state = "met" if e in seen_expr else "unmet"
    seen_expr.add(e); seen_pair.add((e, r))
    if not re.fullmatch(rb"\d+", r):
        continue
    n_int += 1
    L = len(r); s = m.start(2)
    for k in range(L):
        i = s + k
        left = min(k, 3); right = min(L - 1 - k, 3)
        add((state, "left", left), i)
        add((state, "right", right), i)
        if L >= 2:
            add((state, "lead" if k == 0 else ("units" if k == L - 1 else "middle")), i)
    o = op_re.match(e)
    if o and L >= 1:
        x, op, y = o.group(1), o.group(2).decode(), o.group(3)
        if op in "+-*":
            # trailing face: result units given operand units and the operation
            faces[("units|operand units", op)][(x[-1:], y[-1:], r[-1:])] += 1
            if L >= 2 and len(x) >= 1 and len(y) >= 1:
                # leading face: result's leading digit given operand leading digits and lengths
                faces[("lead|operand lead+lengths", op)][(x[:1], y[:1], len(x), len(y), r[:1], L)] += 1
                faces[("lead|operand two leading+lengths", op)][(x[:2], y[:2], len(x), len(y), r[:1], L)] += 1
def cond_entropy(c):
    # H(result face | the rest of the key), the last field(s) being the result face
    by = collections.defaultdict(collections.Counter)
    for k, n in c.items():
        if len(k) == 3: ctx, out = k[:2], k[2]
        else: ctx, out = k[:4], k[4:]
        by[ctx][out] += n
    tot = sum(c.values()); h = 0.0
    for ctx, cc in by.items():
        nn = sum(cc.values())
        for v in cc.values(): h -= v * math.log2(v / nn)
    return tot, h / tot, len(by)
out = {"calculations": n_calc, "integer results": n_int, "code": {}, "faces": {}}
for k in sorted(acc, key=str):
    n, rb, bb = acc[k]
    out["code"]["/".join(map(str, k))] = {"digits": n, "ring bits a digit": rb / n, "base bits a digit": bb / n}
for k, c in faces.items():
    tot, h, nctx = cond_entropy(c)
    out["faces"]["%s %s" % k] = {"calculations": tot, "bits a result digit": h, "contexts": nctx}
json.dump(out, open(sys.argv[3], "w"), indent=1)
for k, v in out["code"].items(): print("%-22s %7d  ring %.3f  base %.3f" % (k, v["digits"], v["ring bits a digit"], v["base bits a digit"]))
for k, v in out["faces"].items(): print("%-44s %6d  H %.4f  contexts %d" % (k, v["calculations"], v["bits a result digit"], v["contexts"]))
print("calculations", n_calc, "integer results", n_int)
