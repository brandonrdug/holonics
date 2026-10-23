"""Per-place cost of a product's digits (operands 0..99, leading digit first,
teacher-forced) for a reader that keeps the size and the result's faces on the
base's cheap rings, each predicted from the operands by one crossing
(p mod q = (a mod q)(b mod q) mod q). Exact integer work; entropies are exterior readings."""
import math, collections, json, time
t0 = time.perf_counter_ns()
def digits(n): return [int(c) for c in str(n)]
def cost(pairs, face):
    groups = collections.defaultdict(collections.Counter); items = []
    for a, b, r in pairs:
        f = face(a, b); ds = digits(r)
        for k, d in enumerate(ds):
            key = (f, tuple(ds[:k])); groups[key][d] += 1; items.append((key, d, len(ds) - 1 - k))
    by = collections.defaultdict(lambda: [0.0, 0])
    for key, d, place in items:
        c = groups[key]; by[place][0] += -math.log2(c[d] / sum(c.values())); by[place][1] += 1
    return {str(pl): round(s / n, 3) for pl, (s, n) in sorted(by.items())}
R = range(100)
prod = [(a, b, a*b) for a in R for b in R]
def size(a, b): return (len(str(a)), len(str(b)), int(str(a)[0]), int(str(b)[0]))
def ring(q): return lambda a, b: (a % q) * (b % q) % q
out = {}
for name, qs in [("size", []), ("size + ring 2", [2]), ("size + ring 5", [5]), ("size + ring 10", [10]),
                 ("size + ring 10 + ring 9", [10, 9]), ("size + ring 10 + ring 9 + ring 11", [10, 9, 11])]:
    out[name] = cost(prod, lambda a, b, qs=qs: size(a, b) + tuple(ring(q)(a, b) for q in qs))
out["elapsed_ms"] = (time.perf_counter_ns() - t0) // 1_000_000
for k, v in out.items(): print(f"{k:40s} {v}")
json.dump(out, open("rings.json", "w"), indent=1)
