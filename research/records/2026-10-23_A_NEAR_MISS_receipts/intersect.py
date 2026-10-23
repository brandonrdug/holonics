"""How many cheap faces close a two-digit product's fibre.
Size face: one leading digit and the length of each operand (radix.leading-fibre).
Ring faces: last digit (ring 10 = 2 x 5), digit sum (ring 9), alternating sum (ring 11),
alternating digit pairs (ring 101) (radix.cheap-faces). Exact integers only."""
import json, time
from collections import Counter
t0 = time.perf_counter_ns()
rings = [("units", 10), ("+ring 9", 9), ("+ring 11", 11), ("+ring 101", 101)]
out = {}
pairs = [(a, b) for a in range(10, 100) for b in range(10, 100)]
for k in range(len(rings) + 1):
    used = [q for _, q in rings[:k]]
    sizes = Counter()
    for a, b in pairs:
        A, B = a // 10, b // 10
        lo, hi = A * B * 100, (A * 10 + 9) * (B * 10 + 9)
        p = a * b
        n = sum(1 for c in range(lo, hi + 1) if all(c % q == p % q for q in used))
        sizes[n] += 1
    name = "size only" if k == 0 else "size + " + " ".join(r for r, _ in rings[:k])
    tot = len(pairs)
    mean_bits = sum(cnt * __import__("math").log2(n) for n, cnt in sizes.items()) / tot
    out[name] = {"closed_share": f"{sizes[1]}/{tot}", "max_fibre": max(sizes),
                 "mean_log2_fibre": round(mean_bits, 3)}
# the four products Brandon named: fibre counts at each stage
named = [(92, 65, 6090), (83, 27, 2309), (46, 15, 850), (12, 35, 405)]
rows = []
for a, b, d in named:
    A, B = a // 10, b // 10
    lo, hi = A * B * 100, (A * 10 + 9) * (B * 10 + 9)
    p = a * b
    row = {"draw": f"{a}*{b}={d}", "true": p, "fibre": [lo, hi]}
    for k in range(len(rings) + 1):
        used = [q for _, q in rings[:k]]
        row[f"stage{k}"] = sum(1 for c in range(lo, hi + 1) if all(c % q == p % q for q in used))
    row["draw_keeps"] = {f"ring {q}": d % q == p % q for q in (2, 5, 9, 11, 101)}
    rows.append(row)
out["named"] = rows
out["elapsed_ms"] = (time.perf_counter_ns() - t0) // 1_000_000
json.dump(out, open("intersect.json", "w"), indent=1)
print(json.dumps(out, indent=1))
