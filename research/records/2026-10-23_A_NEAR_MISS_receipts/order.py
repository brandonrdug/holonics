"""Where a held face pays, and that its total does not depend on the reading order.
Products of operands 0..99. A reader holds the size (lengths, one leading digit each)
and some of the result's ring faces composed from the operands (q(ab) = q(a) q(b) mod q),
then reads the result's digits leading first or units first. Per-place cost is the
conditional entropy given the held faces and the digits already read (exact counts over
the uniform population; the logarithms are exterior readings). Also: a joint reading,
each place given every other place and the held faces. Places are counted from the units,
results padded to four places so every order reads the same word."""
import math, collections, json, time
t0 = time.perf_counter_ns()
R = range(100)
pop = [(a, b, a * b) for a in R for b in R]
def size(a, b): return (len(str(a)), len(str(b)), int(str(a)[0]), int(str(b)[0]))
def held(a, b, qs): return size(a, b) + tuple((a % q) * (b % q) % q for q in qs)
def word(n): return [(n // 10**k) % 10 for k in range(4)]  # place 0 = units
def H(counter):
    n = sum(counter.values()); return -sum(c / n * math.log2(c / n) for c in counter.values())
def cond(keyf, valf):
    groups = collections.defaultdict(collections.Counter)
    for a, b, p in pop: groups[keyf(a, b, p)][valf(a, b, p)] += 1
    N = len(pop); return sum(sum(c.values()) / N * H(c) for c in groups.values())
out = {}
for name, qs in [("size + ring 10", [10]), ("size + ring 10 + ring 9", [10, 9]),
                 ("size + ring 10 + ring 9 + ring 11", [10, 9, 11])]:
    row = {}
    for oname, order in [("leading first", [3, 2, 1, 0]), ("units first", [0, 1, 2, 3])]:
        per = {}
        for i, pl in enumerate(order):
            prev = order[:i]
            per[pl] = round(cond(lambda a, b, p: (held(a, b, qs), tuple(word(p)[j] for j in prev)),
                                 lambda a, b, p: word(p)[pl]), 3)
        row[oname] = {"per place (units, tens, hundreds, thousands)": [per[k] for k in range(4)],
                      "total": round(sum(per.values()), 3)}
    joint = [round(cond(lambda a, b, p: (held(a, b, qs), tuple(word(p)[j] for j in range(4) if j != k)),
                        lambda a, b, p: word(p)[k]), 3) for k in range(4)]
    row["joint (each place given all others)"] = joint
    row["whole word given the held faces"] = round(cond(lambda a, b, p: held(a, b, qs), lambda a, b, p: p), 3)
    out[name] = row
out["elapsed_ms"] = (time.perf_counter_ns() - t0) // 1_000_000
print(json.dumps(out, indent=1)); json.dump(out, open("order.json", "w"), indent=1)
