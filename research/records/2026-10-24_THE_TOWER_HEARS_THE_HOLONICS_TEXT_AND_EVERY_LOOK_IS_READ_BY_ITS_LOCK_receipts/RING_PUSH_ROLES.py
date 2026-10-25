# Exterior: where the founded ring's state factors open, |α γ| = |aᵀŝ| |gᵀ(ŝ, 2^16)| at each cell
# of the held-out sums, by the arriving byte's role in its line, from a full modes reading of the
# base tower (ŝ = level 0's state before the move, on 2^-16) and the forms file.
import sys, math, collections
text = open(sys.argv[1], "rb").read()
forms = open(sys.argv[3]).read().split("\n")
def field(line, k): return [int(v) for v in line.split(k + "=", 1)[1].split()[0].split(",")]
fl = [l for l in forms if l.startswith("FORM 0")][0]; rl = [l for l in forms if l.startswith("RING 0")][0]
a0, a1, g = field(fl, "a"), field(fl, "ai"), field(rl, "g")
ra, rb, rg = field(rl, "release")
def rel(x, s): return (x + (1 << (s - 1))) >> s if s else x
def role(i):
    s = text.rfind(b"\n", 0, i) + 1; e = text.find(b"\n", i); e = len(text) if e < 0 else e
    line = text[s:e]; j = i - s
    if i == e: return "newline"
    lhs, rhs = line.split(b"=")
    A, B = lhs.split(b"+")
    if j < len(A): return "A%s%d" % (len(A), len(A) - 1 - j)
    if j == len(A): return "plus(A%d,B%d)" % (len(A), len(B))
    if j < len(lhs): k = j - len(A) - 1; return "B%s%d(A%d)" % (len(B), len(B) - 1 - k, len(A))
    if j == len(lhs): return "eq(B%d)" % len(B)
    k = j - len(lhs) - 1; return "C%d%d" % (len(rhs), len(rhs) - 1 - k)
by = collections.defaultdict(list)
for line in open(sys.argv[2]):
    if not line.startswith("MODES "): continue
    p = line.split(); i = int(p[1])
    modes = [[int(v) for v in m.split(",")] for m in p[4].split("=", 1)[1].split(";")]
    s = []
    for m in modes: s += [rel(m[0], 8), rel(m[1], 8)]
    al = (rel(sum(x * y for x, y in zip(a0, s)), ra), rel(sum(x * y for x, y in zip(a1, s)), ra))
    ga = rel(sum(x * y for x, y in zip(g, s)) + g[len(s)] * (1 << 16), rg)
    by[role(i)].append(math.hypot(*al) * abs(ga))
top = max(sum(v) / len(v) for v in by.values())
for r in sorted(by, key=lambda r: -sum(by[r]) / len(by[r])):
    v = by[r]; print("%-14s n=%4d  |αγ| mean %.4f of the largest role's" % (r, len(v), sum(v) / len(v) / top))
