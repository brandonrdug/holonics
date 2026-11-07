#!/usr/bin/env python3
"""The held places' KL by place (theory, November 7, 08:25): from an ENUMERATED.tsv and the codec, each place's
KL(enumerated || face) in nats, the top tenth's share of the total, and their bytes and kinds (a bracket or a string's
quote, opening or closing; a block's newline, indent or colon; a letter, digit or other). A reading only."""
import csv, math, sys
rows = [r for r in csv.DictReader(open(sys.argv[1]), delimiter="\t") if r["lap"] == sys.argv[3]]
codec_bytes = [int(v) for v in open(sys.argv[2]).read().split("\n")[1].split()]
def kind(b):
    c = chr(b)
    if c in "([{": return "bracket-open"
    if c in ")]}": return "bracket-close"
    if c in "'\"": return "quote"
    if c == "\n": return "newline"
    if c in " \t": return "space"
    if c == ":": return "colon"
    if c.isalpha(): return "letter"
    if c.isdigit(): return "digit"
    return "other"
out = []
for r in rows:
    t = 2.0 ** (int(r["log2_t"]) / 2 ** 24)
    g = [int(v) / 2 ** 32 for v in r["energies"].split(",")]
    lo = min(g)
    w = [2.0 ** (-(x - lo) / t) for x in g]
    z = sum(w); p = [x / z for x in w]
    masses = [int(v) for v in r["face_masses"].split(",")]; total = int(r["face_total"])
    q = [max(m, 1) / total for m in masses]
    kl = sum(a * math.log(a / b) for a, b in zip(p, q) if a > 0)
    c = int(r["truth"]); b = codec_bytes[c] if c < len(codec_bytes) else -1
    kl_t, code_t = float("nan"), float("nan")
    if r.get("truth_face_masses"):
        tm = [int(v) for v in r["truth_face_masses"].split(",")]; tt = int(r["truth_face_total"])
        qt = [max(m, 1) / tt for m in tm]
        kl_t = sum(a * math.log(a / b2) for a, b2 in zip(p, qt) if a > 0)
        code_t = -math.log(qt[c])
    out.append((kl, r["problem"], r["place"], b, kind(b) if b >= 0 else "void", -math.log(p[c]), kl_t, code_t, -math.log(q[c])))
out.sort(reverse=True)
total = sum(x[0] for x in out)
top = out[: max(1, len(out) // 10)]
print(f"places {len(out)} open-face KL total {total:.3f} nats (mean {total / len(out):.3f}); the top tenth ({len(top)}) carries {sum(x[0] for x in top) / total:.1%}")
if not math.isnan(out[0][6]):
    kt = [x[6] for x in out]; st = sorted(kt, reverse=True)
    print(f"truth-face KL mean {sum(kt) / len(kt):.3f} nats, top tenth {sum(st[: len(top)]) / sum(kt):.1%}; codes: enumerated {sum(x[5] for x in out) / len(out):.3f}, open face {sum(x[8] for x in out) / len(out):.3f}, truth face {sum(x[7] for x in out) / len(out):.3f} nats a byte")
for kl, k, place, b, kd, code, kl_t, code_t, code_o in top:
    print(f"  problem {k} place {place}: byte {b} ({kd}) open-face KL {kl:.3f}, truth-face KL {kl_t:.3f} nats; enumerated code {code:.3f}, open face {code_o:.3f}, truth face {code_t:.3f}")
from collections import Counter
print("  kinds of the top tenth:", dict(Counter(x[4] for x in top)), "; of all places:", dict(Counter(x[4] for x in out)))
