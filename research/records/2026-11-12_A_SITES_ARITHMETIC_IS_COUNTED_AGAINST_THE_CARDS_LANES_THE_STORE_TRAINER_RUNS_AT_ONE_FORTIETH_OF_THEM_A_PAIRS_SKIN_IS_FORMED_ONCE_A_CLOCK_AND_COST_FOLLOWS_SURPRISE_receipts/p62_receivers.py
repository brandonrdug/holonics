"""p62_receivers: P62's readings from read-receivers' lines (a host ruler; numbers only).

usage: python3 -I p62_receivers.py LOG A0_TSV LINE_CAVITY_TSV
Codes on 2^-20 bits are read as nats a place (code / 2^20 ln 2). A0's codes are compared place by place with the line's own read of the same
state (read-cavity's P and W rows, its cK).
"""
import math
import re
import sys

LN2 = math.log(2.0)
SLICES = ["code", "web", "science", "books", "wikidata"]
log, a0_tsv, line_tsv = sys.argv[1:4]
arms = {}
sections = []
for line in open(log):
    if line.startswith("RECEIVERS_ARM"):
        m = re.match(r"RECEIVERS_ARM arm=(\S+) kind=(\S+) rows=(\d+) computed=(\d+) code_sum_2\^-20_bits=(-?\d+) places=(\d+) \| (.*) ms=", line)
        arm, kind, rows, computed, code, places, parts = m.groups()
        by = {}
        for p in parts.split():
            s, v = p.split("=")
            c, n = v.split("/")
            by[s] = (int(c), int(n))
        arms[(arm, kind)] = dict(rows=int(rows), computed=int(computed), code=int(code), places=int(places), by=by)
    if line.startswith("RECEIVERS_SECTIONS"):
        sections.append(dict(w.split("=", 1) for w in line.split()[1:]))


def nats(c, n):
    return c / float(1 << 20) * LN2 / max(n, 1)


print("P62_RECEIVERS nats a place at open places through the trained readout at the last tick; pooled, then by slice with the count")
for kind in ("one_place", "whole"):
    for arm in ("A0", "A1", "A2", "A3.0", "A3.1", "A3.2"):
        a = arms[(arm, kind)]
        print("ARM %s %s pooled=%.4f places=%d computed_rows=%d of %d (%.4f) | %s" % (arm, kind, nats(a["code"], a["places"]), a["places"], a["computed"], a["rows"], a["computed"] / max(a["rows"], 1),
              " ".join("%s=%.4f(%d)" % (s, nats(*a["by"][s]), a["by"][s][1]) for s in SLICES if s in a["by"])))
    base = arms[("A0", kind)]
    a2 = arms[("A2", kind)]
    a3 = [arms[("A3.%d" % d, kind)] for d in range(3)]

    def diff(x, y):
        return nats(x["code"], x["places"]) - nats(y["code"], y["places"])

    def diff_by(x, y):
        return " ".join("%s=%+.4f" % (s, nats(*x["by"][s]) - nats(*y["by"][s])) for s in SLICES if s in x["by"] and x["by"][s][1])
    print("DIFF %s A1_over_A0=%+.4f | %s" % (kind, diff(arms[("A1", kind)], base), diff_by(arms[("A1", kind)], base)))
    print("DIFF %s A2_over_A0=%+.4f | %s" % (kind, diff(a2, base), diff_by(a2, base)))
    d3 = [diff(x, a2) for x in a3]
    print("DIFF %s A3_over_A2 draws=%s mean=%+.4f" % (kind, " ".join("%+.4f" % v for v in d3), sum(d3) / 3))
print("A4 not run: the support's keyed mark (ClassLists::keyed) gates the near field alone; a written place is heard far as a definite member of a probed class or as a definite site an open receiver listens to, and nothing marks it unheard there without a new mechanism")
print("# the sections (the held role's, cut as read-store cuts them), by pass in one hold")
for s in sections:
    sites = int(s["sites"])
    print("SECTIONS pass=%s arm=%s sites=%d open=%s (%.4f) written_landmark=%s (%.4f) written_other=%s (%.4f) computed=%d (%.4f) pairs=%s forward_ms=%s code_open=%.4f" % (
        s["pass"], s["arm"], sites, s["open"], int(s["open"]) / sites, s["written_landmark"], int(s["written_landmark"]) / sites, s["written_other"], int(s["written_other"]) / sites,
        int(s["computed_open"]) + int(s["computed_landmark"]) + int(s["computed_other"]), (int(s["computed_open"]) + int(s["computed_landmark"]) + int(s["computed_other"])) / sites,
        s["pairs"], s["forward_ms"], nats(int(s["code_sum_2^-20_bits"]), int(s["open_places"]))))
by_arm = {}
for s in sections:
    by_arm.setdefault(s["arm"], []).append(s)
p0, p1, p2 = int(by_arm["A0"][0]["pairs"]), int(by_arm["A1"][0]["pairs"]), int(by_arm["A2"][0]["pairs"])
print("PAIRS by the receiving row's kind: open=%d (%.4f) written_landmark=%d (%.4f) written_other=%d (%.4f) of %d" % (p1, p1 / p0, p2 - p1, (p2 - p1) / p0, p0 - p2, (p0 - p2) / p0, p0))
c0 = [int(s["forward_ms"]) for s in by_arm["A0"]]
c2 = [int(s["forward_ms"]) for s in by_arm["A2"]]
rows0 = sum(int(by_arm["A0"][0][k]) for k in ("computed_open", "computed_landmark", "computed_other"))
rows2 = sum(int(by_arm["A2"][0][k]) for k in ("computed_open", "computed_landmark", "computed_other"))
print("UNDER_A2 rows=%.4f of A0's pairs=%.4f forward=%.4f (A2 %s ms against A0 %s ms; the controls' spread %.4f)" % (rows2 / rows0, p2 / p0, (sum(c2) / len(c2)) / (sum(c0) / len(c0)), "/".join(map(str, c2)), "/".join(map(str, c0)), abs(c0[0] - c0[-1]) / (sum(c0) / len(c0))))
# A0 against the line's own read.
line = {}
for i, l in enumerate(open(line_tsv)):
    w = l.rstrip("\n").split("\t")
    if i == 0:
        head = w
        continue
    d = dict(zip(head, w))
    if d["row"] in ("P", "W"):
        line[(d["row"], d["slice"], d["stretch"], d["t"])] = (d["class"], d["cK"])
equal = differ = missing = 0
for i, l in enumerate(open(a0_tsv)):
    if i == 0:
        continue
    row, sl, k, t, cls, ck = l.rstrip("\n").split("\t")
    got = line.get((row, sl, k, t))
    if got is None:
        missing += 1
    elif got == (cls, ck):
        equal += 1
    else:
        differ += 1
print("A0_AGAINST_LINE places_equal=%d differ=%d missing=%d (the line's read of the same state, read-cavity's cK)" % (equal, differ, missing))
