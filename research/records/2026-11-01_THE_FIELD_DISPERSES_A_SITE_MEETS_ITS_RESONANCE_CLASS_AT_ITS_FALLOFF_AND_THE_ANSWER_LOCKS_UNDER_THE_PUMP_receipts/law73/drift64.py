#!/usr/bin/env python3
"""The writer's drift to its read 64 on the same keys (§16.47, the unified-theory reading of November 5, 13:26), from
length-field's LENGTH.tsv and ENDS.tsv read with READS 64 and one KEY.

Usage: drift64.py NAME=DIR ...

For each state: the mean over problems of L at read 0 and at read 64 less the held length, and of the drift L(64) - L(0),
with its standard error; then each later state's drift less the first's, paired problem by problem (the same keys, so the
same draws wherever the faces agree), with its standard error. Lengths on 2^-20 places. Reading only; nothing here is a text.
"""
import csv
import statistics
import sys

UNIT = 1 << 20


def read(d):
    l = {}
    with open(f"{d}/LENGTH.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            if r["read"] in ("0", "64"):
                l.setdefault(int(r["problem"]), {})[int(r["read"])] = int(r["length"]) / UNIT
    with open(f"{d}/ENDS.tsv") as f:
        held = {int(r["problem"]): int(r["held"]) for r in csv.DictReader(f, delimiter="\t")}
    return {k: (v[0] - held[k], v[64] - held[k]) for k, v in l.items() if 0 in v and 64 in v}


def se(xs):
    return statistics.stdev(xs) / len(xs) ** 0.5


def main():
    states = [a.split("=", 1) for a in sys.argv[1:]]
    got = {name: read(d) for name, d in states}
    print("state\tproblems\tL(0) less held\tL(64) less held\tdrift\tse")
    for name, _ in states:
        g = got[name]
        drift = [b - a for a, b in g.values()]
        print(f"{name}\t{len(g)}\t{statistics.mean(a for a, _ in g.values()):+.1f}\t{statistics.mean(b for _, b in g.values()):+.1f}\t{statistics.mean(drift):+.1f}\t{se(drift):.1f}")
    base = states[0][0]
    for name, _ in states[1:]:
        ks = sorted(set(got[base]) & set(got[name]))
        diff = [(got[name][k][1] - got[name][k][0]) - (got[base][k][1] - got[base][k][0]) for k in ks]
        print(f"{name} less {base}: drift {statistics.mean(diff):+.1f}, se {se(diff):.1f} (paired, {len(ks)} problems)")
    if len(states) > 2:
        a, b = states[1][0], states[2][0]
        ks = sorted(set(got[a]) & set(got[b]))
        diff = [(got[b][k][1] - got[b][k][0]) - (got[a][k][1] - got[a][k][0]) for k in ks]
        print(f"{b} less {a}: drift {statistics.mean(diff):+.1f}, se {se(diff):.1f} (paired, {len(ks)} problems)")


if __name__ == "__main__":
    main()
