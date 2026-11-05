#!/usr/bin/env python3
"""The answer's expected length along the writer's path (§16.47), from length-field's LENGTH.tsv and ENDS.tsv.

Usage: length.py DIR

L at a read is the places resolved as letters plus the sum of (1 - void mass) over the open places, the field's own
expected length at that state; at the release's end it is the written length. Printed: L less the held length by read
(sweeps 0, 1, 2, 4, ..., the last sweep, each refine pass's first read, the end); each problem's drift split at its first
void (L at the read that first meets a void, less L at the opening; then the written length less that); the refine passes'
share; and the rule fixed before the read (the unified-theory reading of November 5, 09:45). Lengths on 2^-20 places.
Reading only; nothing here is a text.
"""
import csv
import statistics
import sys

UNIT = 1 << 20


def main():
    d = sys.argv[1]
    by = {}
    passes = {}
    with open(f"{d}/LENGTH.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            k, read = int(r["problem"]), int(r["read"])
            by.setdefault(k, {})[read] = int(r["length"]) / UNIT
            passes.setdefault(int(r["pass"]), set()).add(read)
    ends = {}
    with open(f"{d}/ENDS.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            ends[int(r["problem"])] = r
    held = {k: int(e["held"]) for k, e in ends.items()}
    written = {k: int(e["written"]) for k, e in ends.items()}
    sweeps = max(passes[0])
    marks = [0] + [1 << i for i in range(0, 11) if (1 << i) < sweeps] + [sweeps]
    for p in sorted(passes):
        if p > 0:
            marks.append(min(passes[p]))
    marks = sorted(set(m for m in marks if all(m in by[k] for k in by)))
    print("read\tpass\tmean L less held\tmedian")
    for m in marks:
        xs = [by[k][m] - held[k] for k in by]
        p = next(p for p in passes if m in passes[p])
        print(f"{m}\t{p}\t{statistics.mean(xs):+.1f}\t{statistics.median(xs):+.1f}")
    final = max(max(r) for r in by.values())
    print(f"end ({final})\t-\t{statistics.mean(written[k] - held[k] for k in by):+.1f}\t{statistics.median(written[k] - held[k] for k in by):+.1f}")
    pre, post, refine_drift, total = [], [], [], []
    for k in by:
        open_l = by[k][0]
        fv = ends[k]["first_void_read"]
        fv_l = by[k][int(fv)] if fv != "-" and int(fv) in by[k] else written[k]
        after_sweeps = by[k].get(sweeps, written[k])
        pre.append(fv_l - open_l)
        post.append(written[k] - fv_l)
        refine_drift.append(written[k] - after_sweeps)
        total.append(written[k] - open_l)
    t = statistics.mean(total)
    print(f"opening L less held: mean {statistics.mean(by[k][0] - held[k] for k in by):+.1f}")
    print(f"drift from the opening to the end: mean {t:+.1f} a problem")
    print(f"  to the first void: mean {statistics.mean(pre):+.1f} ({statistics.mean(pre) / t:.0%} of it); after it: {statistics.mean(post):+.1f} ({statistics.mean(post) / t:.0%})")
    print(f"  in the refine passes: mean {statistics.mean(refine_drift):+.1f}")
    shorts = [k for k in by if written[k] < held[k]]
    if shorts:
        sr = [written[k] - by[k].get(sweeps, written[k]) for k in shorts]
        ss = [by[k].get(sweeps, written[k]) - held[k] for k in shorts]
        print(f"short answers ({len(shorts)}): after the sweeps L less held {statistics.mean(ss):+.1f}, the refine passes moved them {statistics.mean(sr):+.1f}")
    fvs = [int(ends[k]["first_void_read"]) for k in by if ends[k]["first_void_read"] != "-"]
    print(f"first void read: median {statistics.median(fvs):.0f} of {sweeps} sweeps; last letter's read: median {statistics.median(int(ends[k]['last_letter_read']) for k in by if ends[k]['last_letter_read'] != '-'):.0f}")
    pre_ok = statistics.mean(pre) >= t / 2
    post_ok = abs(statistics.mean(post)) < abs(t) / 4
    print(f"RULE: pre-void at least half {pre_ok}; post-void under a quarter {post_ok}")
    print("problem\theld\twritten_less_held\topening_L_less_held\tL_at_first_void_less_held\tafter_sweeps_less_held\tfirst_void_read\tfirst_void_place\tlast_letter_place\tlast_letter_read")
    for k in sorted(by):
        e = ends[k]
        fv = e["first_void_read"]
        fv_l = by[k][int(fv)] if fv != "-" and int(fv) in by[k] else written[k]
        print(f"{k}\t{held[k]}\t{written[k] - held[k]:+d}\t{by[k][0] - held[k]:+.0f}\t{fv_l - held[k]:+.0f}\t{by[k].get(sweeps, written[k]) - held[k]:+.0f}\t{fv}\t{e['first_void_place']}\t{e['last_letter_place']}\t{e['last_letter_read']}")


if __name__ == "__main__":
    main()
