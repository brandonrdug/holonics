#!/usr/bin/env python3
"""The reach read's rule (§16.45, fixed by the unified-theory reading before the read), from reach-field's REACH.tsv.

Usage: rule.py OLD_DIR,OLD_DIR,OLD_DIR LAW_DIR,LAW_DIR,LAW_DIR

Reach only when all three hold, each by more than the larger of the two laws' spreads (largest less smallest) over
their three states:
1. the free clock's mean duration per answer place at the last tick is above 1 on at least one paced head;
2. with the answer places split at the median place index over all problems, the free clock's code excess over the old
   law is larger on the far half than on the near half;
3. on the far half, the question's information (code beside the next problem's question less beside its own) is below
   the old law's.
A check, not a bar: binned by variation distance (on each paced head), the two laws' question information. Codes on
2^-20 bits, clocks on 2^-24.
"""
import csv
import statistics
import sys

ONE = 1 << 24
CODE = 1 << 20


def load(d):
    with open(f"{d}/REACH.tsv") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def mean(xs):
    return sum(xs) / len(xs)


def spread(xs):
    return max(xs) - min(xs)


def main():
    old = [load(d) for d in sys.argv[1].split(",")]
    law = [load(d) for d in sys.argv[2].split(",")]
    heads = sorted(int(k[5:]) for k in old[0][0] if k.startswith("kappa"))
    median = statistics.median(int(r["place"]) for r in old[0])
    print(f"places a state: old {[len(s) for s in old]} law {[len(s) for s in law]}; median place {median}")

    def halves(state):
        near = [r for r in state if int(r["place"]) < median]
        far = [r for r in state if int(r["place"]) >= median]
        return near, far

    def own(rows):
        return mean([int(r["code_own"]) for r in rows]) / CODE

    def question(rows):
        return mean([int(r["code_foil"]) - int(r["code_own"]) for r in rows]) / CODE

    # 1. The stretch.
    ok1 = False
    for h in heads:
        ks = [mean([int(r[f"kappa{h}"]) for r in s]) / ONE for s in law]
        ko = [mean([int(r[f"kappa{h}"]) for r in s]) / ONE for s in old]
        bar = max(spread(ks), spread(ko))
        held = mean(ks) - 1 > bar
        ok1 = ok1 or held
        print(f"1. head {h}: law duration {mean(ks):.4f} by state {[round(k, 4) for k in ks]}; old {mean(ko):.4f}; over 1 by {mean(ks) - 1:+.4f} against spread {bar:.4f}: {'holds' if held else 'fails'}")
    # 2. The excess is far.
    fn = {name: [own(halves(s)[1]) - own(halves(s)[0]) for s in sets] for name, sets in (("old", old), ("law", law))}
    near = {name: [own(halves(s)[0]) for s in sets] for name, sets in (("old", old), ("law", law))}
    far = {name: [own(halves(s)[1]) for s in sets] for name, sets in (("old", old), ("law", law))}
    excess_near, excess_far = mean(near["law"]) - mean(near["old"]), mean(far["law"]) - mean(far["old"])
    bar = max(spread(fn["old"]), spread(fn["law"]))
    ok2 = excess_far - excess_near > bar
    print(f"2. own code near/far: old {mean(near['old']):.3f}/{mean(far['old']):.3f}, law {mean(near['law']):.3f}/{mean(far['law']):.3f}; excess near {excess_near:+.3f}, far {excess_far:+.3f}; far less near {excess_far - excess_near:+.3f} against spread {bar:.3f}: {'holds' if ok2 else 'fails'}")
    # 3. The question is what is lost there.
    qf = {name: [question(halves(s)[1]) for s in sets] for name, sets in (("old", old), ("law", law))}
    qn = {name: [question(halves(s)[0]) for s in sets] for name, sets in (("old", old), ("law", law))}
    bar = max(spread(qf["old"]), spread(qf["law"]))
    ok3 = mean(qf["old"]) - mean(qf["law"]) > bar
    print(f"3. question information far: old {mean(qf['old']):.4f} {[round(q, 4) for q in qf['old']]}, law {mean(qf['law']):.4f} {[round(q, 4) for q in qf['law']]}; old less law {mean(qf['old']) - mean(qf['law']):+.4f} against spread {bar:.4f}: {'holds' if ok3 else 'fails'} (near: old {mean(qn['old']):.4f}, law {mean(qn['law']):.4f})")
    print(f"REACH_RULE {'reach' if ok1 and ok2 and ok3 else 'not reach'} (1 {ok1}, 2 {ok2}, 3 {ok3})")
    # The check: question information by variation distance on doubling spans.
    for h in heads:
        print(f"check, head {h}: variation from the question (bare places) -> question bits, old | law")
        tables = {}
        for name, sets in (("old", old), ("law", law)):
            t = {}
            for s in sets:
                for r in s:
                    v = int(r[f"variation{h}"]) / ONE
                    b = int(v).bit_length()
                    t.setdefault(b, []).append(int(r["code_foil"]) - int(r["code_own"]))
            tables[name] = t
        for b in sorted(set(tables["old"]) | set(tables["law"])):
            cells = []
            for name in ("old", "law"):
                xs = tables[name].get(b)
                cells.append(f"{mean(xs) / CODE:.4f} ({len(xs)})" if xs else "-")
            print(f"  [{0 if b == 0 else 1 << (b - 1)}, {1 << b})\t{cells[0]}\t{cells[1]}")


if __name__ == "__main__":
    main()
