#!/usr/bin/env python3
"""The question's reach into a blank answer (§16.45), from reach-field's REACH.tsv files.

Usage: reach.py LABEL=DIR[,DIR...] LABEL=DIR[,DIR...] ...

Each LABEL's directories (one state each) are pooled. By place from the question on doubling spans [0,1), [1,2),
[2,4), ... it prints, for each label, the truth's code beside its own question and the question's effect (foil less
own), both in bits a class, and each paced head's mean duration and mean variation from the question (in units of the
bare rate). With two or more labels it prints each later label's excess over the first (own code less the first's) and
its question effect less the first's. Reading only; the codes are on 2^-20 bits, the clocks on 2^-24.
"""
import csv
import sys

ONE = 1 << 24
CODE = 1 << 20


def load(dirs):
    rows = []
    for d in dirs:
        with open(f"{d}/REACH.tsv") as f:
            rows.extend(csv.DictReader(f, delimiter="\t"))
    return rows


def span(j):
    return j.bit_length()


def table(rows):
    heads = sorted({int(k[5:]) for k in rows[0] if k.startswith("kappa")}) if rows else []
    out = {}
    for r in rows:
        s = span(int(r["place"]))
        b = out.setdefault(s, {"n": 0, "own": 0, "foil": 0, "kappa": [0] * len(heads), "var": [0] * len(heads)})
        b["n"] += 1
        b["own"] += int(r["code_own"])
        b["foil"] += int(r["code_foil"])
        for i, h in enumerate(heads):
            b["kappa"][i] += int(r[f"kappa{h}"])
            b["var"][i] += int(r[f"variation{h}"])
    return heads, out


def main():
    sets = []
    for arg in sys.argv[1:]:
        label, dirs = arg.split("=", 1)
        sets.append((label, *table(load(dirs.split(",")))))
    spans = sorted({s for _, _, t in sets for s in t})
    for label, heads, t in sets:
        print(f"== {label}")
        print("from\tplaces\town_bits\tquestion_bits\t" + "\t".join(f"kappa{h}\tvar{h}" for h in heads))
        for s in spans:
            if s not in t:
                continue
            b = t[s]
            n = b["n"]
            cells = "\t".join(f"{b['kappa'][i] / n / ONE:.3f}\t{b['var'][i] / n / ONE:.1f}" for i in range(len(heads)))
            print(f"{0 if s == 0 else 1 << (s - 1)}\t{n}\t{b['own'] / n / CODE:.3f}\t{(b['foil'] - b['own']) / n / CODE:.3f}\t{cells}")
        n = sum(b["n"] for b in t.values())
        print(f"all\t{n}\t{sum(b['own'] for b in t.values()) / n / CODE:.3f}\t{sum(b['foil'] - b['own'] for b in t.values()) / n / CODE:.3f}")
    base_label, _, base = sets[0]
    for label, _, t in sets[1:]:
        print(f"== {label} less {base_label}")
        print("from\texcess_bits\tquestion_less_bits")
        for s in spans:
            if s in t and s in base:
                a, b = t[s], base[s]
                print(f"{0 if s == 0 else 1 << (s - 1)}\t{a['own'] / a['n'] / CODE - b['own'] / b['n'] / CODE:+.3f}\t{(a['foil'] - a['own']) / a['n'] / CODE - (b['foil'] - b['own']) / b['n'] / CODE:+.3f}")


if __name__ == "__main__":
    main()
