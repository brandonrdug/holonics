#!/usr/bin/env python3
"""Score G57 from the two extracts of `tools/state_travel.py rank 32`.

    python3 travel_rank_score.py travel_rank_growth_extract.txt travel_rank_rate_extract.txt

Host arithmetic on the printed lines only. For each line it prints the charge of
W's new columns (their rms over the old columns'), the cosine of each lap's travel
of W with the form it started from (from the rms before, after and of the travel:
|x+d|^2 = |x|^2 + 2<x,d> + |d|^2 over the same entries), and for each pair of laps
the cosine with f1 and f4 over it.
"""
import sys


def fields(line):
    out = {}
    for tok in line.split()[1:]:
        if "=" in tok:
            k, v = tok.split("=", 1)
            out[k] = v
        else:
            out["family"] = tok
    return out


def read(path):
    form, lap, pair = {}, {}, {}
    for line in open(path):
        if line.startswith("FORM"):
            f = fields(line)
            form[(f["family"], f["contacts"], int(f["state"]))] = float(f["rms"])
        elif line.startswith("LAP"):
            f = fields(line)
            lap[(f["family"], f["contacts"], int(f["lap"]))] = float(f["rms"])
        elif line.startswith("TRAVEL_PAIR"):
            f = fields(line)
            k = int(f["laps"].split(",")[0])
            pair[(f["family"], f["contacts"], k)] = tuple(float(f[x]) for x in ("cos", "f1", "f4"))
    return form, lap, pair


def main():
    for path in sys.argv[1:]:
        form, lap, pair = read(path)
        states = sorted({s for (_, _, s) in form})
        print(f"== {path}")
        print("charge (W new rms over old), by state:",
              " ".join(f"{form[('w','new',s)]/form[('w','old',s)]:.4f}" for s in states))
        for sub in ("new", "old"):
            cs = []
            for s in states[:-1]:
                x0, x1, d = form[("w", sub, s)], form[("w", sub, s + 1)], lap[("w", sub, s)]
                cs.append((x1 * x1 - x0 * x0 - d * d) / (2 * x0 * d) if x0 > 0 else float("nan"))
            print(f"cos(lap travel of W {sub}, the form it left):", " ".join(f"{c:+.3f}" for c in cs))
        for fam in ("w", "a", "b"):
            for sub in ("new", "old"):
                ks = sorted(k for (f, c, k) in pair if f == fam and c == sub)
                cos = [pair[(fam, sub, k)][0] for k in ks]
                f1 = [pair[(fam, sub, k)][1] for k in ks]
                f4 = [pair[(fam, sub, k)][2] for k in ks]
                n = len(ks)
                line = f"{fam} {sub}: cos mean {sum(cos)/n:+.4f} min {min(cos):+.4f} max {max(cos):+.4f}; f1 mean {sum(f1)/n:.4f}; f4 mean {sum(f4)/n:.4f} max {max(f4):.4f}"
                if min(cos) > 0.3:
                    line += "; f1/cos " + " ".join(f"{a/c:.3f}" for a, c in zip(f1, cos))
                    line += "; f4/cos " + " ".join(f"{a/c:.3f}" for a, c in zip(f4, cos))
                print(line)


if __name__ == "__main__":
    main()
