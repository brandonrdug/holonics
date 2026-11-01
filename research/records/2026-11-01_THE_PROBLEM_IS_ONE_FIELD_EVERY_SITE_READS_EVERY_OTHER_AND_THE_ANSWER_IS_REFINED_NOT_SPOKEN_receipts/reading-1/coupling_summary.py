"""COUPLING.tsv (release-field) folded: means and the distribution of λ, F*, plateaus, the longest plateau."""
import sys, statistics as s
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
cols = ["released", "held", "lambda", "friction", "plateaus", "longest", "lag"]
data = {c: [int(r[i + 1]) for r in rows] for i, c in enumerate(cols)}
print(f"COUPLING problems={len(rows)}")
for c in cols:
    v = sorted(data[c])
    q = lambda p: v[min(len(v) - 1, int(p * len(v)))]
    print(f"  {c}: sum={sum(v)} mean={s.mean(v):.2f} min={v[0]} q25={q(.25)} median={q(.5)} q75={q(.75)} max={v[-1]}")
ratio = [int(r[3]) / max(1, int(r[2])) for r in rows]
print(f"  lambda/held: mean={s.mean(ratio):.3f} median={sorted(ratio)[len(ratio)//2]:.3f}")
