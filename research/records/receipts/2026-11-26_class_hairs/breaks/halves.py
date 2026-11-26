"""The fade covector against the count of breaks (G-C1): dense less sparse half, a place, by slice and ring, over the sections read.

python3 -I halves.py slice_fades_breaks_W121.txt   (host floats, a ruler's)
"""
import sys, re, statistics as st

rows, agg = {}, {}
for l in open(sys.argv[1]):
    if not l.startswith('SLICE_FADES_HALF') or 'kind=fade' not in l:
        continue
    f = dict(re.findall(r'(\w+)=(\S+)', l))
    sums = {int(a): int(b) for a, b in re.findall(r' (\d+):(-?\d+)', l)}
    rows[(int(f['section']), f['slice'], f['half'])] = (int(f['sites']), int(f['breaks']), sums)
    a = agg.setdefault((f['slice'], f['half']), [0, 0, 0])
    a[0] += int(f['regions']); a[1] += int(f['sites']); a[2] += int(f['breaks'])
slices = sorted({k[1] for k in rows})
sections = sorted({k[0] for k in rows})
for s in slices:
    sp, de = agg[(s, 'sparse')], agg[(s, 'dense')]
    print(f"HALVES slice={s} sparse_breaks_a_place={sp[2]/sp[1]:.4f} dense_breaks_a_place={de[2]/de[1]:.4f} sparse_places_a_region={sp[1]/sp[0]:.1f} dense_places_a_region={de[1]/de[0]:.1f}")
for ring in sorted(next(iter(rows.values()))[2]):
    for s in slices:
        d = [(rows[(k, s, 'dense')][2][ring] / rows[(k, s, 'dense')][0] - rows[(k, s, 'sparse')][2][ring] / rows[(k, s, 'sparse')][0]) / 1e6 for k in sections if (k, s, 'dense') in rows and (k, s, 'sparse') in rows]
        if len(d) > 1:
            m, se = st.mean(d), st.stdev(d) / len(d) ** 0.5
            print(f"DENSE_LESS_SPARSE ring={ring} slice={s} sections={len(d)} mean={m:+.2f} se={se:.2f} over_2se={int(abs(m) > 2 * se)}")
