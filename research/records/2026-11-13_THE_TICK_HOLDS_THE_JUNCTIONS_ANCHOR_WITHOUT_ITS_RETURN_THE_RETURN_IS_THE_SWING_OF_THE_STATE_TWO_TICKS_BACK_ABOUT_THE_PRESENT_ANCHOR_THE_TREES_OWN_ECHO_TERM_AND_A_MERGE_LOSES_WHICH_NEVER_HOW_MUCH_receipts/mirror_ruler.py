"""A ruler (host, floats lawful): the read's mirror at its founding, from read-mirror's mirror.tsv and chart.tsv (G160).

The stage x_j <- x_j - s_h mu_j moves the code by -s_h sum_j a_j 2^-40 bits (the covector's grain against the state's), so
d(code)/ds_h = -sum a ln 2 2^-40 nats, read over the region's open places. Prints by mask, head and kind of reader (open, written, both) over
the ticks: d(code)/ds in nats a place per unit of s (positive: the code rises with s, so the deposit asks for s < 0, agreement), the coherence
|sum|/sum|.| and its ratio to the random-sign level over sources; with both kinds, the source's ray's coordinates' median and upper-quartile
coherence, the mean audience and the lanes' power spread (the standard deviation of log2 of a lane's power). Then by tick.
Usage: python3 -I mirror_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict

KINDS = ["open", "written", "both"]


def main(outs):
    for out in outs:
        acc = defaultdict(lambda: [0] * 8)
        places = {}
        with open(os.path.join(out, "mirror.tsv")) as f:
            next(f)
            for row in f:
                s, m, k, h, w, pl, src, a, aa, asq, aud, pw, pwsq, ln = (int(x) for x in row.split("\t"))
                places[(s, m)] = pl
                for key in ((m, h, w, None), (m, h, w, k)):
                    c = acc[key]
                    for i, v in enumerate((src, a, aa, asq, aud, pw, pwsq, ln)):
                        c[i] += v
        open_places = defaultdict(int)
        for (s, m), pl in places.items():
            open_places[m] += pl
        ch = defaultdict(lambda: [0, 0])
        with open(os.path.join(out, "chart.tsv")) as f:
            next(f)
            for row in f:
                s, m, k, h, i, sm, mag = (int(x) for x in row.split("\t"))
                c = ch[(m, h, i)]
                c[0] += sm
                c[1] += mag
        print(f"READ {out}")
        for key in sorted(acc, key=lambda q: (q[0], q[1], q[2], -1 if q[3] is None else q[3])):
            m, h, w, k = key
            src, a, aa, asq, aud, pw, pwsq, ln = acc[key]
            if aa == 0:
                continue
            slope = -a * math.log(2) / 2**40 / open_places[m]
            coh = abs(a) / aa
            lev = math.sqrt(2 / math.pi) * math.sqrt(asq) * 2**32 / aa
            line = f"  MIRROR mask={m} head={h} readers={KINDS[w]} tick={'all' if k is None else k} sources={src} | dcode_ds={slope:+.5f} nats a place | coherence={coh:.4f} ratio={coh / lev:.2f}"
            if w == 2 and k is None:
                v = sorted(abs(ch[(m, h, i)][0]) / ch[(m, h, i)][1] for i in range(64) if ch[(m, h, i)][1])
                mean_log = pw / ln / 2**16
                sd = math.sqrt(max(0.0, pwsq / ln / 2**32 - mean_log**2))
                line += f" | ray_chart median={v[len(v) // 2]:.4f} q75={v[3 * len(v) // 4]:.4f} | audience_mean={aud / src / 2**31:.3f} | log2_power mean={mean_log:.2f} sd={sd:.2f}"
            print(line)


if __name__ == "__main__":
    main(sys.argv[1:])
