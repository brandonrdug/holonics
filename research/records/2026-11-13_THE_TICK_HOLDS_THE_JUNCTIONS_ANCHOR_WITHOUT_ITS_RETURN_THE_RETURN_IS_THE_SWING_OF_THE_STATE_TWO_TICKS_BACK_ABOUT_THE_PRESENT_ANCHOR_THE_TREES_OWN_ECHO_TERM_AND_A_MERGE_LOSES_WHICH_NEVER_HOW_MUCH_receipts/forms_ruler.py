"""A ruler (host, floats lawful): the reader's reaction's forms at its founding, from read-reaction-forms' forms.tsv and charts.tsv (G159).

Prints by mask and head over the ticks and slices: the share of written sources where the pair decomposition's a_j agrees in sign with the
route's; the median and upper quartile over coordinates of |sum|/sum|.| for the source's chart (sum_j a_j r_j) and the reader's (sum_i b_i r_i);
and the metric-raised strength's sign (falls: the code falls as s rises) with its coherence and ratio to the random-sign level, beside the
route's raw sum's sign. Usage: python3 -I forms_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict


def main(outs):
    for out in outs:
        f = defaultdict(lambda: [0] * 8)
        with open(os.path.join(out, "forms.tsv")) as fh:
            next(fh)
            for row in fh:
                s, m, k, h, src, rdr, route, pair, agree, w, wa, wsq = (int(x) for x in row.split("\t"))
                a = f[(m, h)]
                for i, v in enumerate((src, rdr, route, pair, agree, w, wa, wsq)):
                    a[i] += v
        c = defaultdict(lambda: [0, 0])
        with open(os.path.join(out, "charts.tsv")) as fh:
            next(fh)
            for row in fh:
                s, m, k, h, chart, i, sm, mag = (int(x) for x in row.split("\t"))
                a = c[(m, h, chart, i)]
                a[0] += sm
                a[1] += mag
        print(f"READ {out}")
        for (m, h) in sorted(f):
            src, rdr, route, pair, agree, w, wa, wsq = f[(m, h)]
            def coh(chart):
                v = sorted(abs(c[(m, h, chart, i)][0]) / c[(m, h, chart, i)][1] for i in range(64) if c[(m, h, chart, i)][1])
                return (v[len(v) // 2], v[3 * len(v) // 4]) if v else (float("nan"), float("nan"))
            sc, rc = coh(0), coh(1)
            wc = abs(w) / wa if wa else 0.0
            wl = math.sqrt(2 / math.pi) * math.sqrt(wsq) * 2**8 / wa if wa else float("nan")
            print(f"  FORMS mask={m} head={h} sources={src} agree={agree / src:.3f} | source_chart median={sc[0]:.4f} q75={sc[1]:.4f} | reader_chart median={rc[0]:.4f} q75={rc[1]:.4f} | raw {'falls' if route > 0 else 'rises'} | metric {'falls' if w > 0 else 'rises'} coherence={wc:.4f} ratio={(wc / wl) if wl else float("nan"):.2f}")


if __name__ == "__main__":
    main(sys.argv[1:])
