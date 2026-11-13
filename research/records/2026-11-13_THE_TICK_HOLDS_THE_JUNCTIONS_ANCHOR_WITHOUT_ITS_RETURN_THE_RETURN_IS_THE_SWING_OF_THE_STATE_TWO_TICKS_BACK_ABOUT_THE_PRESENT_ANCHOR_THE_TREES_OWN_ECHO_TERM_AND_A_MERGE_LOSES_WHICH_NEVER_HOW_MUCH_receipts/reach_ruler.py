"""A ruler (host, floats lawful): a turned head's reach on its own clock at its founding, from read-reach's reach.tsv (G157).

Each line holds a slice, mask, tick, head and kind of receiver with the receiver rows' sums of r_w = d(code)/dw and r_u = d(code)/du (the
reverse's grain), their magnitudes and their squares released 32 bits. Prints, pooled over slices and ticks and then by tick, by mask, head and
kind of receiver: the sum's sign (falls: the code falls as the part rises), the coherence |sum|/sum|.|, and its ratio to the random-sign level
sqrt(2/pi) sqrt(sum r^2)/sum|r| over rows. Usage: python3 -I reach_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict


def level(sq, mag):
    return math.sqrt(2 / math.pi) * math.sqrt(sq) * 2**32 / mag if mag else float("nan")


def main(outs):
    for out in outs:
        acc = defaultdict(lambda: [0, 0, 0, 0, 0, 0, 0])
        with open(os.path.join(out, "reach.tsv")) as f:
            next(f)
            for row in f:
                s, m, k, h, w, rows, a, aa, asq, u, ua, usq = (int(x) for x in row.split("\t"))
                for key in ((m, h, w, None), (m, h, w, k)):
                    c = acc[key]
                    for i, v in enumerate((rows, a, aa, asq, u, ua, usq)):
                        c[i] += v
        print(f"READ {out}")
        for key in sorted(acc, key=lambda q: (q[0], q[1], q[2], -1 if q[3] is None else q[3])):
            m, h, w, k = key
            rows, a, aa, asq, u, ua, usq = acc[key]
            tick = "all" if k is None else str(k)
            cw, cu = abs(a) / aa if aa else 0.0, abs(u) / ua if ua else 0.0
            lw, lu = level(asq, aa), level(usq, ua)
            print(f"  REACH mask={m} head={h} rows={'written' if w else 'open'} tick={tick} n={rows} | w: {'falls' if a < 0 else 'rises'} coherence={cw:.4f} ratio={cw / lw:.2f} | u: {'falls' if u < 0 else 'rises'} coherence={cu:.4f} ratio={cu / lu:.2f}")


if __name__ == "__main__":
    main(sys.argv[1:])
