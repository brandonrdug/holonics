"""A ruler (host, floats lawful): the reader's reaction on its source at its founding, from read-reaction's reaction.tsv (G158).

Each line holds a slice, mask, tick, head and kind of reader with the written sources' sums of a_j = <lambda_j, rho_j> (the reverse's grain),
their magnitudes, their squares released 32 bits, and sum|rho|^2 and sum|x|^2 (entries released 8 bits). d(code)/dkappa_h = -sum a. Prints by
mask and head, the readers' kinds pooled and apart, over the ticks: the sign (falls: the code falls as kappa rises, sum a > 0), the coherence
|sum|/sum|.|, its ratio to the random-sign level sqrt(2/pi) sqrt(sum a^2)/sum|a| over sources, and m^2 = sum|rho|^2/sum|x|^2. Then by tick.
Usage: python3 -I reaction_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict


def main(outs):
    for out in outs:
        acc = defaultdict(lambda: [0, 0, 0, 0, 0, 0])
        with open(os.path.join(out, "reaction.tsv")) as f:
            next(f)
            for row in f:
                s, m, k, h, w, rows, a, aa, asq, rsq, xsq = (int(x) for x in row.split("\t"))
                for key in ((m, h, None, None), (m, h, w, None), (m, h, None, k)):
                    c = acc[key]
                    for i, v in enumerate((rows, a, aa, asq, rsq, xsq)):
                        c[i] += v
        print(f"READ {out}")
        for key in sorted(acc, key=lambda q: (q[0], q[1], -1 if q[2] is None else q[2], -1 if q[3] is None else q[3])):
            m, h, w, k = key
            rows, a, aa, asq, rsq, xsq = acc[key]
            if aa == 0:
                continue
            coh = abs(a) / aa
            lev = math.sqrt(2 / math.pi) * math.sqrt(asq) * 2**32 / aa
            kind = "both" if w is None else ("written" if w else "open")
            tick = "all" if k is None else str(k)
            m2 = rsq / xsq if xsq else float("nan")
            print(f"  REACTION mask={m} head={h} readers={kind} tick={tick} sources={rows} | {'falls' if a > 0 else 'rises'} coherence={coh:.4f} ratio={coh / lev:.2f} m2={m2:.3e}")


if __name__ == "__main__":
    main(sys.argv[1:])
