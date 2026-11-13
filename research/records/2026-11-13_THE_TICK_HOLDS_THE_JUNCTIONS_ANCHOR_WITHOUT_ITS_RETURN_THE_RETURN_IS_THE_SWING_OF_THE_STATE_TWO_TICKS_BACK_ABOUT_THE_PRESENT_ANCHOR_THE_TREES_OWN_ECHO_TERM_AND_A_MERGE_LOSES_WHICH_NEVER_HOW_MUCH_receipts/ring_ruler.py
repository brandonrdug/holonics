"""A ruler (host, floats lawful): the free ring on the host, from read-ring's ring.tsv (G162).

Codes on 2^-20 bits are read as nats a place. Prints, pooled over slices: the code and the expected code by stage, the charts' change norm
(sqrt of the mean squared change a place) and the successive-change cosine sum<dr_k, dr_k-1>/sqrt(|dr_k|^2 |dr_k-1|^2); the stage of the least
code; and the mean cosine over stages 8 to 16. Usage: python3 -I ring_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict

NATS = math.log(2) / 2**20


def main(outs):
    for out in outs:
        acc = defaultdict(lambda: [0, 0, 0, 0, 0])
        with open(os.path.join(out, "ring.tsv")) as f:
            next(f)
            for row in f:
                s, k, pl, code, exp, norm, inner = (int(x) for x in row.split("\t"))
                a = acc[k]
                for i, v in enumerate((pl, code, exp, norm, inner)):
                    a[i] += v
        stages = sorted(acc)
        codes = {k: acc[k][1] / acc[k][0] * NATS for k in stages}
        exps = {k: acc[k][2] / acc[k][0] * NATS for k in stages}
        cos = {}
        for k in stages:
            if k - 1 in acc and acc[k][3] and acc[k - 1][3] and acc[k][4]:
                cos[k] = acc[k][4] / math.sqrt(acc[k][3] * acc[k - 1][3])
        least = min(stages, key=lambda k: codes[k])
        tail = [cos[k] for k in range(8, 17) if k in cos]
        print(f"RING {out} places={acc[stages[0]][0]} least_stage={least} least_code={codes[least]:.4f} mean_cos_8_16={sum(tail) / len(tail) if tail else float('nan'):.4f}")
        print("  code " + " ".join(f"s{k}={codes[k]:.4f}" for k in stages))
        print("  expected " + " ".join(f"s{k}={exps[k]:.4f}" for k in stages))
        print("  change " + " ".join(f"s{k}={math.sqrt(acc[k][3] / acc[k][0]):.1f}" for k in stages if acc[k][3]))
        print("  cosine " + " ".join(f"s{k}={cos[k]:.3f}" for k in sorted(cos)))


if __name__ == "__main__":
    main(sys.argv[1:])
