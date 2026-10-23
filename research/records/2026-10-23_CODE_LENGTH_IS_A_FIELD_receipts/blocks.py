# Expansion and contraction per partition: node bits a byte per fine role and region in 20 blocks of problems.
# usage: python3 -I blocks.py field.json
import json, sys, numpy as np
r = json.load(open(sys.argv[1]))
g = r["blocks"]["grid"]
print("node bits a byte per block of about 336 problems: blocks 1, 5, 10, 20; last/first; slope per block over blocks 11-20; slope per doubling of the block count")
for k, rows in g.items():
    a = np.array(rows, float); rate = a[:, 2] / np.maximum(a[:, 0], 1); x = np.arange(20)
    print("%-36s %8d B  %.3f %.3f %.3f %.3f | %.3f | %+.4f | %+.3f" % (k, int(a[:, 0].sum()), rate[0], rate[4], rate[9], rate[19],
          rate[19] / rate[0], np.polyfit(x[10:], rate[10:], 1)[0], np.polyfit(np.log2(x + 1), rate, 1)[0]))
print("region shares at blocks 1, 6, 11, 16:", {k: ["%.3f" % v for v in vs[::5]] for k, vs in r["share_by_block"].items()})
