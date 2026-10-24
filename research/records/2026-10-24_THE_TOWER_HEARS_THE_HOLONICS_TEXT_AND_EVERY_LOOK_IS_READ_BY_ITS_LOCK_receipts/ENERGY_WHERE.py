"""Where the input tension's energy sits on the slice: by the cell's place in its 128-cell section,
by class, and how concentrated it is over cells. An exterior reading of read-tower-input-covectors."""
import collections, sys
path, text_path = sys.argv[1], sys.argv[2]
text = open(text_path, 'rb').read()
e = []
for l in open(path):
    p = l.split()
    i = int(p[1]); y = [int(v) for v in p[3:]]
    e.append((i, int(p[2]), sum(v * v for v in y)))
tot = sum(x[2] for x in e)
n = len(e)
print(f"cells={n} energy per cell={tot / n / 2**48:.3f}")
srt = sorted((x[2] for x in e), reverse=True)
for q in (1, 10, 100, 1000, 10000):
    print(f"top {q} cells hold {1000 * sum(srt[:q]) / tot:.1f} per mille")
med = srt[n // 2]
print(f"median cell energy={med / 2**48:.4f}  mean/median={tot / n / med:.1f}")
pos = collections.Counter(); posn = collections.Counter()
for i, u, en in e:
    pos[(i % 128) // 16] += en; posn[(i % 128) // 16] += 1
print("by place in section (16-cell bins): " + " ".join(f"{b * 16}:{1000 * pos[b] / tot:.0f}" for b in range(8)))
byc = collections.Counter(); byn = collections.Counter()
for i, u, en in e:
    byc[u] += en; byn[u] += 1
print("classes by energy share (per mille, cells, energy/cell):")
for u, en in byc.most_common(12):
    print(f"  {bytes([u])!r} {1000 * en / tot:.1f} n={byn[u]} {en / byn[u] / 2**48:.2f}")
print("the 12 largest cells with their context:")
for i, u, en in sorted(e, key=lambda x: -x[2])[:12]:
    ctx = text[max(0, i - 30):i + 1].decode('utf-8', 'replace').replace('\n', '\\n')
    nxt = text[i + 1:i + 12].decode('utf-8', 'replace').replace('\n', '\\n')
    print(f"  cell {i} (place {i % 128}) energy={en / 2**48:.0f} ...{ctx}|{nxt}")  # the receipts keep the cell and energy only
