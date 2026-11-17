"""A ruler: the engine's own level, traced. From a read-level dump (each region's epochs' anchors, each place's news at its cavity face,
each epoch's state after the level's last tick): where her epochs fall and what they span; and what the level's state of an epoch still
holds, read by least squares (fitted on half the regions, read on the other): the epoch's own symbols and its identity as one thing, the
epoch before it, and the symbol that leads the next. Outside the machine; shares and counts only.
Usage: python3 -I level_ruler.py DUMP TRACE_ROWS.tsv"""
import sys, math, collections
import numpy as np
d, table = sys.argv[1], sys.argv[2]
text = {}
for l in open(table, encoding='utf-8'):
    lab, p, r = l.rstrip('\n').split('\t')[:3]; text[lab] = p + r
D1 = int(open(d + '/dims.tsv').read().split('\t')[1])
coarse = np.fromfile(d + '/coarse.i32', dtype=np.int32).reshape(-1, D1).astype(np.float64) / 65536
LN2 = math.log(2); G = float(1 << 20)
ep = []          # (region index, epoch string, previous epoch string or None, the symbol leading the next epoch or None, news nats, complete)
row = 0; sizes = []; newses = []; kinds = collections.Counter(); place_news = []
for ri, l in enumerate(open(d + '/level.tsv', encoding='utf-8')):
    lab, sites, anc, news = l.rstrip('\n').split('\t'); sites = int(sites)
    anc = [int(x) for x in anc.split(',')]; c = [int(x) / G * LN2 for x in news.split(',')]; s = text[lab]
    place_news += c[:-1]
    strs = [s[a:b] for a, b in zip(anc, anc[1:] + [sites])]
    for j, a in enumerate(anc):
        b = anc[j + 1] if j + 1 < len(anc) else sites
        complete = b < sites                     # the region's last epoch holds the open place
        if a > 0:
            ch, pv = s[a], s[a - 1]
            kinds['a space or mark' if not ch.isalpha() else 'the first letter of a word' if not pv.isalpha() else 'inside a word'] += 1
        if complete: sizes.append(b - a); newses.append(sum(c[a:b]))
        ep.append((ri, strs[j], strs[j - 1] if j else None, s[b] if complete else None, complete, row)); row += 1
assert row == len(coarse), (row, len(coarse))
n_reg = ri + 1
print(f"LEVEL regions={n_reg} epochs={row}; a place's news at its cavity face {np.mean(place_news):.3f} nats; a whole epoch is {np.mean(sizes):.2f} places and {np.mean(newses):.2f} nats on average (median {np.median(sizes):.0f} places); the section is {math.log(244):.2f} nats")
tot = sum(kinds.values())
print("LEVEL an epoch's leading place is: " + ', '.join(f"{k} {100 * v / tot:.0f}%" for k, v in kinds.most_common()))
hist = collections.Counter(min(x, 12) for x in sizes)
print("LEVEL whole epochs by size in places: " + ' '.join(f"{k}{'+' if k == 12 else ''}:{100 * hist[k] / len(sizes):.0f}%" for k in sorted(hist)))
rng = np.random.default_rng(17); half = rng.permutation(n_reg)[: n_reg // 2]; infit = np.zeros(n_reg, bool); infit[half] = True
def explained(mask, keys, top):
    idx = [i for i in range(len(ep)) if mask(ep[i])]
    fit = [i for i in idx if infit[ep[i][0]]]; test = [i for i in idx if not infit[ep[i][0]]]
    cc = collections.Counter(keys(ep[i]) for i in fit); cls = {k: j for j, (k, _) in enumerate(cc.most_common(top))}
    def Y(ix):
        y = np.zeros((len(ix), len(cls) + 1))
        for r_, i in enumerate(ix): y[r_, cls.get(keys(ep[i]), len(cls))] = 1.0
        return y
    X = lambda ix: np.hstack([coarse[[ep[i][5] for i in ix]], np.ones((len(ix), 1))])
    Xf, Yf, Xt, Yt = X(fit), Y(fit), X(test), Y(test)
    A = Xf.T @ Xf; A += 1e-3 * np.trace(A) / len(A) * np.eye(len(A)); W = np.linalg.solve(A, Xf.T @ Yf)
    return 1000 * (1 - ((Yt - Xt @ W) ** 2).sum() / ((Yt - Yf.mean(0)) ** 2).sum()), len(test)
whole = lambda e: e[4]
rows = [("the epoch's first symbol", whole, lambda e: e[1][0], 30), ("its second symbol", lambda e: e[4] and len(e[1]) > 1, lambda e: e[1][1], 30),
        ("its third symbol", lambda e: e[4] and len(e[1]) > 2, lambda e: e[1][2], 30), ("its last symbol", whole, lambda e: e[1][-1], 30),
        ("its size in places", whole, lambda e: min(len(e[1]), 12), 12), ("the epoch as one identity", whole, lambda e: e[1], 400),
        ("the epoch before it, as one identity", lambda e: e[4] and e[2] is not None, lambda e: e[2], 400),
        ("the last symbol of the epoch before it", lambda e: e[4] and e[2] is not None, lambda e: e[2][-1], 30),
        ("the symbol that leads the next epoch", whole, lambda e: e[3], 30)]
print("LEVEL present in the level's state of an epoch (thousandths, read on half the regions):")
for name, mask, keys, top in rows:
    v, n = explained(mask, keys, top); print(f"LEVEL   {name:40s} {v:6.0f}   (epochs read {n})")
