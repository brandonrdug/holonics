"""Ruler (host, no machinery): G200 on a lap's mean. Joins cavity.tsv (P rows: c0 the news, cK the code) with loudness.tsv (the
last stage's lane powers) by (slice, stretch, t); cuts each stretch into the level's epochs (the engine's level_anchors on c0,
section log2(alphabet) bits on 2^-20); reads an epoch's summed power against its places' mean code."""
import sys, math, collections
cav, loud, alphabet = sys.argv[1], sys.argv[2], int(sys.argv[3])
SECTION = round(math.log2(alphabet) * 2**20)
def rank(v):
    o = sorted(range(len(v)), key=lambda i: v[i]); r = [0.0]*len(v); i = 0
    while i < len(o):
        j = i
        while j + 1 < len(o) and v[o[j+1]] == v[o[i]]: j += 1
        for k in range(i, j+1): r[o[k]] = (i + j) / 2
        i = j + 1
    return r
def spearman(a, b):
    if len(a) < 3: return float('nan')
    ra, rb = rank(a), rank(b); n = len(a); ma = sum(ra)/n; mb = sum(rb)/n
    num = sum((x-ma)*(y-mb) for x, y in zip(ra, rb)); den = math.sqrt(sum((x-ma)**2 for x in ra) * sum((y-mb)**2 for y in rb))
    return num/den if den else float('nan')
news = collections.defaultdict(dict); code = collections.defaultdict(dict)
with open(cav) as f:
    h = f.readline().rstrip('\n').split('\t'); I = {k: i for i, k in enumerate(h)}
    for l in f:
        w = l.rstrip('\n').split('\t')
        if w[0] != 'P': continue
        key = (w[I['slice']], int(w[I['stretch']])); t = int(w[I['t']])
        news[key][t] = int(w[I['cO']]) if w[I['cO']] != '-' else None; code[key][t] = int(w[I['cK']])
power = collections.defaultdict(dict)
with open(loud) as f:
    h = f.readline().rstrip('\n').split('\t'); I = {k: i for i, k in enumerate(h)}
    last = max(int(c.split('_')[0][1:]) for c in h if c.startswith('s') and '_l' in c)
    cols = [I[c] for c in h if c.startswith(f's{last}_l')]
    for l in f:
        w = l.rstrip('\n').split('\t')
        if w[0] != 'P': continue
        power[(w[I['slice']], int(w[I['stretch']]))][int(w[I['t']])] = sum(int(w[c]) for c in cols)
def anchors(c):
    n = len(c); S = [0]*(n+1)
    for t in range(n): S[t+1] = S[t] + c[t]
    left = [None]*n; st = []
    for t in range(n):
        while st and not c[st[-1]] >= c[t]: st.pop()
        left[t] = st[-1] if st else None; st.append(t)
    right = [None]*n; st = []
    for t in range(n-1, -1, -1):
        while st and not c[st[-1]] > c[t]: st.pop()
        right[t] = st[-1] if st else None; st.append(t)
    out = [0]
    for t in range(1, n):
        l = S[t+1] - S[left[t]+1] if left[t] is not None else None
        r = S[right[t]+1] - S[t+1] if right[t] is not None else None
        rho = min(l, r) if (l is not None and r is not None) else (l if l is not None else r)
        if rho is None or rho >= SECTION: out.append(t)
    return out
by = collections.defaultdict(list)
for key in news:
    ts = sorted(news[key])
    if ts != list(range(len(ts))) or key not in power or len(power[key]) != len(ts) or any(news[key][t] is None for t in ts): continue
    c = [news[key][t] for t in ts]; a = anchors(c) + [len(ts)]
    for j in range(len(a) - 1):
        pl = range(a[j], a[j+1])
        m = sum(power[key][t] for t in pl); k = sum(code[key][t] for t in pl) / len(pl)
        by[key[0]].append((len(pl), m, m / len(pl), k))
NAT = math.log(2) / 2**20
for s in sorted(by) + ['all']:
    e = [x for v in by.values() for x in v] if s == 'all' else by[s]
    sa = spearman([x[1] for x in e], [x[3] for x in e])
    sl = spearman([x[0] for x in e], [x[3] for x in e])
    # (b): within one length, rank of mean power a place against rank of mean code, pooled over lengths 2..64
    num = 0; den = 0
    groups = collections.defaultdict(list)
    for x in e:
        if 2 <= x[0] <= 64: groups[x[0]].append(x)
    pooled = []
    for L, g in groups.items():
        if len(g) < 5: continue
        rp = rank([x[2] for x in g]); rc = rank([x[3] for x in g]); n = len(g)
        pooled += [((p - (n-1)/2) / n, (q - (n-1)/2) / n) for p, q in zip(rp, rc)]
    sb = (sum(p*q for p, q in pooled) / math.sqrt(sum(p*p for p, _ in pooled) * sum(q*q for _, q in pooled))) if pooled else float('nan')
    lens = [x[0] for x in e]
    print(f"G200 {s:9s} epochs={len(e):6d} mean_len={sum(lens)/len(lens):5.2f} (a)rho(sum_power,code)={sa:+.3f} rho(len,code)={sl:+.3f} (b)within-length rho(power_a_place,code)={sb:+.3f} pooled={len(pooled)}")
