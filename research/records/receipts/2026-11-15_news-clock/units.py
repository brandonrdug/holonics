import sys, glob, re, os
UNIT = 2.0 ** -20
Q = sys.argv[1]  # the line's directory, holding loud_P{lap}/loudness.tsv
def read(p):
    seqs = {}
    with open(p) as f:
        next(f)
        for l in f:
            r = l.split('\t', 7)
            if r[0] != 'P':
                continue
            seqs.setdefault((r[1], int(r[2])), []).append((int(r[3]), int(r[5]) * UNIT))
    return seqs
def sites(cs, sigma):
    n = len(cs); S = []; s = 0.0
    for c in cs:
        s += c; S.append(s)
    prev = [None] * n; st = []
    for t in range(n):
        while st and cs[st[-1]] < cs[t]:
            st.pop()
        prev[t] = st[-1] if st else None
        st.append(t)
    nxt = [None] * n; st = []
    for t in range(n - 1, -1, -1):
        while st and cs[st[-1]] <= cs[t]:
            st.pop()
        nxt[t] = st[-1] if st else None
        st.append(t)
    count = 0
    for t in range(n):
        a = S[t] - S[prev[t]] if prev[t] is not None else float('inf')
        b = S[nxt[t]] - S[t] if nxt[t] is not None else float('inf')
        if min(a, b) >= sigma:
            count += 1
    return count
laps = sorted(int(m.group(1)) for p in glob.glob(Q + '/loud_P*/loudness.tsv') for m in [re.search(r'loud_P(\d+)/', p)] if m)
for lap in laps:
    seqs = read('%s/loud_P%d/loudness.tsv' % (Q, lap))
    out = []
    for region in sorted({k[0] for k in seqs}):
        places = news = 0; cnt = {4: 0, 8: 0, 16: 0}
        for (sl, _), seq in seqs.items():
            if sl != region:
                continue
            seq.sort()
            cs = [c for _, c in seq]
            places += len(cs); news += sum(cs)
            for sg in cnt:
                cnt[sg] += sites(cs, sg)
        out.append('%s:%.4f/%.4f/%.4f(b%.4f,bits%.3f)' % (region, cnt[4] / places, cnt[8] / places, cnt[16] / places, news / places / 8, news / places))
    print('SITES lap=%d sites_a_place(4/8/16 bits) %s' % (lap, ' '.join(out)))
