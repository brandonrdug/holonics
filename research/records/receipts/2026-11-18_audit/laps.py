import sys, os, re, statistics
Q = sys.argv[1]
lo, hi = int(sys.argv[2]), int(sys.argv[3])
def kv(line):
    return dict(re.findall(r'(\w+)=(\S+)', line))
print("lap store secs ended stopped before_mean open_mean ms_sec | held cK bits: all code web sci books wiki arith words | loud_nats")
for n in range(lo, hi+1):
    log = f"{Q}/lap{n}.log"
    if not os.path.exists(log): continue
    store = '?'; befores=[]; opens=[]; mss=[]; ended='-'; stopped='-'
    for line in open(log, errors='replace'):
        if line.startswith('FIELD_COMMAND train-store'):
            w = line.split(); store = os.path.basename(w[4])[-5:]
        elif line.startswith('STORE_SECTION '):
            d = kv(line)
            befores.append(int(d['before']))
            if 'opening' in d: opens.append(int(d['opening']))
            mss.append(int(d['ms']))
        elif line.startswith('STORE_PASS '):
            ended = kv(line)['ended']
        elif line.startswith('STORE_STOPPED'):
            stopped = kv(line)['sections']
    held = {}
    cav = f"{Q}/out_P{n}/cavity.tsv"
    if os.path.exists(cav):
        sums = {}
        with open(cav) as f:
            next(f)
            for line in f:
                w = line.split('\t')
                if w[0] != 'P': continue
                s = w[1]; ck = int(w[6])
                a = sums.setdefault(s, [0,0]); a[0]+=ck; a[1]+=1
        tot = sum(v[0] for v in sums.values()); cnt = sum(v[1] for v in sums.values())
        held['all'] = tot/cnt/2**20
        for s,v in sums.items(): held[s] = v[0]/v[1]/2**20
    loud = '-'
    lt = f"{Q}/loud_P{n}.table"
    if os.path.exists(lt):
        for line in open(lt):
            if line.startswith('LOUDNESS region=all'):
                loud = kv(line).get('nats_a_place','-')
    hs = ' '.join(f"{held.get(k,float('nan')):.4f}" for k in ['all','code','web','science','books','wikidata','arithmetic','words'])
    bm = statistics.mean(befores)/1e6 if befores else float('nan')
    om = statistics.mean(opens)/1e6 if opens else float('nan')
    ms = statistics.mean(mss) if mss else float('nan')
    print(f"{n} {store} {len(befores)} {ended} {stopped} {bm:.4f} {om:.4f} {ms:.0f} | {hs} | {loud}")
