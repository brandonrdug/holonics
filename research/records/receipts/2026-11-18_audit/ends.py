import sys, re
for path in sys.argv[1:]:
    rows=[]
    for line in open(path, errors='replace'):
        if line.startswith('STORE_SECTION '):
            d=dict(re.findall(r'(\w+)=(\S+)', line))
            rows.append(d)
    names=[k for k in ['code','web','science','books','wikidata','arithmetic','words'] if k in rows[0]]
    last={}
    for i,d in enumerate(rows):
        for k in names:
            if int(d[k])>0: last[k]=i
    tot={k:sum(int(d[k]) for d in rows) for k in names}
    sites=sum(int(d['sites']) for d in rows)
    print(path.split('/')[-1], 'sections',len(rows),'last section with slice:', {k:last.get(k) for k in names}, 'stretches:',tot)
