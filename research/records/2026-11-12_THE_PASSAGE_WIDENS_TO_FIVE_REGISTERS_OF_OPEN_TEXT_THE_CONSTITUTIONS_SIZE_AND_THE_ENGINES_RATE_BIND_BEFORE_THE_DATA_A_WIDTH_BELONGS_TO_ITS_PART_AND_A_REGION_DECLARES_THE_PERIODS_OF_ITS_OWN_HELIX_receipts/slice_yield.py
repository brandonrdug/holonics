# Yield of each slice in one shard (bytes of text), and the share of 256-byte windows a line-length rule drops.
import sys, collections
import pyarrow.parquet as pq
t = pq.ParquetFile(sys.argv[1]).read_row_group(0, columns=['open_type', 'language', 'collection', 'text'])
rows = zip(*[t.column(c).to_pylist() for c in ['open_type', 'language', 'collection', 'text']])
def slice_of(o, l, c):
    if o == 'Open Source': return 'code'
    if o == 'Open Web' and l == 'English' and (c in ('Wikipedia', 'StackExchange') or c.startswith('Creative Commons Common Crawl')): return 'web'
    if o == 'Open Science' and l == 'English': return 'science'
    if o == 'Open Culture' and l == 'English' and c in ('English-PD', 'US-PD-Books'): return 'books'
    if o == 'Semantic data': return 'wikidata'
    return None
A = 256
y = collections.Counter(); docs = collections.Counter(); win = collections.Counter(); drop = collections.Counter(); sub = collections.Counter()
for o, l, c, x in rows:
    s = slice_of(o, l, c)
    if s is None: continue
    b = x.encode('utf-8', 'surrogatepass'); y[s] += len(b); docs[s] += 1; sub[(s, c)] += len(b)
    for k in range(0, len(b), A):
        wdw = b[k:k + A]
        if len(wdw) < A // 4: continue
        win[s] += 1
        if (len(wdw) / (wdw.count(b'\n') + 1)) < 25: drop[s] += 1
share = {'code': 40, 'web': 20, 'science': 20, 'books': 12, 'wikidata': 8}
need = {}
for s in share:
    kept = y[s] * (1 - drop[s] / win[s]) if s in ('science', 'books') else y[s]
    need[s] = share[s] / 100 * 1e9 / kept
    print(f"{s:9s} documents {docs[s]:6d}  bytes {y[s] / 1e6:7.1f} MB  windows of {A}: {win[s]:8d}  under 25 bytes a line: {100 * drop[s] / win[s]:5.1f}%  kept {kept / 1e6:7.1f} MB  shards for 1 GB of the mix: {need[s]:.1f}")
print('by collection:', '; '.join(f"{k[0]}/{k[1]} {v / 1e6:.1f}" for k, v in sorted(sub.items())))
m = max(need.values()); print(f"binding slice needs {m:.1f} shards a GB; 8 GB: {8 * m:.0f} shards, {8 * m * 0.434:.0f} GB of transfer; 50 GB: {50 * m:.0f} shards, {50 * m * 0.434:.0f} GB")
