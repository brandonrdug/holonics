import sys, collections
import pyarrow.parquet as pq
path = sys.argv[1]
pf = pq.ParquetFile(path)
print('rows', pf.metadata.num_rows, 'row groups', pf.metadata.num_row_groups, 'columns', pf.schema_arrow.names)
by = collections.defaultdict(lambda: [0, 0, 0])          # open_type -> rows, bytes, tokens
byl = collections.defaultdict(lambda: [0, 0])            # (open_type, language) -> rows, bytes
byc = collections.defaultdict(lambda: [0, 0])            # (open_type, collection) -> rows, bytes
lens = collections.defaultdict(list)
order = []                                               # open_type sequence, to see whether rows are shuffled
for rg in range(pf.metadata.num_row_groups):
    t = pf.read_row_group(rg, columns=['open_type', 'language', 'collection', 'token_count', 'text'])
    ot = t.column('open_type').to_pylist(); la = t.column('language').to_pylist(); co = t.column('collection').to_pylist()
    tk = t.column('token_count').to_pylist(); tx = t.column('text').to_pylist()
    for o, l, c, k, x in zip(ot, la, co, tk, tx):
        b = len(x.encode('utf-8', 'surrogatepass')) if x else 0
        by[o][0] += 1; by[o][1] += b; by[o][2] += (k or 0)
        byl[(o, l)][0] += 1; byl[(o, l)][1] += b
        byc[(o, c)][0] += 1; byc[(o, c)][1] += b
        lens[o].append(b)
        if len(order) < 60: order.append(o)
tot = sum(v[1] for v in by.values())
print('text bytes in the shard: %.1f MB' % (tot / 1e6))
print('first 60 rows open_type:', ' '.join(''.join(w[0] for w in o.split()) for o in order))
for o, v in sorted(by.items(), key=lambda kv: -kv[1][1]):
    ls = sorted(lens[o]); med = ls[len(ls) // 2]; p90 = ls[int(len(ls) * 0.9)]
    print('\n%-16s rows %6d  bytes %7.1f MB (%.1f%%)  tokens %6.1f M  bytes/token %.2f  median %d  p90 %d' % (o, v[0], v[1] / 1e6, 100 * v[1] / tot, v[2] / 1e6, v[1] / max(1, v[2]), med, p90))
    top = sorted(((k[1], w) for k, w in byl.items() if k[0] == o), key=lambda kv: -kv[1][1])[:12]
    print('   languages by bytes: ' + '; '.join('%s %.1f MB' % (k, w[1] / 1e6) for k, w in top))
    top = sorted(((k[1], w) for k, w in byc.items() if k[0] == o), key=lambda kv: -kv[1][1])[:12]
    print('   collections by bytes: ' + '; '.join('%s %.1f MB (%d)' % (k, w[1] / 1e6, w[0]) for k, w in top))
