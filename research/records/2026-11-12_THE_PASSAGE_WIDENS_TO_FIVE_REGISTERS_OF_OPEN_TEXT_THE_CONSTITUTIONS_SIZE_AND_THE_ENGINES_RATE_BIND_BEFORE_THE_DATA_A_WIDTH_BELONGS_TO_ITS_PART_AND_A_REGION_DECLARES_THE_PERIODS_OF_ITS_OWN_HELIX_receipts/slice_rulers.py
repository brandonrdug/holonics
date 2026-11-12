import sys, zlib, lzma, collections
import pyarrow.parquet as pq
t = pq.ParquetFile(sys.argv[1]).read_row_group(0, columns=['open_type', 'language', 'collection', 'title', 'license', 'date', 'text'])
rows = list(zip(*[t.column(c).to_pylist() for c in ['open_type', 'language', 'collection', 'title', 'license', 'date', 'text']]))
def group(pred): return [r for r in rows if pred(r)]
groups = [
 ('Semantic data (Wikidata)', lambda r: r[0] == 'Semantic data'),
 ('Open Source, all', lambda r: r[0] == 'Open Source'),
 ('Open Source, Python', lambda r: r[0] == 'Open Source' and r[1] == 'Python'),
 ('Open Web, English Wikipedia', lambda r: r[0] == 'Open Web' and r[2] == 'Wikipedia' and r[1] == 'English'),
 ('Open Web, StackExchange', lambda r: r[0] == 'Open Web' and r[2] == 'StackExchange'),
 ('Open Web, CCC', lambda r: r[0] == 'Open Web' and r[2].startswith('Creative Commons') and r[1] == 'English'),
 ('Open Web, Youtube-Commons', lambda r: r[0] == 'Open Web' and r[2] == 'Youtube-Commons' and r[1] == 'English'),
 ('Open Science, English OpenAlex', lambda r: r[0] == 'Open Science' and r[2] == 'OpenAlex' and r[1] == 'English'),
 ('Open Culture, English-PD', lambda r: r[0] == 'Open Culture' and r[2] == 'English-PD'),
 ('Open Culture, US-PD-Newspapers', lambda r: r[0] == 'Open Culture' and r[2] == 'US-PD-Newspapers'),
 ('Open Culture, US-PD-Books', lambda r: r[0] == 'Open Culture' and r[2] == 'US-PD-Books'),
]
mode = sys.argv[2]
for name, pred in groups:
    g = group(pred)
    blob = b''
    for r in g:
        blob += r[6].encode('utf-8', 'surrogatepass') + b'\x1e'
        if len(blob) > 16_000_000: break
    blob = blob[:16_000_000]
    if mode == 'rulers':
        asc = sum(1 for b in blob if b < 128) / max(1, len(blob))
        z = len(zlib.compress(blob, 9)) / max(1, len(blob)); x = len(lzma.compress(blob, preset=6)) / max(1, len(blob))
        cnt = collections.Counter(blob); import math
        h0 = -sum(c / len(blob) * math.log2(c / len(blob)) for c in cnt.values())
        print('%-34s rows %6d  sample %5.1f MB  ascii %.3f  order-0 %.2f bits/byte  zlib %.3f  xz %.3f (%.2f bits/byte)' % (name, len(g), len(blob) / 1e6, asc, h0, z, x, 8 * x))
    else:
        want = sys.argv[3:]
        if not any(w in name for w in want): continue
        print('=' * 20, name, 'rows', len(g))
        step = max(1, len(g) // 4)
        for r in g[1::step][:3]:
            x = r[6]
            print('--- lang=%s lic=%s date=%s title=%r chars=%d' % (r[1], r[4], r[5], (r[3] or '')[:70], len(x)))
            k = 0 if len(x) < 1400 else len(x) // 3
            print('   ' + x[k:k + 620].replace('\n', '\n   '))
