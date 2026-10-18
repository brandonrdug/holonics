"""Reproduce the deterministic train-only partition from train.jsonl alone (test indices are 0..1318 by count)."""
import hashlib, json, sys, unicodedata
from collections import defaultdict
src, out = sys.argv[1], sys.argv[2]
def digest(b): return hashlib.sha256(b).hexdigest()
def norm(q): return ' '.join(unicodedata.normalize('NFKC', q).casefold().split())
rows = [json.loads(x) for x in open(src, 'rb').read().splitlines() if x.strip()]
g = defaultdict(list)
for i, r in enumerate(rows):
    g[digest(norm(r['question']).encode('utf-8'))].append(i)
target = (len(rows) + 5) // 10
selected = []
for h in sorted(g):
    if len(selected) >= target: break
    selected.extend(g[h])
dev = set(selected)
allocation = {'algorithm': 'Ascending SHA256 of NFKC-casefold-whitespace-collapsed UTF-8 question; take whole train question groups until at least round-half-up(10% of train rows). Zero-based source row indices.', 'target_dev_rows': target, 'train_indices': [i for i in range(len(rows)) if i not in dev], 'dev_indices': sorted(dev), 'test_indices': list(range(1319))}
text = json.dumps(allocation, indent=2) + '\n'
open(out, 'w').write(text)
print(digest(text.encode()), len(allocation['train_indices']), len(allocation['dev_indices']))
