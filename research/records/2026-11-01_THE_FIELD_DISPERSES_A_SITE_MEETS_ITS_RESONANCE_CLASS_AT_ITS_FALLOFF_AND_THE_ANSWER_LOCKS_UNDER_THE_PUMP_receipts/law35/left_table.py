# A reading only, never part of the field: a left-to-right byte table with interpolated absolute discounting (orders 0..K),
# fitted on TRAIN.txt, coding each held answer's bytes (and the blank line that ends it) given its question and the answer so far.
import sys, math
from collections import defaultdict
train = open(sys.argv[1], 'rb').read()
held = open(sys.argv[2], 'rb').read().split(b'\n\n')
K = int(sys.argv[3]); D = 0.75
cnt = [defaultdict(lambda: defaultdict(int)) for _ in range(K + 1)]
for i in range(len(train)):
    for k in range(K + 1):
        if i - k < 0: break
        cnt[k][train[i - k:i]][train[i]] += 1
tot = [{c: (sum(d.values()), len(d)) for c, d in cnt[k].items()} for k in range(K + 1)]
def prob(ctx, b):
    p = 1.0 / 257
    for k in range(K + 1):
        c = ctx[len(ctx) - k:] if k else b''
        if len(c) < k: break
        t = tot[k].get(c)
        if not t: break
        n, u = t
        p = max(cnt[k][c].get(b, 0) - D, 0) / n + D * u / n * p
    return p
bits = 0.0; nb = 0
for prob_text in held:
    if not prob_text.strip(): continue
    q, _, a = prob_text.partition(b'\n')
    text = q + b'\n' + a + b'\n\n'
    for i in range(len(q) + 1, len(text)):
        bits -= math.log2(prob(text[max(0, i - K):i], text[i])); nb += 1
print(f"order={K} answer_bytes={nb} bits_a_byte={bits / nb:.3f}")
