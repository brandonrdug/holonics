# A reading only, never part of the field: the elementary statistics of a passage of English (GSM8K's training passage),
# each stated as a physical pattern of the bytes: the alphabet, the conditional entropy by context, the mutual information
# between bytes at a distance (the falloff), the periods of the boundaries (the clocks), the words (Zipf, Heaps, coverage),
# where in a word the uncertainty sits, and how much of an answer its question already holds.
import sys, math, re
from collections import Counter
import numpy as np

text = open(sys.argv[1], 'rb').read()
b = np.frombuffer(text, dtype=np.uint8).astype(np.int64)
N = len(b)
def H(counts):
    c = np.asarray([v for v in counts if v > 0], dtype=np.float64); p = c / c.sum()
    return float(-(p * np.log2(p)).sum())

print(f"## passage bytes={N}")
u = np.bincount(b, minlength=256)
print(f"alphabet used={int((u > 0).sum())} H0_bits={H(u):.3f}")
cls = {'lower': sum(u[97:123]), 'upper': sum(u[65:91]), 'digit': sum(u[48:58]), 'space': u[32], 'newline': u[10]}
cls['punct_other'] = N - sum(cls.values())
print("classes " + " ".join(f"{k}={v / N:.4f}" for k, v in cls.items()))
top = np.argsort(-u)[:16]
print("top bytes " + " ".join(f"{repr(chr(i))}:{u[i] / N:.4f}" for i in top))

# mutual information between bytes d apart: I(X_t; X_(t+d)) in bits
print("## falloff: I(X_t ; X_(t+d)) bits")
row = []
for d in [1, 2, 3, 4, 5, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024]:
    joint = np.bincount(b[:-d] * 256 + b[d:], minlength=65536).reshape(256, 256).astype(np.float64)
    pj = joint / joint.sum(); px = pj.sum(1); py = pj.sum(0)
    nz = pj > 0
    mi = float((pj[nz] * np.log2(pj[nz] / np.outer(px, py)[nz])).sum())
    # the finite-sample floor: about (k-1)^2 / (2 N ln 2) for k used classes
    k = int((u > 0).sum()); floor = (k - 1) ** 2 / (2 * (N - d) * math.log(2))
    row.append((d, mi, floor))
    print(f"d={d} mi={mi:.5f} floor={floor:.5f} excess={mi - floor:.5f}")
xs = [(math.log(d), math.log(mi - fl)) for d, mi, fl in row if 8 <= d <= 256 and mi - fl > 0]
if len(xs) > 2:
    mx = sum(x for x, _ in xs) / len(xs); my = sum(y for _, y in xs) / len(xs)
    slope = sum((x - mx) * (y - my) for x, y in xs) / sum((x - mx) ** 2 for x, _ in xs)
    print(f"power-law exponent over d=8..256 (excess over the floor): I ~ d^{slope:.3f}")

# the clocks: periods of the boundaries
print("## clocks")
s = text.decode('utf-8', 'replace')
words = re.findall(r"\S+", s)
wl = Counter(len(w) for w in words)
mean_wl = sum(k * v for k, v in wl.items()) / len(words)
print(f"tokens(whitespace)={len(words)} mean_token_len={mean_wl:.3f} token_len_dist " + " ".join(f"{k}:{wl[k] / len(words):.3f}" for k in range(1, 13)))
lines = [l for l in s.split('\n') if l]
ll = np.array([len(l) for l in lines])
print(f"lines={len(lines)} line_len_median={int(np.median(ll))} q1={int(np.percentile(ll, 25))} q3={int(np.percentile(ll, 75))}")
probs = s.split('\n\n')
qs = [p.split('\n', 1)[0] for p in probs if '\n' in p]; ans = [p.split('\n', 1)[1] for p in probs if '\n' in p]
print(f"problems={len(probs)} question_len_median={int(np.median([len(q) for q in qs]))} answer_len_median={int(np.median([len(a) for a in ans]))}")
sp = (b == 32).astype(np.float64); sp -= sp.mean()
f = np.fft.rfft(sp[: 1 << 21]); pw = np.abs(f) ** 2; pw[0] = 0
freqs = np.fft.rfftfreq(1 << 21)
peaks = np.argsort(-pw[1:])[:5] + 1
print("space indicator spectrum peaks (period in bytes) " + " ".join(f"{1 / freqs[i]:.2f}" for i in peaks))

# words: Zipf, Heaps, coverage
print("## words")
low = [re.sub(r"[^a-z']", "", w.lower()) for w in words]; low = [w for w in low if w]
wc = Counter(low); ranks = np.array(sorted(wc.values(), reverse=True), dtype=np.float64)
r = np.arange(1, len(ranks) + 1, dtype=np.float64)
sel = (r >= 10) & (r <= 1000)
z = np.polyfit(np.log(r[sel]), np.log(ranks[sel]), 1)[0]
print(f"word types={len(wc)} word tokens={len(low)} zipf_exponent(ranks 10..1000)={z:.3f} H_word_unigram_bits={H(wc.values()):.3f}")
cum = np.cumsum(ranks) / ranks.sum()
print("coverage by the top K types " + " ".join(f"K={K}:{cum[K - 1]:.3f}" for K in [10, 50, 100, 500, 1000, 2000, 5000] if K <= len(cum)))
print("top words " + " ".join(f"{w}:{c}" for w, c in wc.most_common(25)))
seen = set(); heaps = []
for i, w in enumerate(low, 1):
    seen.add(w)
    if i in (1000, 10000, 100000, len(low)): heaps.append((i, len(seen)))
hb = math.log(heaps[-1][1] / heaps[1][1]) / math.log(heaps[-1][0] / heaps[1][0])
print("heaps (tokens, types) " + " ".join(f"{a}:{c}" for a, c in heaps) + f" beta={hb:.3f}")
print(f"hapax share of types={sum(1 for v in wc.values() if v == 1) / len(wc):.3f} of tokens={sum(1 for v in wc.values() if v == 1) / len(low):.4f}")

# where in a word the uncertainty sits: H(letter | position in word, previous letters of the word) from the passage's counts
print("## inside a word: H(letter_k | letters before it in the word), plug-in, lowercase letter words")
lw = [w for w in low if w.isalpha()]
for k in range(0, 7):
    ctx = Counter(); joint = Counter()
    for w in lw:
        if len(w) > k:
            ctx[w[:k]] += 1; joint[(w[:k], w[k])] += 1
    tot = sum(joint.values())
    h = -sum(c / tot * math.log2(c / ctx[p]) for (p, _), c in joint.items())
    print(f"k={k} letters_known={k} H_bits={h:.3f} share_of_words_this_long={tot / len(lw):.3f}")
ends = Counter(w[-2:] for w in lw if len(w) > 3)
print("commonest endings " + " ".join(f"-{e}:{c / sum(ends.values()):.3f}" for e, c in ends.most_common(12)))

# the copy channel: how much of an answer its question already holds
print("## question and answer")
tot = cop = num_tot = num_cop = 0
for q, a in zip(qs, ans):
    qw = set(re.findall(r"[A-Za-z]+|\d+(?:\.\d+)?", q))
    for w in re.findall(r"[A-Za-z]+|\d+(?:\.\d+)?", a):
        tot += 1; cop += w in qw
        if w[0].isdigit():
            num_tot += 1; num_cop += w in qw
print(f"answer word/number tokens={tot} found in own question={cop / tot:.3f}; numbers={num_tot} found in own question={num_cop / num_tot:.3f}")
cap = Counter(w for q in qs for w in re.findall(r"\b[A-Z][a-z]+\b", q))
print(f"capitalized words in questions (names, starts) types={len(cap)}")
