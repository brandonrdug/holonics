# usage: python3 -I words.py TRAIN SAMPLE_BIN... : the share of the sample's letter words found as words in
# TRAIN, and the share of its adjacent word pairs (inside one clause: split at line ends and . ? ! , ; :) found adjacent
# in TRAIN; the last line pools the files.
import re, sys
word = re.compile(rb"[A-Za-z]+(?:'[A-Za-z]+)?")
def pairs(text):
    out = []
    for line in re.split(rb"[\n.?!,;:]", text):
        ws = [w.lower() for w in word.findall(line)]
        out.extend(zip(ws, ws[1:]))
    return out
train = open(sys.argv[1], 'rb').read()
vocab = set(w.lower() for w in word.findall(train))
seen = set(pairs(train))
tw = tk = tp = tkp = 0
for path in sys.argv[2:]:
    text = open(path, 'rb').read()
    ws = [w.lower() for w in word.findall(text)]
    ps = pairs(text)
    known = sum(w in vocab for w in ws)
    kp = sum(p in seen for p in ps)
    tw += len(ws); tk += known; tp += len(ps); tkp += kp
    print(f"WORDS {path} words={len(ws)} found={known} share={known / max(len(ws), 1):.3f} pairs={len(ps)} found={kp} share={kp / max(len(ps), 1):.3f}")
print(f"WORDS_POOLED files={len(sys.argv) - 2} words={tw} share={tk / max(tw, 1):.3f} pairs={tp} share={tkp / max(tp, 1):.3f}")
