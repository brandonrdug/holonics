"""The transcript's code given its own sound against given another utterance's (read-reach codes.tsv on pair_rows.tsv), by row pair.

python3 -I pair_codes.py OUT   (host floats, a ruler's)
"""
import sys, math, statistics as st
LN2_20 = math.log(2) / (1 << 20)
out = sys.argv[1]
rows = {}
for line in open(f"{out}/codes.tsv"):
    w = line.rstrip("\n").split("\t")
    r, label, place, code = int(w[0]), w[1], int(w[2]), int(w[3]) * LN2_20
    rows.setdefault(r, (label, {}))[1][place] = code
pairs = {}
for r, (label, codes) in rows.items():
    kind, frames, k = label.split(":")[0], int(label.split(":")[1]), r // 2
    words = [c for p, c in codes.items() if p > frames]  # the transcript's places, past the line's end after the frames
    first = [c for p, c in codes.items() if frames < p <= frames + 20]
    frm = [c for p, c in codes.items() if 0 < p < frames]
    pairs.setdefault(k, {})[kind] = (sum(words), len(words), sum(first), len(first), sum(frm), len(frm))
d, dfirst, own_n, swap_n, own_t, swap_t, own_f, frames_n = [], [], 0, 0, 0.0, 0.0, 0.0, 0
for k, v in pairs.items():
    if "own" in v and "swap" in v:
        o, s = v["own"], v["swap"]
        d.append((o[0] - s[0]) / o[1]); dfirst.append((o[2] - s[2]) / max(o[3], 1))
        own_t += o[0]; swap_t += s[0]; own_n += o[1]; own_f += o[4]; frames_n += o[5]
m, se = st.mean(d), st.stdev(d) / len(d) ** 0.5
print(f"PAIRS_TEXT pairs={len(d)} letters={own_n} own={own_t / own_n:.4f} swap={swap_t / own_n:.4f} own_less_swap={m:+.4f} se={se:.4f} first20_own_less_swap={st.mean(dfirst):+.4f} frames_own={own_f / max(frames_n, 1):.4f}")
