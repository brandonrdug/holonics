# C2(c): does the change persist between words?  The revised tick (lossless ring elements, lossless
# contacts with storage and stiffness), one 1-bit injection per word at source ring 0.
#  carried  : the waves and contact states persist from word to word (the first design's refine
#             publishing s', b');
#  released : every word starts at zero change, receives its injection, and at its end the unread
#             change leaves as the word's emitted exchange (the revised law).
import random, sys
from fractions import Fraction as F
from field import Field

widths = [4, 2, 4, 6, 2, 4]
edges = [(0, 1, 2), (1, 2, 1), (2, 3, 3), (3, 4, 2), (4, 5, 1), (5, 0, 2), (0, 3, 2)]
f = Field(widths, edges, seed=11)
eA = 6

def word(state, cell):
    s, a, z = state
    s = [list(x) for x in s]
    s[0][0] += cell
    state = (s, a, z)
    peak = 0
    for _ in range(eA):
        state, _ = f.tick(state)
        peak = max(peak, f.state_bits(state))
    return state, peak

rng = random.Random(5)
cells = [F(rng.randint(0, 1)) for _ in range(256)]

# released: independent words
peaks = [word(f.zero(), c)[1] for c in cells[:32]]
print("released: peak bits inside a word of", eA, "ticks, over 32 words: min", min(peaks), "max", max(peaks))
for L in (2, 4, 8, 16, 32):
    st = f.zero(); st[0][0][0] += 1; pk = []
    for t in range(L):
        st, _ = f.tick(st); pk.append(f.state_bits(st))
    print(f"  one word of {L:2d} ticks: peak bits {max(pk)}")

# carried: state persists
st = f.zero(); out = {}
limit = int(sys.argv[1]) if len(sys.argv) > 1 else 64
for w in range(1, limit + 1):
    st, _ = word(st, cells[w - 1])
    if w in (8, 16, 32, 64, 128, 256):
        out[w] = f.state_bits(st)
        print("carried: bits after", w, "words:", out[w], flush=True)
