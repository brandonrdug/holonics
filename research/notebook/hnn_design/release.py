# C2(f), R3 R1-R2: what the collapse may release is exactly what no admitted receiver distinguishes,
# computed by the two per-ring recursions of the design, time-indexed.
#
# Path of six rings 0-1-2-3-4-5, source ring 0, receiving ring 2 (e_0 = 2).  The reading at epoch e is
# the anchor v_R that tick e's junction computes, from the state after e ticks; the last receiving
# epoch is e_last = e_0 + A - 1, and the word evaluates e_max = e_0 + A junction steps.
#
# The recursions, one neighbour exchange per round, e_last rounds:
#   reach    r_g = hop distance from the source rings  (r = 0 on S;  r_h <- min(r_h, r_g + 1))
#   observe  o_g = hop distance to the receiving ring  (o = 0 at R;  o_g <- min(o_g, o_h + 1))
# One tick maps block x to block y along an edge x -> y; the edge's operator is used on a change that
# some admitted reading sees exactly when  r_x + 1 + o_y <= e_last.  So:
#   ring g's element (edge g -> g)            is retained iff  r_g + 1 + o_g <= e_last
#   ring g's junction (edges g -> g, g -> h)  is retained iff  r_g + o_g <= e_last  (always at R)
#   contact a = (g, h)'s channel (C, K, D)    is retained iff  min(r_g, r_h) + 1 + min(o_g, o_h) <= e_last
#   contact a's conductance G_a               is retained iff  its channel or either end's junction is
# and everything else is released.  This is FaceMap.horizonBlind(e_last - t) at the block's reach time
# t = r_x, on the loci's sparsity.
import copy, random
from fractions import Fraction as F
from field import Field, gram, rr

widths = [4, 4, 4, 4, 4, 4]
edges = [(0, 1, 2), (1, 2, 2), (2, 3, 2), (3, 4, 2), (4, 5, 2)]
base = Field(widths, edges, seed=23, dissipative=True)
S, R = {0}, 2
G = len(widths)
adj = {g: sorted({c['h'] for c in base.contacts if c['g'] == g} | {c['g'] for c in base.contacts if c['h'] == g})
       for g in range(G)}
INF = 10**9

def recursions(e_last):
    r = [0 if g in S else INF for g in range(G)]
    o = [0 if g == R else INF for g in range(G)]
    for _ in range(e_last):
        r = [min([r[g]] + [r[h] + 1 for h in adj[g]]) for g in range(G)]
        o = [min([o[g]] + [o[h] + 1 for h in adj[g]]) for g in range(G)]
    return r, o

def retention(e_last):
    r, o = recursions(e_last)
    element = {g for g in range(G) if r[g] + 1 + o[g] <= e_last}
    junction = {g for g in range(G) if (g == R and r[g] <= e_last) or r[g] + o[g] <= e_last}
    channel = {ai for ai, c in enumerate(base.contacts)
               if min(r[c['g']], r[c['h']]) + 1 + min(o[c['g']], o[c['h']]) <= e_last}
    conduct = {ai for ai, c in enumerate(base.contacts)
               if ai in channel or c['g'] in junction or c['h'] in junction}
    return dict(element=element, junction=junction, channel=channel, conduct=conduct), r, o

def separable(e_last):
    """The first realization: reached at some time and read at some time, not in time together."""
    r, o = recursions(e_last)
    element = {g for g in range(G) if r[g] <= e_last and o[g] <= e_last}
    channel = {ai for ai, c in enumerate(base.contacts)
               if min(r[c['g']], r[c['h']]) <= e_last and min(o[c['g']], o[c['h']]) <= e_last}
    return element, channel

def entries(element, channel):
    return (sum(widths[g] ** 2 for g in element)
            + sum(3 * base.contacts[ai]['k'] ** 2 for ai in channel))
TOTAL = entries(range(G), range(len(base.contacts)))

def replaced(keep, rng, only=None):
    """A copy of the field with every item outside `keep` (or, with `only`, just that one item)
    replaced by arbitrary values."""
    f = copy.deepcopy(base)
    def hit(kind, x):
        return (kind, x) == only if only else x not in keep[kind]
    for g in range(G):
        if hit('element', g):
            f.cay[g] = [[rr(rng) for _ in range(widths[g])] for _ in range(widths[g])]
        if hit('junction', g):
            f.Yr[g] = F(rng.randint(1, 9), rng.randint(1, 9))
    for ai, c in enumerate(f.contacts):
        k = c['k']
        if hit('channel', ai):
            c['C'] = gram(rng, k); c['K'] = gram(rng, k); c['D'] = gram(rng, k, F(1, 2))
        if hit('conduct', ai):
            c['G'] = F(rng.randint(1, 9), rng.randint(1, 9))
    return f

def readings(f, inj, e0, e_last):
    st = f.zero(); st[0][0] = list(inj); out = []
    for t in range(e_last + 1):          # e_max = e_last + 1 junction steps; the last read ends the word
        if t >= e0:
            s, a, z = st
            tot = f.Yr[R] + sum(f.contacts[ai]['G'] for ai in f.inc[R])
            out.append([(f.Yr[R] * s[R][i] + sum(f.contacts[ai]['G'] * a[(R, ai)][i] for ai in f.inc[R])) / tot
                        for i in range(widths[R])])
        if t < e_last:
            st, _ = f.tick(st)
    return out

def check(A, label):
    e_last = 2 + A - 1
    keep, r, o = retention(e_last)
    e0 = r[R]
    released = TOTAL - entries(keep['element'], keep['channel'])
    sep_el, sep_ch = separable(e_last)
    show = lambda v: [x if x < INF else 'inf' for x in v]
    print(f"{label}: e_0 = {e0}, A = {A}, e_last = {e_last}, e_max = {e_last + 1}; "
          f"reach r = {show(r)}, observe o = {show(o)}")
    print(f"  retained: elements {sorted(keep['element'])}, junctions {sorted(keep['junction'])}, "
          f"channels {[tuple((base.contacts[ai]['g'], base.contacts[ai]['h'])) for ai in sorted(keep['channel'])]}, "
          f"conductances {[tuple((base.contacts[ai]['g'], base.contacts[ai]['h'])) for ai in sorted(keep['conduct'])]}")
    print(f"  time-indexed recursion releases {released} of {TOTAL} constitution entries "
          f"(element n_g^2, channel 3 k_a^2); the separable form releases "
          f"{TOTAL - entries(sep_el, sep_ch)} (lawful, finer)")
    rng = random.Random(9); same = True
    for _ in range(20):
        inj = [F(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(widths[0])]
        same &= readings(base, inj, e0, e_last) == readings(replaced(keep, rng), inj, e0, e_last)
    print("  every released item replaced by arbitrary values: every admitted reading identical, "
          "20 injections:", same)
    rng = random.Random(10); items = [(k, x) for k in ('element', 'junction', 'channel', 'conduct')
                                      for x in sorted(keep[k])]
    tight = 0
    for item in items:
        changed = False
        for _ in range(5):
            inj = [F(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(widths[0])]
            changed |= readings(base, inj, e0, e_last) != readings(replaced(keep, rng, only=item), inj, e0, e_last)
        tight += changed
    print(f"  tightness: replacing any one retained item changes some reading: {tight} of {len(items)} items")

check(2, "the design's example")
check(1, "the rim case")
