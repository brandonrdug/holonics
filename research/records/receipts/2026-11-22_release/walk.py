"""A ruler's arithmetic: the material's growth on the store line against a free walk at the deposit's own noise, and what a leak holds.

The deposit steps an entry by 2^(-rate) * m / (floor(sqrt(v)) + 1), m and v the covector's two moments at 2^(-3) and 2^(-8)
(THE_ENGINE, the deposit's row). On a covector of zero mean and unlike sections the ratio has root mean square 1/sqrt(15) and mean
modulus 0.206, and its running sum over n sections has root mean square sqrt(n): an entry no comparison restrains walks
2^(-rate) sqrt(n). With the store's leak, theta <- theta - 2^(-K) theta after the step (Learner::relax), the same entry rests at
a spread 2^(-rate) sqrt(2^K / 2) and an entry whose ratio has mean c rests at 2^(K - rate) c.

Part 1 checks those three figures on a planted covector (the two moments as the engine keeps them, in floats: a ruler).
Part 2 reads the audit's figures of November 18 (its section 1.6: root mean squares by family at lap 10 and lap 94, the line at
2^(-12), 3,000 sections a lap) against the walk. Part 3 prints what a leak of K bits holds and how fast it settles.
Outside the machine; it enters no law. Part 2's reading (a free walk) was withdrawn the same night: the entries are held, and
length.py reads the same figures as the lengthening of a part read as a ratio. Usage: walk.py"""
import math, random

def planted(rate, leak, mean, entries, sections, seed):
    """Root mean square of an entry and its mean, after `sections` steps of the deposit's form on a covector mean + unit noise."""
    rng = random.Random(seed); thetas = []
    for _ in range(entries):
        m = 0.0; v = 1.0 + mean * mean; th = 0.0
        for _ in range(sections):
            g = mean + rng.gauss(0.0, 1.0)
            m += (g - m) / 8.0; v += (g * g - v) / 256.0
            th += 2.0 ** -rate * m / math.sqrt(v)
            if leak is not None: th -= th * 2.0 ** -leak
        thetas.append(th)
    mu = sum(thetas) / entries
    return math.sqrt(sum(t * t for t in thetas) / entries), mu

print('PART 1, planted covectors (rate 6; 300 entries)')
r, _ = planted(6, None, 0.0, 300, 4096, 1)
print(f'  no leak, zero mean, 4,096 sections: rms {r:.4f}; the walk 2^-6 sqrt(4096) = {2.0 ** -6 * 64:.4f}')
for K in (6, 8):
    r, _ = planted(6, K, 0.0, 300, 8 * 2 ** K, 2)
    b = 1 - 2.0 ** -K; a = 7 / 8
    form = 2.0 ** -6 * math.sqrt((1 / 15) * (1 + a * b) / ((1 - a * b) * (1 - b * b)))
    print(f'  leak {K}, zero mean: rms {r:.4f}; the form {form:.4f}; its limit 2^-6 sqrt(2^{K}/2) = {2.0 ** -6 * math.sqrt(2 ** K / 2):.4f}')
for c in (0.1, 0.5):
    _, mu = planted(6, 8, c, 300, 8 * 2 ** 8, 3)
    print(f'  leak 8, covector mean {c} of its spread: entry mean {mu:.4f}; 2^(8-6) c / sqrt(1 + c^2) = {4 * c / math.sqrt(1 + c * c):.4f}')

print('PART 2, the line (the audit of November 18, section 1.6): rate 12, 3,000 sections a lap')
rate, per_lap = 12, 3000
walk = lambda lap: 2.0 ** -rate * math.sqrt(lap * per_lap)
print(f'  a free walk stands at {walk(10):.4f} at lap 10 and {walk(94):.4f} at lap 94; its power grows {walk(94) ** 2 - walk(10) ** 2:.5f}')
for name, r10, r94 in (('w', 0.129, 0.169), ('read', 0.128, 0.171), ('a', 0.120, 0.153), ('opening', 0.084, 0.165)):
    grown = r94 ** 2 - r10 ** 2
    print(f'  {name:8s} rms {r10:.3f} -> {r94:.3f}: power grows {grown:.5f}, {grown / (walk(94) ** 2 - walk(10) ** 2):.2f} of the walk\'s; '
          f'the growth is {grown / r94 ** 2:.2f} of the power at lap 94')

print('PART 3, a leak of K bits on the line (rate 12)')
for K in (12, 13, 14, 15, 16):
    rest = 2.0 ** -rate * math.sqrt(2 ** K / 2); e_fold = 2 ** K / per_lap
    settled = [1 - math.exp(-n * per_lap / 2 ** K) for n in (1, 2, 3)]
    print(f'  K={K}: an unrestrained entry rests at {rest:.4f} (the walk at lap 94: {walk(94):.4f}); a ratio of mean c holds {2 ** (K - rate)} c; '
          f'e-fold {e_fold:.1f} laps; settled after 1, 2, 3 laps: {settled[0]:.2f}, {settled[1]:.2f}, {settled[2]:.2f}')
