"""A ruler's arithmetic: a part the code reads as a ratio to its own power, under the deposit's step and the store's leak.

A part theta of N entries is read only through theta / |theta|, so its covector is orthogonal to it and falls as 1 / |theta|.
The deposit steps each entry by 2^(-rate) m / sqrt(v), m and v the covector's two moments at 2^(-3) and 2^(-8) (THE_ENGINE, the
deposit's row), and the leak takes 2^(-K) of the entry after the step (Learner::relax).

The statements read here (floats; a ruler, outside the machine, entering no law):
  LENGTH  with no leak the part's power an entry grows by c 2^(-2 rate) a section, c = 1 on a white covector whatever its size,
          while its direction is held: every step orthogonal to the part lengthens it, and the moment's memory carries each
          step's covector onto the part the step has since moved. The net travel across the part stays far under a free walk's.
  TURN    the part turns by 2^(-rate) rms(ratio) / rms(theta) a section: its rate over its own size.
  REST    with a leak of K bits it rests at rms 2^(-rate) sqrt(c 2^(K - 1)), where it turns by rms(ratio) 2^(-(K - 1)/2) / sqrt(c)
          a section whatever its rate.
Part 1 plants them. Part 2 reads the audit's figures of November 18 (section 1.6: root mean squares by family at lap 10 and
lap 94, the line at 2^(-12), 3,000 sections a lap) as a c, and gives the leak at which each family's present size is its rest.
Part 3 prints, for the line's rate, the rest size and the turn at rest by K against the present turn. Part 4 reads the paces'
growth as a mean ratio and gives its rest under a leak. Part 5 set the scale reads of November 11 beside the law by their summary figures and is withdrawn: scale_c.py reads them by block. Usage: length.py"""
import math
import numpy as np


def plant(rate, leak, hold, entries, sections, lap, seed, start=0.5):
    """A part read as a ratio: covector (1/rms) P_perp(hold (theta_hat - u) + xi), xi white. Returns the growth of its power an
    entry over c's unit, the net travel a lap over a free walk's lap, the mean cosine of successive lap travels, the cosine of
    a lap's travel with the part, the end rms and the turn a section at the end."""
    rng = np.random.default_rng(seed)
    u = rng.standard_normal(entries); u /= np.sqrt(np.mean(u * u))
    th = start * u.copy()
    m = np.zeros(entries); v = np.ones(entries) / (start * start)
    eta = 2.0 ** -rate
    ends = [th.copy()]; p0 = float(np.mean(th * th)); step_rms = 0.0
    for t in range(sections):
        rms = math.sqrt(float(np.mean(th * th)))
        hat = th / rms
        g = hold * (hat - u) + rng.standard_normal(entries)
        g -= hat * float(np.mean(g * hat))
        g /= rms
        m += (g - m) / 8.0; v += (g * g - v) / 256.0
        s = -eta * m / np.sqrt(v)
        th += s
        if leak is not None: th -= th * 2.0 ** -leak
        if (t + 1) % lap == 0: ends.append(th.copy())
        if t >= sections - lap: step_rms += float(np.mean(s * s))
    p1 = float(np.mean(th * th))
    travels = [b - a for a, b in zip(ends, ends[1:])]
    net = np.mean([math.sqrt(float(np.mean(d * d))) for d in travels]) / (eta * math.sqrt(lap))
    cos = np.mean([float(np.sum(a * b)) / math.sqrt(float(np.sum(a * a)) * float(np.sum(b * b))) for a, b in zip(travels, travels[1:])])
    along = np.mean([float(np.sum(d * e)) / math.sqrt(float(np.sum(d * d)) * float(np.sum(e * e))) for d, e in zip(travels, ends)])
    end = math.sqrt(p1)
    return (p1 - p0) / (eta * eta * sections), net, cos, along, end, math.sqrt(step_rms / lap) / end


print('PART 1, a planted part read as a ratio (rate 8; 1,024 entries; laps of 3,000 sections)')
for hold in (0.0, 0.5, 2.0, 8.0):
    c, net, cos, along, end, turn = plant(8, None, hold, 1024, 60000, 3000, 7)
    print(f'LENGTH hold={hold:3.1f}  c={c:5.3f} (1 on a white covector)  net travel a lap over a free walk\'s={net:5.3f}  '
          f'cosine of successive laps={cos:+5.3f}  of a lap with the part={along:+5.3f}')
for K in (8, 10, 12):
    c, net, cos, along, end, turn = plant(8, K, 2.0, 1024, 16 * 2 ** K, 1024, 11, start=2.0 ** -8 * math.sqrt(2.0 ** (K - 1)))
    rest = 2.0 ** -8 * math.sqrt(2.0 ** (K - 1))
    print(f'REST   leak={K:2d}  rms={end:6.4f}  2^(-rate) sqrt(2^(K-1))={rest:6.4f}  ratio={end / rest:5.3f} (sqrt c)  '
          f'turn a section={turn:7.5f}  2^(-(K-1)/2)/sqrt(15)={2.0 ** (-(K - 1) / 2) / math.sqrt(15):7.5f}')

print('PART 2, the line (the audit of November 18, section 1.6): rate 12, 3,000 sections a lap, lap 10 to lap 94')
rate, lap, sections = 12, 3000, 84 * 3000
unit = 2.0 ** (-2 * rate) * sections
for name, a, b in (('w', 0.129, 0.169), ('read', 0.128, 0.171), ('a', 0.120, 0.153), ('opening', 0.084, 0.165)):
    c = (b * b - a * a) / unit
    K = 1 + 2 * math.log2(b * 2.0 ** rate)
    eps = 1000 * lap * 2.0 ** (-2 * rate) / (2 * b * b)
    turn = 2.0 ** -rate / math.sqrt(15) / b
    print(f'LINE {name:8s} rms {a:.3f} -> {b:.3f}  c={c:4.2f}  lengthening a lap at lap 94, parts a thousand: {eps * c:4.2f} at this c, '
          f'{eps:4.2f} at c=1, {eps / 15:4.2f} at c=1/15  turn a section={turn:.6f}  rests at its present size under K={K:5.2f}')
step = 2.0 ** -rate * math.sqrt(lap)
print(f'LINE a free walk\'s lap: {step:.5f}, {100 * step / 0.169:.1f}% of 0.169 and {100 * step / 0.129:.1f}% of 0.129; '
      f'a walk of unlike sections at the ratio\'s own rms: {step / math.sqrt(15):.5f}, {100 * step / math.sqrt(15) / 0.169:.1f}% of 0.169')

print('PART 3, a part read as a ratio under a leak of K bits (rate 12, c = 1; present turn of a part of rms 0.169 beside)')
now = 2.0 ** -12 / math.sqrt(15) / 0.169
for K in (12, 14, 16, 18, 20, 22, 24):
    rest = 2.0 ** -12 * math.sqrt(2.0 ** (K - 1)); turn = 2.0 ** (-(K - 1) / 2) / math.sqrt(15)
    print(f'LEAK K={K:2d}  rest rms={rest:6.4f}  turn at rest={turn:.6f}  over the present turn={turn / now:6.2f}  '
          f'settles by e in {2.0 ** K / lap / 2:7.1f} laps (its power)  an entry under {2.0 ** (K - 1 - 24):.5f} stands (grain 2^-24), '
          f'under {2.0 ** (K - 1 - 16):.4f} (grain 2^-16)')

print('PART 4, the paces (the audit: maximum 12.9 -> 19.9, rms 2.50 -> 3.77, lap 10 to lap 94)')
for name, a, b in (('maximum', 12.9, 19.9), ('rms', 2.50, 3.77)):
    ratio = (b - a) / sections * 2.0 ** rate
    print(f'PACE {name:8s} mean ratio a section={ratio:.4f}  its rest 2^(K - rate) ratio at K=18, 19, 20: '
          f'{2.0 ** 6 * ratio:5.1f} {2.0 ** 7 * ratio:5.1f} {2.0 ** 8 * ratio:5.1f}')

print('PART 5, WITHDRAWN (G-L0 (c), GUESS.txt): the second lane\'s charts were charging, c 4 to 8 (scale_c_floor_means.txt), so the figures below take a push for the step\'s own lengthening')
print(f'RATIO forms at 0.23 and 0.14 of the first lane\'s lengthen {1 / 0.23 ** 2:.0f} to {1 / 0.14 ** 2:.0f} times as fast '
      f'(read: 18 to 24 parts a thousand a lap against under 1)')
x = 1.018 ** 2 - 1
for f in (4, 8, 16):
    laps = [1000 * (math.sqrt((1 + (k + 1) * x * f * f) / (1 + k * x * f * f)) - 1) for k in range(6)]
    print(f'RAISED rate x{f:2d}: lengthening by lap, parts a thousand, from the floor\'s 18 alone: ' + ' '.join(f'{v:5.0f}' for v in laps))
print('RAISED read on November 11: 71 at four times the rate and 110 at eight; 184 then 107 on a raised chart (the laps of those reads not recorded)')
