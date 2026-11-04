"""§16.42: each lap's step prices against their own spread, from sections.tsv (main52's FIELD_SECTION rows).

Per section, in millionths of a bit a site: the step's own first-order change `a` (predicted_micro), its own curvature
`b = change - a` (a step that stood at full size: deposited, no halving), and the transfer `t` the next section reads of
that step. Per lap: means, standard errors, the curvature's per-section spread, and the steps priced of those taken.
Per octave: the transfer split as `t = s(g_n.d) + s^2 h_n` from the two arms at 2^-11 and 2^-12 that opened on one state,
and the next section's first-order change over the own first-order change.
"""
import csv, math, sys
from collections import defaultdict

rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
laps = defaultdict(lambda: {'a': [], 'b': [], 't': [], 'rate': None, 'taken': 0})
prior = {}
for r in rows:
    key = (r['arm'], int(r['lap']))
    L = laps[key]
    L['rate'] = int(r['rate'])
    L['taken'] += 1
    if r['transfer_micro'] != '-' and prior.get(r['arm']) is not None:
        L['t'].append(int(r['transfer_micro'])); L['b'].append(prior[r['arm']])
    if r['predicted_micro'] != '-':
        L['a'].append(int(r['predicted_micro']))
    full = r['predicted_micro'] != '-' and r['deposited'] == 'true' and r['halvings'] == '0'
    prior[r['arm']] = int(r['change_micro']) - int(r['predicted_micro']) if full else None

def stats(x):
    n = len(x); mu = sum(x) / n; sd = math.sqrt(sum((v - mu) ** 2 for v in x) / (n - 1))
    return mu, sd / math.sqrt(n), sd

print("arm\tlap\trate\tpriced/taken\ta\tt\tt_se\tb\tb_se\tb_sd\tz_t\tz_b")
octave = defaultdict(lambda: {'a': [], 't': [], 'b': [], 'bsd': []})
for (arm, lap), L in sorted(laps.items(), key=lambda kv: (['rate11', 'rate12', 'transfer', 'seg1'].index(kv[0][0]), kv[0][1])):
    a, _, _ = stats(L['a']); t, tse, _ = stats(L['t']); b, bse, bsd = stats(L['b'])
    print(f"{arm}\t{lap}\t{L['rate']}\t{len(L['t'])}/{L['taken']}\t{a:.0f}\t{t:.1f}\t{tse:.1f}\t{b:.1f}\t{bse:.1f}\t{bsd:.0f}\t{t/tse:.1f}\t{b/bse:.1f}")
    if not (arm == 'transfer' and lap == 0):  # the transfer arm's first lap is rate11's lap 0 again
        O = octave[L['rate']]; O['a'] += L['a']; O['t'] += L['t']; O['b'] += L['b']; O['bsd'].append(bsd)

print("\nrate\tsections\ta\tt\tt_se\tb\tb_se\tmean per-lap b_sd")
for k in sorted(octave):
    O = octave[k]; a, _, _ = stats(O['a']); t, tse, _ = stats(O['t']); b, bse, _ = stats(O['b'])
    print(f"{k}\t{len(O['t'])}\t{a:.0f}\t{t:.1f}\t{tse:.1f}\t{b:.1f}\t{bse:.1f}\t{sum(O['bsd'])/len(O['bsd']):.0f}")

# t = s*(g_n.d) + s^2*h_n: at 2^-11 the two parts are A + B, at 2^-12 A/2 + B/4 (one state, the same steps' law).
t11, se11 = stats(octave[11]['t'])[:2]; t12, se12 = stats(octave[12]['t'])[:2]; a11 = stats(octave[11]['a'])[0]
A = 4 * t12 - t11  # A + B = t11 and A/2 + B/4 = t12, so 4 t12 - t11 = A
A_se = math.sqrt((4 * se12) ** 2 + se11 ** 2)
print(f"\nfirst-order transfer at 2^-11: A = 4 t12 - t11 = {A:.0f} ± {A_se:.0f}; curvature part t11 - A = {t11 - A:.0f}; own a = {a11:.0f}; A/a = {A/a11:.4f} ± {A_se/abs(a11):.4f}")
for k in (16, 17):
    t, tse, _ = stats(octave[k]['t']); a = stats(octave[k]['a'])[0]; curv = (t11 - A) / 4 ** (k - 11)
    print(f"2^-{k}: t = {t:.1f} ± {tse:.1f}, curvature part from 2^-11 scaled {curv:.2f}, first-order {t - curv:.1f}; own a = {a:.0f}; ratio {(t - curv)/a:.4f} ± {tse/abs(a):.4f}")
