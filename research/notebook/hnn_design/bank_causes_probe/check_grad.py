from common import *
from dumpio import parse_read, turn as dturn

rng = np.random.default_rng(7)
E0c, _ = __import__('bankprobe').E0()
pairs = order2(rng, 3)
decs = decisions(pairs, 'causal')[:6]
Cs, tg = counts_of(decs)
# placement validated against the exact dump: compare storage of request 0 of the dump
D0 = parse_read(DIR + '/read.dump')
r0 = D0['requests'][0]
C = candidates_counts(r0['request'], {}, 0)
z = storage_nodes(C, E0c)
from dumpio import to_complex
ex = [e for e in D0['exact'] if e['label'] == 's0']
err = max(np.abs(z[e['class']] - to_complex(e['storage'])).max() for e in ex)
print('storage vs exact dump (s0 candidates), largest |error|:', err)
C2 = candidates_counts(r0['request'], {0: r0['target'][0], 1: r0['target'][1]}, 2)
z2 = storage_nodes(C2, E0c)
ex2 = [e for e in D0['exact'] if e['label'] == 's2']
err2 = max(np.abs(z2[e['class']] - to_complex(e['storage'])).max() for e in ex2)
print('storage vs exact dump (s2 candidates), largest |error|:', err2)
a, _, mem, _ = joint_growth(to_turn(z2), P)
inside = all(float(e['members'][m][0]) - 1e-9 <= mem[e['class'], m] <= float(e['members'][m][1]) + 1e-9 for e in ex2 for m in range(4))
print('member growths inside exact enclosures (s2):', inside)

r = read(Cs, E0c, grad=True, want_face=True)
dE = (rng.standard_normal(E0c.shape) + 1j * rng.standard_normal(E0c.shape))
h = 1e-6
rp = read(Cs, E0c + h * dE, want_face=True)
rm = read(Cs, E0c - h * dE, want_face=True)
fd = (rp['a'] - rm['a']) / (2 * h)
an = inner(r['GE'], dE[None, None])
print('executed growth: largest relative |fd - analytic|:', np.abs(fd - an).max() / np.abs(fd).max())
fdA = (rp['A'] - rm['A']) / (2 * h)
anA = inner(r['GA'], dE[None, None])
print('face: largest relative |fd - analytic|:', np.abs(fdA - anA).max() / np.abs(fdA).max())
