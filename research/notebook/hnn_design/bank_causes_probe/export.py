"""Export a fitted E and a terrain's requests for the native re-read (`bank_causes -- native-release`):
`E rows cols`, then E's realified rows as exact binary fractions (the float values themselves; the
native harness rounds them to the source port's lattice), then one line a request,
`pair i <request> <target> float <float release> <released>`, the float release being
`fit.generate`'s lock iteration under the same placement law. Exterior harness, not a law.

usage: export.py <E.npy> <terrain> <seed> <count> <out> [rho]

With `rho`, the transport modulus is written (`rho <ρ>`, an exact binary fraction of the float)
and the float release reads the placement at it."""
from fractions import Fraction
from fit import *
import model

path, tname, seed, count, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
terrain = {'order2': order2, 'alternation': alternation, 'line': spectral_line}[tname]
if len(sys.argv) > 6:
    model.DECAY[0] = float(sys.argv[6])
E = np.load(path)
pairs = terrain(np.random.default_rng(seed), count)
real = np.empty((2 * D, CLASSES))
real[0::2] = E.real
real[1::2] = E.imag
lines = [f'E {2 * D} {CLASSES}']
for row in real:
    lines.append(' '.join(str(Fraction(float(x))) for x in row))
if model.DECAY[0] != 1.0:
    lines.append(f'rho {Fraction(model.DECAY[0])}')
for i, (req, tgt) in enumerate(pairs):
    sec, ok = generate(req, E)
    lines.append(f"pair {i} {','.join(map(str, req))} {','.join(map(str, tgt))} float "
                 f"{','.join(map(str, sec))} {int(ok)}")
with open(out, 'w') as f:
    f.write('\n'.join(lines) + '\n')
print(f'export: {count} requests of {tname} at seed {seed}; E largest |entry| in '
      f'{log2cell(float(np.abs(real).max()))}')
