"""The terrain's held panel (November 21): for each of the world's six kinds, 16 held expressions (FNV-1a of the expression's octets, mixed,
modulo 16 is zero, as `athena::world::held`), each after three unheld records of its kind, written `EXPRESSION = ANSWER` a line, the
held one's answer the reference. A ruler outside the machine; the world's law mirrored from crates/athena/src/world.rs."""
import random, sys
def fnv(b):
    h = 0xCBF29CE484222325
    for x in b:
        h = ((h ^ x) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return h
M = 0xFFFFFFFFFFFFFFFF
def mix(z):
    z = (z + 0x9E3779B97F4A7C15) & M
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M
    return z ^ (z >> 31)
held = lambda e: mix(fnv(e.encode())) % 16 == 0
rng = random.Random(20261121)
def number(most):
    w = 1 + rng.randrange(most)
    low = 0 if w == 1 else 10 ** (w - 1)
    return low + rng.randrange(10 ** w - low)
def draw(kind):
    if kind == 'sum':
        a, b = number(3), number(3); return f'{a} + {b}', str(a + b)
    if kind == 'difference':
        a, b = number(3), number(3); a, b = max(a, b), min(a, b); return f'{a} - {b}', str(a - b)
    if kind == 'product':
        a, b = number(2), number(1); return f'{a} * {b}', str(a * b)
    if kind == 'close':
        o = [rng.choice('([{') for _ in range(1 + rng.randrange(6))]
        return ' '.join(o), ' '.join({'(': ')', '[': ']', '{': '}'}[c] for c in reversed(o))
    d = [str(rng.randrange(10)) for _ in range(2 + rng.randrange(6))]
    return f'{kind} ' + ' '.join(d), ' '.join(d if kind == 'copy' else reversed(d))
out = []
for kind in ['sum', 'difference', 'product', 'close', 'copy', 'reverse']:
    n = 0
    while n < 16:
        e, a = draw(kind)
        if not held(e):
            continue
        ctx = []
        while len(ctx) < 3:
            ce, ca = draw(kind)
            if not held(ce):
                ctx.append(f'{ce} = {ca}')
        out.append(f'terrain:{kind}:h{n}\t' + '\\n'.join(ctx) + f'\\n{e} = \t{a}')
        n += 1
open(sys.argv[1], 'w').write('\n'.join(out) + '\n')
print(len(out), 'rows')
