"""e's spigot as a world (November 21; Brandon 06:10Z: the spigot, never the digits fed). Sale's spigot: e = 2 + 1/2!(1 + 1/3(1 + ...)),
the remainders a_i over the radices i = N..2 all one at the start (e's factorial-base expansion 2.111...). One decimal digit is a sweep
from i = N down to 2: x = 10 a_i + c, a_i <- x mod i, c <- x div i; the carry out of radix 2 is the digit. A record is one carry step,
`e R A C = Q M`: radix R, its remainder A before the step, the carry C in; Q the carry out, M the remainder kept. Three consecutive
steps of one sweep make a row, so each C is the step before's Q. Digits 1 to 120 are the world's training sweeps; 150 to 199 are held.
A ruler and a terrain outside the machine: rows for try-passes (read by two streams) and held panels for write-next."""
import random
N = 230
def sweeps(digits):
    a = [1] * (N + 1); out = []
    for k in range(1, digits + 1):
        c = 0; steps = []
        for i in range(N, 1, -1):
            x = 10 * a[i] + c; steps.append((i, a[i], c, x // i, x % i)); a[i] = x % i; c = x // i
        out.append((k, steps, c))
    return out
S = sweeps(200)
assert ''.join(str(d) for _, _, d in S[:10]) == '7182818284', 'e = 2.7182818284...'
rec = lambda s: f'e {s[0]} {s[1]} {s[2]} = {s[3]} {s[4]}'
r = random.Random(271828)
rows = []
for k, steps, d in S[:120]:
    for j in range(0, len(steps) - 2, 1):
        if r.random() < 0.25:
            a, b, c = steps[j:j + 3]
            rows.append(f'e:{k}:{a[0]}\t{rec(a)}\\n{rec(b)}\\n{" ".join(rec(c).split(" = ")[:1])} = \t{c[3]} {c[4]}\\n\tstrand')
r.shuffle(rows)
open('fit_e.tsv', 'w').write('\n'.join(rows) + '\n')
panel = []
for k, steps, d in S[149:199]:
    j = r.randrange(0, len(steps) - 3)
    a, b, c = steps[j:j + 3]
    panel.append(f'spigot:step:k{k}\t{rec(a)}\\n{rec(b)}\\ne {c[0]} {c[1]} {c[2]} = \t{c[3]} {c[4]}')
for k, steps, d in S[149:199]:
    a, b, c = steps[-3:]
    panel.append(f'spigot:digit:k{k}\t{rec(a)}\\n{rec(b)}\\ne {c[0]} {c[1]} {c[2]} = \t{c[3]} {c[4]}')
open('panel_e.tsv', 'w').write('\n'.join(panel) + '\n')
print(len(rows), 'rows;', len(panel), 'held prompts;', rows[0][:120]); print(panel[-1][:140])
