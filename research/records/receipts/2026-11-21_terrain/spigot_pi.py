"""pi's spigot as a world (November 21; Brandon 06:10Z). Rabinowitz-Wagon: pi = 2 + 1/3(2 + 2/5(2 + 3/7(2 + ...))), the remainders a_i
over the mixed radices i/(2i-1) all two at the start. One sweep from i = L down to 1: x = 10 a_i + q i, a_i <- x mod (2i-1),
q <- x div (2i-1); then the predigit q div 10 enters a short buffer of nines (the spigot's own carry into digits already released).
A record is one carry step, `pi I A Q = Q' M`: the place I, its remainder A, the carry in Q; the carry out and the remainder kept.
Three consecutive steps a row. Sweeps 1 to 120 are training, 150 to 199 held. A ruler and a terrain outside the machine."""
import random
D = 200; L = 10 * D // 3 + 1
def sweeps():
    a = [2] * (L + 1); out = []; digits = []; nines = 0; pre = None
    for k in range(1, D + 1):
        q = 0; steps = []
        for i in range(L, 0, -1):
            x = 10 * a[i] + q * i; d = 2 * i - 1
            steps.append((i, a[i], q, x // d, x % d)); a[i] = x % d; q = x // d
        a[1] = q % 10; q //= 10
        if q == 9: nines += 1
        elif q == 10:
            digits.append((pre or 0) + 1); digits += [0] * nines; pre = 0; nines = 0
        else:
            if pre is not None: digits.append(pre)
            digits += [9] * nines; pre = q; nines = 0
        out.append((k, steps))
    return out, digits
S, digits = sweeps()
assert ''.join(map(str, digits[:10])) == '3141592653', ''.join(map(str, digits[:10]))
rec = lambda s: f'pi {s[0]} {s[1]} {s[2]} = {s[3]} {s[4]}'
r = random.Random(314159)
rows = []
for k, steps in S[:120]:
    for j in range(len(steps) - 2):
        if r.random() < 0.085:
            a, b, c = steps[j:j + 3]
            rows.append(f'pi:{k}:{a[0]}\t{rec(a)}\\n{rec(b)}\\npi {c[0]} {c[1]} {c[2]} = \t{c[3]} {c[4]}\\n\tstrand')
r.shuffle(rows)
open('fit_pi.tsv', 'w').write('\n'.join(rows) + '\n')
panel = []
for k, steps in S[149:199]:
    j = r.randrange(0, len(steps) - 3); a, b, c = steps[j:j + 3]
    panel.append(f'spigot:step:k{k}\t{rec(a)}\\n{rec(b)}\\npi {c[0]} {c[1]} {c[2]} = \t{c[3]} {c[4]}')
for k, steps in S[149:199]:
    a, b, c = steps[-3:]
    panel.append(f'spigot:last:k{k}\t{rec(a)}\\n{rec(b)}\\npi {c[0]} {c[1]} {c[2]} = \t{c[3]} {c[4]}')
open('panel_pi.tsv', 'w').write('\n'.join(panel) + '\n')
print(len(rows), 'rows;', len(panel), 'held;', rows[0][:110])
