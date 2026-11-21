"""Score the deterministic-logic panel: for each prompt and state, the draws (of 8) whose write begins with the reference continuation (its
first min(6, len) characters, as the panel of November 19 was scored), the draws whose first character is the reference's, and the commonest
write's opening. Outside the machine; a ruler on the writes."""
import sys, os, collections
O = os.path.dirname(os.path.abspath(__file__))
states = sys.argv[1:] or ['L17', 'L71', 'L75']
order = []
res = {}
for n in states:
    p = f'{O}/logic_{n}/forms.written'
    if not os.path.exists(p):
        continue
    for line in open(p, encoding='utf-8', errors='replace', newline='\n'):
        f = line.rstrip('\n').split('\t')
        if len(f) < 4:
            continue
        name = f[0].split(':')[1]
        if name not in order:
            order.append(name)
        w, r = f[2], f[3]
        k = min(6, len(r.strip()))
        d = res.setdefault((n, name), {'hit': 0, 'first': 0, 'tot': 0, 'writes': collections.Counter(), 'ref': r, 'prompt': f[1]})
        d['tot'] += 1
        d['hit'] += int(w.startswith(r[:k])) if k else 0
        d['first'] += int(w[:1] == r[:1])
        d['writes'][w[:24]] += 1
for n in states:
    tot = sum(res[(n, x)]['hit'] for x in order if (n, x) in res)
    first = sum(res[(n, x)]['first'] for x in order if (n, x) in res)
    rows = sum(res[(n, x)]['tot'] for x in order if (n, x) in res)
    print(f'LOGIC_SCORE {n} whole_opening {tot}/{rows} first_character {first}/{rows} | ' + ' '.join(f"{x} {res[(n, x)]['hit']}/{res[(n, x)]['tot']}" for x in order if (n, x) in res))
for x in order:
    d0 = next(res[(n, x)] for n in states if (n, x) in res)
    print(f'\n## {x}: prompt ...{d0["prompt"][-40:]!r} expected {d0["ref"]!r}')
    for n in states:
        if (n, x) in res:
            d = res[(n, x)]
            top = d['writes'].most_common(2)
            print(f'  {n}: {d["hit"]}/8 opening, {d["first"]}/8 first char; commonest: ' + ' | '.join(f'{w!r} x{c}' for w, c in top))
