"""Score the terrain's held panel: by kind, the writes that begin with the whole reference answer and close it with a line feed
(`whole`), that begin with it (`opening`), and whose first symbol is the reference's. A ruler outside the machine.
Usage: score_terrain.py NAME=DIR [NAME=DIR ...] (DIR holds forms.written)."""
import sys, collections
for arg in sys.argv[1:]:
    name, d = arg.split('=', 1)
    by = collections.defaultdict(lambda: [0, 0, 0, 0])
    shown = collections.defaultdict(list)
    for line in open(f'{d}/forms.written', encoding='utf-8', errors='replace', newline='\n'):
        f = line.rstrip('\n').split('\t')
        if len(f) < 4:
            continue
        kind = f[0].split(':')[1]
        w, r = f[2], f[3]
        b = by[kind]
        b[0] += 1
        b[1] += int(w.startswith(r) and (w[len(r):].startswith('\\n') or len(w) == len(r)))
        b[2] += int(w.startswith(r))
        b[3] += int(w[:1] == r[:1])
        if len(shown[kind]) < 3:
            shown[kind].append(f'{f[1].split(chr(92) + "n")[-1]}{w[:len(r) + 4]!r} (want {r})')
    tot = [sum(b[i] for b in by.values()) for i in range(4)]
    print(f'TERRAIN_SCORE {name} whole {tot[1]}/{tot[0]} opening {tot[2]}/{tot[0]} first {tot[3]}/{tot[0]} | ' + ' '.join(f'{k} {b[1]}/{b[2]}/{b[3]} of {b[0]}' for k, b in by.items()))
    for k in by:
        print(f'  {name} {k}: ' + ' | '.join(shown[k]))
