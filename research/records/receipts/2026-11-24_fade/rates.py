"""Each paced head's fade rates in a state whose classes fade at their own rates (hnn-field-v14s, fade word 2 or 3): the last
paced x (A + 1) entries of the fine material line, with the lattice's rest, in thousandths of a stride (rate on 2^-24), the space's and
the line feed's and the five largest in magnitude, each named by its byte. A ruler; reads only. Usage: rates.py CODEC STATE [STATE ...]"""
import sys
codec = open(sys.argv[1]).read().split('\n')[1].split()
name = lambda c: 'unres' if c >= len(codec) else repr(chr(int(codec[c]))) if 32 <= int(codec[c]) < 127 or int(codec[c]) in (9, 10, 13) else f'0x{int(codec[c]):02x}'
for p in sys.argv[2:]:
    lines = open(p).read().split('\n')
    head = lines[1].split(' ')
    if head[0] != 'hnn-field-v14s' or head[23] not in ('2', '3'):
        print('RATES', p.split('/')[-2] + '/' + p.split('/')[-1], 'none'); continue
    a = int(head[1]) + 1
    mat = lines[2].split(' ')
    rest = next((l.split(' ')[1:] for l in lines if l.startswith('lattice_rest ')), None)
    paced = 2
    at = len(mat) - paced * a
    vals = [int(mat[at + i]) + (int(rest[at + i]) if rest else 0) for i in range(paced * a)]
    out = []
    for h in range(paced):
        row = vals[h * a:(h + 1) * a]
        ms = lambda v: round(v * 1000 / 2**24)
        top = sorted(range(a), key=lambda c: -abs(row[c]))[:5]
        out.append(f'head{h} space={ms(row[4])} lf={ms(row[1])} top=' + ','.join(f'{name(c)}:{ms(row[c])}' for c in top))
    print('RATES', p.split('/')[-2] + '/' + p.split('/')[-1], ' | '.join(out))
