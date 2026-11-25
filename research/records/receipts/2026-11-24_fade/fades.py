"""Each turned ring's fade in a state that holds them (hnn-field-v14s): the last TURNED entries of the fine material line, with the
lattice's rest where a lattice is set, in thousandths of an octave of the skin's fade (ell on 2^-24). A ruler; reads only."""
import sys
def fades(path, turned=16):
    lines = open(path).read().split('\n')
    head = lines[1].split(' ')
    if head[0] != 'hnn-field-v14s':
        return None
    mat = lines[2].split(' ')
    at = len(mat) - turned
    vals = [int(v) for v in mat[at:]]
    for l in lines:
        if l.startswith('lattice_rest '):
            r = l.split(' ')[1:]
            vals = [v + int(r[at + i]) for i, v in enumerate(vals)]
    return [round(v * 1000 / 2**24) for v in vals]
for p in sys.argv[1:]:
    f = fades(p)
    PERIODS = [2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024, 2187, 4096, 6561]  # her turned rings, slot order (found-fade)
    print('FADES', p.split('/')[-2] + '/' + p.split('/')[-1], 'none' if f is None else ' '.join(f'{n}:{v}' for n, v in zip(PERIODS, f) if v))
