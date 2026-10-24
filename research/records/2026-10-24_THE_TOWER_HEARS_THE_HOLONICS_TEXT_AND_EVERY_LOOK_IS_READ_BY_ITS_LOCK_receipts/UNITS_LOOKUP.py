"""The units crossing's share of the input tension: the energy a per-(op, a0, b0) lookup removes from
the input covector at B, beside the training text's within-class tension energy (from the slice's
moments, scaled to the whole text). An exterior reading."""
import collections, importlib.util, sys
sys.path.insert(0, '../../tools')
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
lines = open('situated/slice16.moments').read().split('\n')
head = lines[0]; dims = 128; w = 64
cells = int(head.split('cells=')[1].split()[0])
yy = [int(v) for v in lines[1].split()[1].split(',')]
# upper triangle of 64x64 row by row: diagonal entries at offsets
tr, k = 0, 0
for i in range(w):
    tr += yy[k]; k += w - i
cls = 0
for l in lines[2:]:
    if not l.startswith('CLASS'): continue
    f = dict(x.split('=', 1) for x in l.split()[2:])
    n = int(f['n']); y = [int(v) for v in f['y'].split(',')]
    cls += sum(v * v for v in y) / n
within_slice = tr - cls
per_cell = within_slice / cells
print(f"slice cells={cells} tr Y per cell={tr / cells / 2**48:.6f} within-class per cell={per_cell / 2**48:.6f}")
train_cells = 1789108
W = per_cell * train_cells
for role in "ABEU":
    groups, cl = collections.defaultdict(list), collections.defaultdict(list)
    tot = 0
    for c in range(8):
        text = open(f'modes/block{c}.txt', 'rb').read()
        roles, info = tm.probe_roles(text)
        for l in open(f'situated/cov/block{c}.txt'):
            p = l.split(); i = int(p[1]); r = roles.get(i + 1, ())
            if role not in r: continue
            y = [int(v) for v in p[3:]]
            op, a0, b0, c0 = info[i + 1]
            groups[(op, a0, b0, int(p[2]))].append(y); cl[int(p[2])].append(y)
    def mean(ys): return [sum(col) / len(ys) for col in zip(*ys)]
    cm = {u: mean(ys) for u, ys in cl.items()}
    within = sum(sum((a - b) ** 2 for a, b in zip(y, cm[u])) for u, ys in cl.items() for y in ys)
    cross = sum(len(ys) * sum((a - b) ** 2 for a, b in zip(mean(ys), cm[key[3]])) for key, ys in groups.items())
    n = sum(len(v) for v in cl.values())
    print(f"{role}: cells={n} within-class energy per cell={within / n / 2**48:.6f} lookup-removable share of it={cross / within:.3f} "
          f"lookup-removable share of the training text's within-class tension={1000 * cross / W:.2f} per mille")
