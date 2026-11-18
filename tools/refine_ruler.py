"""A ruler's writer: a written panel refined by a field's reading of a place between known neighbours (the level's design record of
November 17, its §14; guess G-V10). No part and no training: it reads a saved state through `athena host complete-language read-tension`,
which opens each named place alone with the rest of its record known and writes that place's whole face.

A sweep reopens every place of each written run alone, its neighbours as the draft has them, one colour of places at a time (a place's
index modulo COLOURS), and redraws it from the face by a keyed draw (the key is the row's label, the sweep and the place; the density is
the face's own, with no sharpening). After each sweep the runs are written as `OUT/sweep_K.written` (label, prompt, run, reference).

The symbols' classes are read off a dump the same command made: at a place whose symbol is known, the class is the one whose code on
the face equals the place's code.

Usage: python3 -I refine_ruler.py DRAFT.written MAP_DUMP MAP_ROWS.tsv OUT SWEEPS COLOURS -- BIN UNITS KEYS CODEC STATE
(the five paths after `--` are the command's; their digests are taken here). Outside the machine; the writes derive from private
text and stay out of the repository."""
import sys, os, subprocess, hashlib, shutil
import numpy as np

draft, map_dump, map_rows, out, sweeps, colours = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6])
assert sys.argv[7] == '--'
binary, units, keys, codec, state = sys.argv[8:13]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
esc = lambda s: s.replace('\n', '\\n'); unesc = lambda s: s.replace('\\n', '\n')

def dump_faces(d):
    """The dump's places in order: (label, place, code) and each place's face (the code of every class, on 2^-20 bits)."""
    dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
    ticks = int(dims['ticks'])
    rows = []
    for i, l in enumerate(open(d + '/rows.tsv', encoding='utf-8')):
        lab, place, tick, c = l.rstrip('\n').split('\t')[:4]
        if int(tick) == 0:
            rows.append((lab, int(place), int(c)))
    faces = np.fromfile(d + '/faces.i64', dtype=np.int64).reshape(len(rows), -1)
    return rows, faces

# The symbols' classes, from a dump of places whose symbols are known.
runs = {}
for l in open(map_rows, encoding='utf-8'):
    lab, _, r = l.rstrip('\n').split('\t')[:3]
    runs[lab] = unesc(r)
rows, faces = dump_faces(map_dump)
votes = {}
for (lab, place, code), f in zip(rows, faces):
    hit = np.nonzero(f == code)[0]
    if len(hit) == 1:
        votes.setdefault(runs[lab][place], {}).setdefault(int(hit[0]), 0)
        votes[runs[lab][place]][int(hit[0])] += 1
class_of = {c: max(v, key=v.get) for c, v in votes.items()}
sym_of = {k: c for c, k in class_of.items()}
assert len(sym_of) == len(class_of), "two symbols on one class"
known = np.array(sorted(sym_of)); print(f"REFINE symbols mapped {len(class_of)} of an alphabet of {faces.shape[1]}", flush=True)

panel = []
for l in open(draft, encoding='utf-8'):
    lab, prompt, run, ref = l.rstrip('\n').split('\t')[:4]
    panel.append([lab, unesc(prompt), list(unesc(run)), ref])
os.makedirs(out, exist_ok=False)
env = {'HOME': os.environ.get('HOME', ''), 'PATH': os.environ.get('PATH', ''), 'RAYON_NUM_THREADS': os.environ.get('RAYON_NUM_THREADS', '16')}
digests = [sha(units), sha(keys), sha(codec), sha(state)]
changed_total = 0
for sweep in range(1, sweeps + 1):
    changed = 0; mass_known = []; news = []
    for colour in range(colours):
        table = out + f'/t_{sweep}_{colour}.tsv'
        with open(table, 'w', encoding='utf-8') as g:
            for lab, prompt, run, _ in panel:
                places = [j for j in range(len(run)) if j % colours == colour]
                g.write(f"{lab}\t{esc(prompt)}\t{esc(''.join(run))}\t{','.join(map(str, places))}\n")
        d = out + f'/d_{sweep}_{colour}'
        res = subprocess.run([binary, 'host', 'complete-language', 'read-tension', units, digests[0], keys, digests[1], codec, digests[2], table, sha(table), state, digests[3], d],
                             env=env, capture_output=True, text=True)
        if res.returncode != 0:
            sys.exit('REFINE the reading failed: ' + (res.stdout + res.stderr)[-400:])
        rows, faces = dump_faces(d)
        by_label = {p[0]: p for p in panel}
        for (lab, place, code), f in zip(rows, faces):
            p = np.exp2(-(f[known] - f[known].min()) / float(1 << 20))
            total_all = np.exp2(-(f - f[known].min()) / float(1 << 20)).sum()
            mass_known.append(p.sum() / total_all); p /= p.sum()
            u = int.from_bytes(hashlib.sha256(f"{lab}:{sweep}:{place}".encode()).digest()[:8], 'big') / 2.0 ** 64
            k = int(np.searchsorted(np.cumsum(p), u)); k = min(k, len(known) - 1)
            new = sym_of[int(known[k])]
            run = by_label[lab][2]
            news.append(-np.log(p[list(known).index(class_of[run[place]])]) if run[place] in class_of else float('nan'))
            if new != run[place]:
                changed += 1
            run[place] = new
        shutil.rmtree(d); os.remove(table)
    changed_total += changed
    path = out + f'/sweep_{sweep}.written'
    with open(path, 'w', encoding='utf-8') as g:
        for lab, prompt, run, ref in panel:
            g.write(f"{lab}\t{esc(prompt)}\t{esc(''.join(run))}\t{ref}\n")
    places = sum(len(p[2]) for p in panel)
    print(f"REFINE sweep={sweep} places={places} redrawn_to_another_symbol={changed} ({100 * changed / places:.1f}%) the standing symbol's code before its redraw {np.nanmean(news):.3f} nats  mass on mapped symbols {np.mean(mass_known):.4f}  wrote {path}", flush=True)
print(f"REFINE done sweeps={sweeps} colours={colours}")
