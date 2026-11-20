"""A ruler for the composition of a writer's writes (the lead, November 20; first read inline on November 19, receipts 19:15 UTC): of the
word pairs and triples a write forms, the share attested in its slice's training text.

For each named panel (NAME=FORMS, FORMS a `write-next` output's `forms.written`: label, prompt, write, reference, tab-separated, `\\n`
escaped), a write's words are its maximal runs of ASCII letters, lowercased; its pairs and triples are consecutive words. A pair or triple is
attested when it stands, as whole words, in the first 16 MB of its slice's training documents (`DOCS_<slice>.bin` of the store, the label's
first field naming the slice), read as one stream of lowercased words. The reference continuations are read the same way, over their first
96 octets, as the receiver's scale; and by place, the share of the k-th pair attested along each write and reference. Outside the machine; counts only. Usage: python3 -I write_composition_ruler.py STORE NAME=FORMS [...]"""
import sys, os, re
store = sys.argv[1]
WORD = re.compile(rb'[A-Za-z]+')
streams = {}
def stream(slice_):
    if slice_ not in streams:
        with open(os.path.join(store, f'DOCS_{slice_}.bin'), 'rb') as f:
            raw = f.read(16 << 20)
        streams[slice_] = b' ' + b' '.join(m.group(0).lower() for m in WORD.finditer(raw)) + b' '
    return streams[slice_]
def grams(text, n):
    w = [m.group(0).lower() for m in WORD.finditer(text)]
    return [b' ' + b' '.join(w[i:i + n]) + b' ' for i in range(len(w) - n + 1)]
def rows(path):
    for line in open(path, 'rb'):
        f = line.rstrip(b'\n').split(b'\t')
        if len(f) >= 4:
            un = lambda b: b.replace(b'\\n', b'\n').replace(b'\\t', b'\t')
            yield f[0].decode().split(':')[0], un(f[2]), un(f[3])
def by_place(name, path, field, places=8):
    """The share of a write's k-th word pair attested, k = 1 to PLACES (the k-th pair after the prompt), so a reader sees whether a write
    holds its sense as it goes or loses it: a share that falls along the write is a drift of the writer's own context."""
    hits, tots = [0] * places, [0] * places
    for slice_, write, ref in rows(path):
        text = write if field == 'write' else ref
        s = stream(slice_)
        for k, g in enumerate(grams(text, 2)[:places]):
            tots[k] += 1; hits[k] += g in s
    print(f"COMPOSITION_BY_PLACE {name} {field}: " + ' '.join(f"{k + 1}:{hits[k] / max(1, tots[k]):.3f}({tots[k]})" for k in range(places)), flush=True)
def read(name, path, field):
    counts = {}
    for slice_, write, ref in rows(path):
        text = write if field == 'write' else ref[:96]
        s = stream(slice_)
        for n in (2, 3):
            g = grams(text, n)
            c = counts.setdefault((slice_, n), [0, 0])
            c[0] += len(g); c[1] += sum(1 for x in g if x in s)
    out = []
    for n in (2, 3):
        tot = sum(v[0] for (sl, m), v in counts.items() if m == n); hit = sum(v[1] for (sl, m), v in counts.items() if m == n)
        by = ' '.join(f"{sl} {v[1]}/{v[0]}" for (sl, m), v in sorted(counts.items()) if m == n)
        out.append(f"{'pairs' if n == 2 else 'triples'} {tot} attested {hit / max(1, tot):.3f} ({by})")
    print(f"COMPOSITION {name} {field}: " + ' | '.join(out), flush=True)
args = [a.split('=', 1) for a in sys.argv[2:]]
for name, path in args:
    read(name, path, 'write')
    by_place(name, path, 'write')
read('reference', args[0][1], 'reference')
by_place('reference', args[0][1], 'reference')
