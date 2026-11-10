"""Census of declared widths at a git ref (read only).

Usage: python3 -I census.py REPO REF OUTDIR

Lists every integer constant of the Rust crates and every #define of the CUDA kernels, with its value (simple
expressions evaluated), owner, doc tag, and its uses by word match across crates/ (the declaration excluded), then
joins the hand classification of the live field path (lap 14) from classes.tsv beside this script.
"""
import collections, os, re, subprocess, sys

repo, ref, outdir = sys.argv[1:4]
here = os.path.dirname(os.path.abspath(__file__))

def git(*a):
    return subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, check=True).stdout

files = [f for f in git('ls-tree', '-r', '--name-only', ref, '--', 'crates').split('\n') if f.endswith(('.rs', '.cu', '.cuh'))]
src = {f: git('show', f'{ref}:{f}') for f in files}

RUST = re.compile(r'^\s*(pub(?:\([a-z]+\))?\s+)?const\s+([A-Z][A-Z0-9_]*)\s*:\s*(u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)\s*=\s*(.+?);')
CUDA = re.compile(r'^\s*#define\s+([A-Z][A-Z0-9_]*)\s+(\(?[-0-9A-Za-z_ ()*+<>]+\)?)\s*(?://.*)?$')
decls = []
for f in files:
    lines = src[f].split('\n')
    for i, l in enumerate(lines):
        m = RUST.match(l) if f.endswith('.rs') else CUDA.match(l)
        if not m:
            continue
        if f.endswith('.rs'):
            vis, name, ty, expr = m.group(1) or '', m.group(2), m.group(3), m.group(4).strip()
        else:
            vis, name, ty, expr = 'define', m.group(1), '', m.group(2).strip()
            if not re.search(r'\d', expr) and not re.search(r'[A-Z]{2}', expr):
                continue
        doc = []
        j = i - 1
        while j >= 0 and lines[j].lstrip().startswith(('///', '//')) and not lines[j].lstrip().startswith('//!'):
            doc.insert(0, re.sub(r'^\s*///?\s?', '', lines[j]))
            j -= 1
        doc = ' '.join(doc)
        tag = 'agent-inferred' if 'agent-inferred' in doc else ('measurement' if '[measurement' in doc else ('definition' if '[definition' in doc else ''))
        test = '/tests' in f or f.endswith('tests.rs') or '/tests/' in f
        decls.append(dict(file=f, line=i + 1, name=name, ty=ty, vis=vis.strip(), expr=expr, doc=doc[:300], tag=tag, test=test))

# Evaluate simple expressions, same-file names first.
byname = collections.defaultdict(list)
for d in decls:
    byname[d['name']].append(d)
KNOWN = {'i128::BITS': 128, 'u64::BITS': 64, 'u32::BITS': 32, 'usize::BITS': 64, 'u32::MAX': 2**32 - 1, 'u64::MAX': 2**64 - 1}
def value(d, depth=0):
    if 'value' in d:
        return d['value']
    e = d['expr']
    for k, v in KNOWN.items():
        e = e.replace(k, str(v))
    e = re.sub(r'(\d)_(\d)', r'\1\2', e)
    e = re.sub(r'\b(\d+)(u8|u16|u32|u64|u128|usize|i32|i64|i128|ull|u)\b', r'\1', e)
    e = e.replace('as u32', '').replace('as u64', '').replace('as usize', '').replace('as i64', '').replace('as i128', '')
    def sub(m):
        n = m.group(0)
        if depth > 6:
            raise ValueError
        # Rust's `use super::*`: the same file, then the parent module's file, then the grandparent's, then any.
        f = d['file']
        order = [f]
        parts = f[:-3].split('/') if f.endswith('.rs') else []
        for k in (1, 2):
            if len(parts) > k:
                order.append('/'.join(parts[:-k]) + '.rs')
        cands = []
        for o in order:
            cands += [c for c in byname.get(n, []) if c['file'] == o]
        cands = cands or byname.get(n, [])
        if not cands:
            raise ValueError
        return str(value(cands[0], depth + 1))
    try:
        e = re.sub(r'\b0x([0-9A-Fa-f]+)\b', lambda m: str(int(m.group(1), 16)), e)
        e2 = re.sub(r'\b[A-Z][A-Z0-9_]*\b', sub, e)
        if not re.fullmatch(r'[0-9 ()*+\-<>/x]+', e2):
            raise ValueError
        v = eval(e2, {'__builtins__': {}})
    except Exception:
        v = None
    d['value'] = v
    return v
for d in decls:
    value(d)

# Uses by word match across crates (comments and the declaration line excluded), from one token index.
TOK = re.compile(r'[A-Z][A-Z0-9_]*')
index = collections.defaultdict(collections.Counter)
declared_at = {(d['file'], d['line']): d['name'] for d in decls}
for f in files:
    for i, l in enumerate(src[f].split('\n')):
        s = l.lstrip()
        if s.startswith(('//', '///', '//!', '*')):
            continue
        l = l.split('//')[0]
        toks = TOK.findall(l)
        own = declared_at.get((f, i + 1))
        for t in toks:
            index[t][f] += 1
        if own is not None:
            index[own][f] -= 1
for d in decls:
    fs = +index.get(d['name'], collections.Counter())
    d['uses'] = sum(fs.values())
    d['files'] = len(fs)
    d['home_uses'] = fs.get(d['file'], 0)

cls = {}
cpath = os.path.join(here, 'classes.tsv')
if os.path.exists(cpath):
    for l in open(cpath, encoding='utf-8'):
        if l.startswith('#') or not l.strip():
            continue
        p = l.rstrip('\n').split('\t')
        cls[(p[0], p[1])] = p[2:]

os.makedirs(outdir, exist_ok=True)
with open(os.path.join(outdir, 'census.tsv'), 'w', encoding='utf-8') as o:
    o.write('file\tline\tname\ttype\tvalue\texpr\tuses\tfiles\ttest\ttag\tclass\tquantity\tconsumer\tneed\n')
    for d in sorted(decls, key=lambda d: (d['file'], d['line'])):
        c = cls.get((d['file'].split('/')[-1], d['name']), ['', '', '', ''])
        o.write('\t'.join(str(x) for x in [d['file'], d['line'], d['name'], d['ty'], d['value'], d['expr'], d['uses'], d['files'], int(d['test']), d['tag'], *c]) + '\n')

# Collisions: one name, several values.
coll = []
for n, ds in byname.items():
    vals = {(d['value'] if d['value'] is not None else d['expr']) for d in ds if not d['test']}
    if len(vals) > 1:
        coll.append((n, sorted(((d['file'].split('crates/')[-1], d['line'], d['value'] if d['value'] is not None else d['expr']) for d in ds if not d['test']), key=str)))
# Repeated declarations of one value under one name.
dup = [(n, len([d for d in ds if not d['test']])) for n, ds in byname.items() if len({d['value'] for d in ds if not d['test']}) == 1 and len([d for d in ds if not d['test']]) > 1]
with open(os.path.join(outdir, 'summary.txt'), 'w', encoding='utf-8') as o:
    live = [d for d in decls if not d['test']]
    o.write(f'ref {ref} at {git("rev-parse", "--short=8", ref).strip()}  files {len(files)}  constants and defines {len(decls)} ({len(live)} outside tests)\n')
    o.write('unused (declared, no use outside comments): ' + ', '.join(f"{d['name']}@{d['file'].split('/')[-1]}:{d['line']}" for d in live if d['uses'] == 0) + '\n')
    o.write('one name, several values:\n')
    for n, v in sorted(coll):
        o.write(f'  {n}: ' + '; '.join(f'{a}:{b}={c}' for a, b, c in v) + '\n')
    o.write('one name, one value, declared more than once: ' + ', '.join(f'{n} x{k}' for n, k in sorted(dup)) + '\n')
    tags = collections.Counter(d['tag'] or 'untagged' for d in live)
    o.write('doc tags: ' + ', '.join(f'{k} {v}' for k, v in tags.most_common()) + '\n')
print(open(os.path.join(outdir, 'summary.txt')).read())
