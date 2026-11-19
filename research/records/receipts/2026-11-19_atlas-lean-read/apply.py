#!/usr/bin/env python3
"""Apply fix files to docs/atlas by id, replacing whole fields. Usage: apply.py BASE_COMMIT FIX.tsv... [--write]
A field is applied only where the row's field at HEAD equals the field at BASE (nobody changed it since the fixer read it);
owners must keep every existing owner in order. Prints each change and each refusal."""
import sys, subprocess, re, collections
FIELDS = {'expr': 2, 'reads': 3, 'scope': 4, 'owners': 5, 'grade': 6}
args = [a for a in sys.argv[1:] if not a.startswith('--')]
write = '--write' in sys.argv
base, fixfiles = args[0], args[1:]
SH = ['objects', 'information', 'geometry', 'physics', 'arithmetic', 'targets']
def load(text):
    rows = {}
    for i, l in enumerate(text.splitlines()):
        p = l.split('\t')
        if len(p) >= 8: rows[p[0]] = (i, p)
    return rows
head_text = {s: open(f'docs/atlas/{s}.tsv', encoding='utf-8').read() for s in SH}
head = {s: load(head_text[s]) for s in SH}
basev = {s: load(subprocess.run(['git', 'show', f'{base}:docs/atlas/{s}.tsv'], capture_output=True, text=True).stdout) for s in SH}
where = {rid: s for s in SH for rid in head[s]}
changes = collections.OrderedDict(); refused = []; nofix = 0; n = 0
for ff in fixfiles:
    for ln, l in enumerate(open(ff, encoding='utf-8'), 1):
        l = l.rstrip('\n')
        if not l or l.startswith('#'): continue
        p = l.split('\t')
        if len(p) < 4: refused.append((ff, ln, '?', 'short line')); continue
        rid, shard, cls, field = p[0], p[1], p[2], p[3]
        n += 1
        if cls == 'NOFIX' or field == '-': nofix += 1; continue
        val = p[4] if len(p) > 4 else ''
        s = where.get(rid)
        if s is None: refused.append((ff, ln, rid, 'no such row')); continue
        if field not in FIELDS: refused.append((ff, ln, rid, f'field {field}')); continue
        k = FIELDS[field]
        hv = head[s][rid][1][k]; bv = basev[s][rid][1][k] if rid in basev[s] else None
        if bv is not None and hv != bv: refused.append((ff, ln, rid, f'{field} changed on main since the base')); continue
        if field == 'owners':
            old = [o.strip() for o in hv.split(';') if o.strip()]
            new = [o.strip() for o in val.split(';') if o.strip()]
            if new[:len(old)] != old: refused.append((ff, ln, rid, 'owners do not keep the existing owners in order')); continue
        if re.search(r'\bexact(ly)?\b', val, re.I) and not re.search(r'\bexact(ly)?\b', hv, re.I):
            refused.append((ff, ln, rid, f'{field} adds the word exact')); continue
        if re.search(r'\bwrong\b', val, re.I): refused.append((ff, ln, rid, f'{field} says wrong')); continue
        key = (rid, field)
        if key in changes and changes[key][2] != val: refused.append((ff, ln, rid, f'two values for {field}')); continue
        changes[key] = (s, k, val, hv, ff)
for (rid, field), (s, k, val, hv, ff) in changes.items():
    print(f'CHANGE {s}:{rid}:{field}\n  - {hv}\n  + {val}')
for r in refused: print('REFUSED', *r)
print(f'APPLY fixes={n} nofix={nofix} changes={len(changes)} refused={len(refused)}')
if write:
    for s in SH:
        lines = head_text[s].split('\n')
        for (rid, field), (s2, k, val, hv, ff) in changes.items():
            if s2 != s: continue
            i = head[s][rid][0]; p = lines[i].split('\t'); p[k] = val; lines[i] = '\t'.join(p)
        open(f'docs/atlas/{s}.tsv', 'w', encoding='utf-8').write('\n'.join(lines))
