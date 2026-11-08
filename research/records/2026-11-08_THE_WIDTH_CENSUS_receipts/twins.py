import csv, sys, collections
rows = list(csv.DictReader(open(sys.argv[1], encoding='utf-8'), delimiter='\t'))
host = collections.defaultdict(list)
for r in rows:
    if r['file'].endswith('.rs') and r['test'] == '0':
        host[r['name']].append(r)
out = []
for r in rows:
    if not r['file'].endswith(('.cu', '.cuh')):
        continue
    k = r['file'].split('/')[-1]
    if k not in ('field.cu', 'field_energy.cuh', 'field_moment.cuh', 'tower.cu'):
        continue
    if r['name'].startswith(('REFUSED', 'ENERGY_LOCK', 'ENERGY_LETTERS', 'ENERGY_PAIR', 'ENERGY_LOGS', 'ENERGY_PAIRS', 'ENERGY_MOVED', 'ENERGY_PHI', 'NO_BIAS', 'MOMENT_REFUSED')):
        continue
    h = host.get(r['name'], [])
    hv = sorted({x['value'] for x in h})
    expr_lit = r['expr'].strip('()').isdigit()
    hexpr = sorted({x['expr'] for x in h})
    status = 'no host twin' if not h else ('equal' if hv == [r['value']] else ('several host values ' + ','.join(hv) if len(hv) > 1 else 'DIFFERS'))
    if h and status == 'equal' and expr_lit and any(not e.strip().isdigit() for e in hexpr):
        status = 'equal; card literal, host derived (' + '; '.join(hexpr) + ')'
    out.append((k, r['line'], r['name'], r['value'], status))
for o in out:
    print('\t'.join(o))
