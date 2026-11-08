import csv, sys
rows = [r for r in csv.DictReader(open(sys.argv[1], encoding='utf-8'), delimiter='\t') if r['class'] and r['test'] == '0']
order = ['grain, picked', 'grain, criterion', 'grain, derived', 'derived', 'carrier, derived', 'carrier, inherited', 'carrier, preset', 'identity', 'structural', 'schedule', 'derived from a horizon', 'read', 'realization', 'exterior', 'dead']
def key(r):
    c = r['class']
    for i, o in enumerate(order):
        if c.startswith(o):
            return (i, r['file'].endswith(('.cu', '.cuh')), r['file'], int(r['line']))
    return (99, r['file'], int(r['line']))
print('| Width | Value | Owner | Class | Quantity | Need |')
print('|---|---|---|---|---|---|')
for r in sorted(rows, key=key):
    owner = r['file'].split('/')[-1] + ':' + r['line']
    v = r['value'] if r['value'] != 'None' else r['expr']
    e = r['expr']
    val = v if (e == v or e.strip('()') == v) else f'{v} (`{e}`)'
    cells = [f"`{r['name']}`", val, owner, r['class'], r['quantity'], r['need']]
    print('| ' + ' | '.join(c.replace('|', '\\|') for c in cells) + ' |')
