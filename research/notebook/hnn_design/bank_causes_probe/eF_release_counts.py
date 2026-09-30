"""Exact counts of a `bank_causes -- native-release` trace on order-2 requests (exterior reading of
the receipts; no float): released/held/refused, whole sections, stations right by station, the
first lock's station and whether it is right, sections following the rule among their own
stations, native-float agreement, the two chains' implied seeds, certificates and admission.

usage: eF_release_counts.py <export> <native-release trace>"""
import re
import sys
from collections import Counter

export, trace = sys.argv[1], sys.argv[2]
requests = {}
for line in open(export):
    parts = line.split()
    if parts and parts[0] == 'pair':
        requests[int(parts[1])] = [int(x) for x in parts[2].split(',')]

rows = []
cur = None
for line in open(trace):
    m = re.match(r'request (\d+): target \[(.*?)\]; native (released|held) \[(.*?)\] \(right (\d+), the float release \[(.*?)\] agrees at (\d+)\); refinements (\d+), readings (\d+), locks (\[.*\]); members certified (\d+) of (\d+), ticks closed (\d+) of (\d+)', line)
    if m:
        cur = {
            'index': int(m.group(1)),
            'target': [int(x) for x in m.group(2).split(',')],
            'released': m.group(3) == 'released',
            'classes': [int(x) for x in m.group(4).split(',')],
            'agree': int(m.group(7)),
            'locks': eval(m.group(10)),
            'certified': (int(m.group(11)), int(m.group(12))),
            'ticks': (int(m.group(13)), int(m.group(14))),
        }
        rows.append(cur)
        continue
    if re.match(r'request (\d+): .*REFUSED', line):
        rows.append({'refused': True})
        cur = None
        continue
    m = re.match(r'\s+admission: (\d+) candidates read, (\d+) past the signed form', line)
    if m and cur is not None:
        cur['admission'] = (int(m.group(1)), int(m.group(2)))
    m = re.match(r'\s+teacher-forced: .*exact top = target (\d+)', line)
    if m and cur is not None:
        cur['tf'] = int(m.group(1))

stations = 8
read = [r for r in rows if not r.get('refused')]
released = sum(r['released'] for r in read)
held = len(read) - released
refused = len(rows) - len(read)
whole = right = f01 = fright = consistent = agree = tf = 0
by_station = [0] * stations
first_st = Counter()
chains = {0: Counter(), 1: Counter()}
cert = [0, 0]
ticks = [0, 0]
cand = [0, 0]
for r in read:
    cls, tgt = r['classes'], r['target']
    hits = [int(a == b) for a, b in zip(cls, tgt)]
    right += sum(hits)
    whole += int(all(hits))
    for j in range(stations):
        by_station[j] += hits[j]
    if r['locks']:
        first = r['locks'][0]
        for s in first:
            first_st[s] += 1
        f01 += int(any(s < 2 for s in first))
        fright += int(all(cls[s] == tgt[s] for s in first))
    consistent += int(all(cls[j] == (cls[j - 2] + 1) % 4 for j in range(2, stations)))
    agree += r['agree']
    tf += r.get('tf', 0)
    cert[0] += r['certified'][0]; cert[1] += r['certified'][1]
    ticks[0] += r['ticks'][0]; ticks[1] += r['ticks'][1]
    if 'admission' in r:
        cand[0] += r['admission'][0]; cand[1] += r['admission'][1]
    req = requests[r['index']]
    x38, x39 = req[-2], req[-1]
    for j in range(stations):
        k = j // 2
        c = cls[j]
        if c > 3:
            chains[j % 2]['neither'] += 1
            continue
        seed = (c - (k + 1)) % 4
        hit38, hit39 = seed == x38, seed == x39
        chains[j % 2]['both' if hit38 and hit39 else 'x_38' if hit38 else 'x_39' if hit39 else 'neither'] += 1
print(f'requests {len(rows)}: released {released}, held {held}, refused {refused}; whole {whole}; stations right {right} '
      f'by station {by_station}; first lock at station 0 or 1 {f01}, first lock right {fright}; first-lock stations '
      f'{dict(sorted(first_st.items()))}; consistent {consistent}; native-float agreement {agree} of {8 * len(read)}; '
      f'teacher-forced tops right {tf}; members certified {cert[0]} of {cert[1]}, ticks closed {ticks[0]} of {ticks[1]}; '
      f'candidates read {cand[0]}, past the signed form {cand[1]}')
print('even stations (rule: seed x_38):', dict(chains[0]))
print('odd stations (rule: seed x_39):', dict(chains[1]))
