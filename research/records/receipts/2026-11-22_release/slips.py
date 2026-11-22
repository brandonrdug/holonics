"""A ruler: the digits a write misses, by what the missed digit is. Reads the panel lines of a TERRAIN_SCORE file (the terrain's held
panel as tools print it: `  ARM kind: PROMPT = 'WRITE\\n..' (want REFERENCE) | ...`).

A sum's missed digit is counted as `carry dropped` where its place takes a carry from the places under it and the write is the
reference less one, `carry added` where it takes none and the write is the reference plus one, and `other` elsewhere (only writes of
the reference's length are aligned). A copy's or a reversal's missed digit is counted as `in its operand` where the written digit
stands at another place of the same operand, and `foreign` where the operand holds it nowhere.
A planted line checks each count before the file is read. Outside the machine. Usage: slips.py SCORES"""
import re, sys, collections

def sum_slips(prompt, write, want):
    a, b = (int(x) for x in prompt.split(' + ')); out = []
    if len(write) != len(want) or not write.isdigit(): return [('unaligned', None)] if write != want else []
    for k in range(len(want)):                                   # k from the units
        w, r = int(write[-1 - k]), int(want[-1 - k])
        if w == r: continue
        carry = (a % 10 ** k + b % 10 ** k) >= 10 ** k
        if carry and w == (r - 1) % 10: out.append(('carry dropped', k))
        elif not carry and w == (r + 1) % 10: out.append(('carry added', k))
        else: out.append(('other, a carry due' if carry else 'other, none due', k))
    return out

def copy_slips(prompt, write, want):
    operand = prompt.split()[1:]; w, r = write.split(), want.split(); out = []
    if len(w) != len(r): return [('unaligned', None)] if w != r else []
    for i, (x, y) in enumerate(zip(w, r)):
        if x != y: out.append(('in its operand' if x in operand else 'foreign', i))
    return out

def read(lines):
    tally = collections.defaultdict(collections.Counter); digits = collections.Counter(); writes = collections.Counter()
    for line in lines:
        m = re.match(r"\s+(\S+) (sum|copy|reverse): (.*)", line)
        if not m: continue
        arm, kind, rest = m.groups()
        for item in rest.split(' | '):
            m2 = re.match(r"(.*) = '(.*?)\\\\n.*' \(want (.*)\)", item)
            if not m2: continue
            prompt, write, want = m2.groups(); writes[kind] += 1
            digits[kind] += len(want.replace(' ', ''))
            for what, _ in (sum_slips if kind == 'sum' else copy_slips)(prompt, write, want):
                tally[kind][what] += 1
    return tally, digits, writes

planted = ["  P sum: 57 + 9 = '56\\\\n1' (want 66) | 12 + 13 = '26\\\\n1' (want 25) | 730 + 929 = '1359\\\\n1' (want 1659)",
           "  P copy: copy 4 7 8 = '8 7 8\\\\nco' (want 4 7 8) | copy 0 6 9 = '6 0 3\\\\nco' (want 0 6 9)"]
t, _, _ = read(planted)
assert t['sum'] == {'carry dropped': 1, 'carry added': 1, 'other, none due': 1}, t['sum']
assert t['copy'] == {'in its operand': 3, 'foreign': 1}, t['copy']
print('SLIPS planted: a dropped carry, an added carry and an other found among 3 sums; 3 in-operand and 1 foreign among 2 copies')
tally, digits, writes = read(open(sys.argv[1], encoding='utf-8'))
for kind in ('sum', 'copy', 'reverse'):
    missed = sum(tally[kind].values())
    print(f'SLIPS {kind}: {writes[kind]} writes, {digits[kind]} reference digits, {missed} missed | ' + ', '.join(f'{k} {v}' for k, v in sorted(tally[kind].items())))
