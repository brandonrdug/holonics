"""A ruler: the forward contact's executed instructions and stall samples by the kernel source's function, from an Nsight
Compute source page (`ncu --import REP --page source --csv --print-source cuda,sass`) of a `-lineinfo` build.

Usage: python3 -I source_shares.py SOURCE_CSV FIELD_CU. Each CUDA line of FIELD_CU is assigned the innermost function whose
definition opens above it (a line that starts a `__device__`, `__global__` or `static` definition); lines of other files are
summed as `(other files)`. Prints each function's share of the kernel's executed instructions and of its stall samples, with
its samples per instruction against the kernel's. No path is printed."""
import csv, re, sys
from collections import defaultdict

src_csv, field_cu = sys.argv[1], sys.argv[2]
opens = []
pat = re.compile(r'^(?:template\s*<[^>]*>\s*)?(?:static\s+|__device__\s+|__global__\s+|__forceinline__\s+|inline\s+|extern\s+"C"\s+)+[\w:<>,\s\*&]*?\b(\w+)\s*\(')
for no, line in enumerate(open(field_cu, encoding='utf-8'), 1):
    m = pat.match(line)
    if m and not line.rstrip().endswith(';'):
        opens.append((no, m.group(1)))
macro = re.compile(r'^#define\s+(\w+)')
for no, line in enumerate(open(field_cu, encoding='utf-8'), 1):
    m = macro.match(line)
    if m and line.rstrip().endswith('\\'):
        opens.append((no, '#' + m.group(1)))
opens.sort()

def owner(no):
    lo, hi, best = 0, len(opens) - 1, '(before any function)'
    while lo <= hi:
        mid = (lo + hi) // 2
        if opens[mid][0] <= no:
            best, lo = opens[mid][1], mid + 1
        else:
            hi = mid - 1
    return best

inst, samp = defaultdict(int), defaultdict(int)
own = False
with open(src_csv, newline='', encoding='utf-8') as f:
    rows = csv.reader(f)
    header = None
    for row in rows:
        if not row:
            continue
        if row[0] == 'File Path':
            own = row[1].endswith('kernels/field.cu')
            header = None
            continue
        if row[0] == 'Function Name':
            continue
        if row[0] == 'Line No':
            header = row
            ii, si = header.index('Instructions Executed'), header.index('Warp Stall Sampling (All Samples)')
            continue
        if header is None or not row[0].isdigit():
            continue
        try:
            i, s = int(row[ii] or 0), int(row[si] or 0)
        except ValueError:
            continue
        key = owner(int(row[0])) if own else '(other files)'
        inst[key] += i
        samp[key] += s
ti, ts = sum(inst.values()), sum(samp.values())
print(f'kernel: {ti} warp instructions executed, {ts} stall samples')
print(f'{"function":32} {"instr":>7} {"samples":>8} {"samples/instr vs kernel":>24}')
for k in sorted(inst, key=lambda k: -samp[k]):
    if inst[k] == 0 and samp[k] == 0:
        continue
    a, b = inst[k] / ti, samp[k] / ts
    print(f'{k:32} {a:7.3f} {b:8.3f} {(b / a if a else float("inf")):24.2f}')
