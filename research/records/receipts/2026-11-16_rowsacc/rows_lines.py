"""A ruler: one kernel's executed instructions and stall samples by line of field.cu, from an Nsight Compute source page
(`ncu --import REP --page source --csv --print-source cuda,sass`) of a `-lineinfo` build.

Usage: python3 -I rows_lines.py SOURCE_CSV FIELD_CU LO HI [TOP]. Lines LO..HI of FIELD_CU (the kernel's own body, its lambdas
included) are printed by stall samples, each with its share of the kernel's instructions and samples and the line's first 90
characters; every other line of FIELD_CU is summed under the function that opens above it, and lines of other files as
`(other files)`. No path is printed."""
import csv, re, sys
from collections import defaultdict

src_csv, field_cu, lo, hi = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
top = int(sys.argv[5]) if len(sys.argv) > 5 else 40
text = open(field_cu, encoding='utf-8').read().split('\n')
pat = re.compile(r'^(?:template\s*<[^>]*>\s*)?(?:static\s+|__device__\s+|__global__\s+|__forceinline__\s+|inline\s+|extern\s+"C"\s+)+[\w:<>,\s\*&]*?\b(\w+)\s*\(')
opens = [(no, m.group(1)) for no, line in enumerate(text, 1) for m in [pat.match(line)] if m and not line.rstrip().endswith(';')]

def owner(no):
    best = '(before any function)'
    for o, name in opens:
        if o <= no:
            best = name
        else:
            break
    return best

inst, samp, reasons = defaultdict(int), defaultdict(int), defaultdict(lambda: defaultdict(int))
own = False
header = None
with open(src_csv, newline='', encoding='utf-8') as f:
    for row in csv.reader(f):
        if not row:
            continue
        if row[0] == 'File Path':
            own = row[1].endswith('kernels/field.cu')
            header = None
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
        no = int(row[0])
        key = ('L', no) if own and lo <= no <= hi else ('F', owner(no) if own else '(other files)')
        inst[key] += i
        samp[key] += s
ti, ts = sum(inst.values()), sum(samp.values())
print(f'kernel: {ti} warp instructions executed, {ts} stall samples')
body_i = sum(v for k, v in inst.items() if k[0] == 'L')
body_s = sum(v for k, v in samp.items() if k[0] == 'L')
print(f'lines {lo}-{hi} (the kernel body): instr {body_i / ti:.3f} samples {body_s / ts:.3f}')
print('functions outside the body, by samples:')
for k in sorted((k for k in inst if k[0] == 'F'), key=lambda k: -samp[k]):
    if samp[k] == 0 and inst[k] == 0:
        continue
    print(f'  {k[1]:34} instr {inst[k] / ti:6.3f} samples {samp[k] / ts:6.3f}')
print(f'the body\'s lines, by samples (top {top}):')
for k in sorted((k for k in inst if k[0] == 'L'), key=lambda k: -samp[k])[:top]:
    print(f'  {k[1]:5d} instr {inst[k] / ti:6.3f} samples {samp[k] / ts:6.3f}  {text[k[1] - 1].strip()[:90]}')
