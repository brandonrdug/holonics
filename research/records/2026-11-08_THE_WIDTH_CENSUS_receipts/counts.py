"""Counts behind the width census's findings 9 and 10 (read only).

Usage: python3 -I counts.py REPO REF [FILE ...]

For each file of the field path (default: the host field, energy and moment laws and their three card kernels) it
counts, on code lines only (a line whose text starts with // is a comment and is skipped; a test module is counted
apart, by the brace depth of each `#[cfg(test)]` item): calls of the numeric release (`release(` on the host, `rel(` on the card; a method `.release(` and a
definition are not calls), `div_nearest(` calls, `fit64(` calls, lines naming a refusal "past its 128-bit
carrier", and the saturating reads (`saturating_*`, `unwrap_or(u128::MAX)` and the like).
"""
import re, subprocess, sys

def test_lines(lines):
    """Line numbers (from 1) inside a `#[cfg(test)]` item: a `mod tests { ... }` block or a test-only fn, by brace
    depth. `mod tests;` names another file and marks nothing here."""
    marked, i = set(), 0
    while i < len(lines):
        if re.match(r'^\s*#\[cfg\(test\)\]', lines[i]):
            j = i + 1
            while j < len(lines) and lines[j].lstrip().startswith('#['):
                j += 1
            if j < len(lines) and re.match(r'^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*;', lines[j]):
                i = j + 1
                continue
            depth, opened, k = 0, False, j
            while k < len(lines):
                code = re.sub(r'"(?:\\.|[^"\\])*"', '""', lines[k].split('//')[0])
                depth += code.count('{') - code.count('}')
                opened = opened or '{' in code
                marked.add(k + 1)
                if opened and depth <= 0:
                    break
                k += 1
            i = k + 1
            continue
        i += 1
    return marked

repo, ref = sys.argv[1:3]
files = sys.argv[3:] or [
    'crates/holonics/src/hnn/tower/field.rs',
    'crates/holonics/src/hnn/tower/field/energy.rs',
    'crates/holonics/src/hnn/tower/field/moment.rs',
    'crates/holonics-cuda/kernels/field.cu',
    'crates/holonics-cuda/kernels/field_energy.cuh',
    'crates/holonics-cuda/kernels/field_moment.cuh',
]
pats = {
    'release': re.compile(r'(?<![.\w])(?:release|rel)\('),
    'div_nearest': re.compile(r'(?<![.\w])div_nearest\('),
    'fit64': re.compile(r'(?<![.\w])fit64\('),
    'carrier_refusal_lines': None,
    'saturating': re.compile(r'saturating_(?:add|sub|mul)|unwrap_or\(\s*(?:u128|i128|u64|i64)::MAX\s*\)'),
}
print('file\tpart\t' + '\t'.join(pats))
for f in files:
    src = subprocess.run(['git', '-C', repo, 'show', f'{ref}:{f}'], capture_output=True, text=True, check=True).stdout
    counts = {'code': dict.fromkeys(pats, 0), 'test': dict.fromkeys(pats, 0)}
    lines = src.split('\n')
    tests = test_lines(lines)
    for n, line in enumerate(lines, 1):
        part = 'test' if n in tests else 'code'
        if line.lstrip().startswith('//'):
            continue
        # a definition names the function before its parameter list: `fn rel(`, `__device__ ... wide rel(`
        line = re.sub(r'(\bfn\s+|__device__[^;=(]*?\s)(?:release|rel|div_nearest|fit64)\(', ' ', line)
        for k, p in pats.items():
            if p is None:
                counts[part][k] += '128-bit carrier' in line
            else:
                counts[part][k] += len(p.findall(line))
    for part in ('code', 'test'):
        print(f + '\t' + part + '\t' + '\t'.join(str(counts[part][k]) for k in pats))
