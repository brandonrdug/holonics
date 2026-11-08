"""Literal widths in the field path's law, host and card, behind the width census's finding 3 (read only).

Usage: python3 -I literals.py REPO REF [FILE ...]

On code lines only (comments and every `#[cfg(test)]` item skipped; a line that salts a hash with `mix(` is skipped), it lists
each line where one of the literals 40, 20, 62, 16 or 8 stands as a width: a shift amount (`<< N`, `>> N`,
`<< (N ...`), a value shifted into a grain (`62i64 << 20`), a release's grain (`release(..., N)`, `rel(..., N ± ...)`),
or an offset of a named width or a grain (`N ± NAME`, `NAME ± N`, `N + grain`). Each row is file, line, literal, text.
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
LITS = ('40', '20', '62', '16', '8')
def width_uses(line, n):
    name = r'(?:super::)?(?:[A-Z][A-Z0-9_]*|grain|back|bits|h|e)'
    pats = [
        rf'(?:<<|>>)\s*\(?\s*{n}\b',
        rf'\b{n}(?:i64|i128|u64|u128)?\s*<<',
        rf'\b(?:release|rel)\([^;]*,\s*\(?\s*{n}\b',
        rf'\b{n}\s*[-+]\s*{name}\b',
        rf'\b{name}\s*[-+]\s*{n}\b(?!\s*[*\w])',
        rf'\(\s*{n}\s*\+\s*\d+\s*\+\s*{name}',
    ]
    return any(re.search(p, line) for p in pats)
print('file\tline\tliteral\ttext')
for f in files:
    src = subprocess.run(['git', '-C', repo, 'show', f'{ref}:{f}'], capture_output=True, text=True, check=True).stdout
    lines = src.split('\n')
    tests = test_lines(lines)
    for i, line in enumerate(lines, 1):
        if i in tests:
            continue
        if line.lstrip().startswith('//') or 'mix(' in line:
            continue
        code = line.split('//')[0]
        code = re.sub(r'"[^"]*"', '""', code)
        for n in LITS:
            if width_uses(code, n):
                print(f'{f.split("/")[-1]}\t{i}\t{n}\t{line.strip()[:200]}')
