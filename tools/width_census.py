#!/usr/bin/env python3
"""The declared widths of the live crates, read against their table (gate 1).

    python3 tools/width_census.py            check: exit 1 on a violation, each with the step that repairs it
    python3 tools/width_census.py table      print what the sources declare, as rows of the table
    python3 tools/width_census.py --root DIR ...   read another tree (the controls use it)

Reason (the record of November 21, "a width is a tolerance"): the guide's precision law bars a width picked by hand, and
from October 2 to November 20 five records found the engine's grains picked while nothing ran that read them. This check
reads every constant that sets a width, a grain, a rate, a guard or a carrier's bound in `crates/engine`,
`crates/engine-cuda` and `crates/athena`, and every such `#define` of the kernels, against
`crates/engine/WIDTHS.tsv`, where each has a row: its value, its class and its need (the law that gives it, or the read
that will). It refuses:

  1. a declared width with no row, a row with no declaration, a row whose value is not the source's;
  2. a row of a class this file does not know, or a `derived` or `identity` row whose source is a bare literal
     (a derived width is written as its derivation, so it moves with its operands);
  3. a kernel `#define` whose value is not its host twin's (the twins are written by hand until one declaration
     generates both);
  4. a count of `picked`, `carrier`, `literal` or `dead` rows that is not the table's ceiling for that class, or a count of literal
     shifts in a crate above its ceiling. The ceilings only fall: a change that lowers a count lowers the ceiling in
     the same commit, and a change that raises one says in its record which law it could not derive.
  5. a `receiver` or `counted` row whose need does not name, as `unit:NAME`, the state that holds the unit its places are
     counted from, and a count of code lines in a crate that hand a tolerance in by number (an identifier `eps_bits`,
     `epsilon_bits` or `tolerance_bits`) above its ceiling. Reason (the record of November 21, "a grain is a relation between
     grains"): a place counted under a fixed point for a tolerance set by hand is a dial, and E5 of #1088 was built on one
     the same day this check first ran, with nothing here to see it. A grain is located from its store's own spread at its
     reader's clock and carried in the state.

Scope: a name is read when it ends in _BITS (or _BITS_X), _DIGITS, _LIMBS, _RATE, _ROOT, _SLACK or _L1, is GUARD or
TEMPER_TOP, or is named by a row of the table (so any other constant can be put under the check by giving it a row).
A kernel name is read when it ends in _BITS, _DIGITS, _LIMBS, _RATE, _ROOT, _STEPS or _BACK, or is TEMPER_TOP.
Test files are not read. It reads text alone and builds nothing.
"""
import os
import re
import sys

CLASSES = {
    'exterior': 'a width the boundary gives (a byte enters at 8)',
    'receiver': "a grain located from its store's own spread at its reader's clock, or a mask read beside a control; its need names "
                'the state that holds it (unit:NAME)',
    'counted': 'a width read from the count of states its part distinguishes above its spread; its need names the state that '
               'holds its unit (unit:NAME)',
    'derived': 'computed from other widths by the need of its operation (a sum, a count of terms, a product, a bound proved)',
    'identity': 'another width under a second name, written as that name',
    'twin': "a kernel's copy of a host width, checked equal",
    'ruler': "an instrument's extent, outside the law",
    'realization': 'a limb layout or a kernel family, keeping every bit',
    'literal': "a width its own text derives from another, or repeats, written as a bare number (a defect: it does not move with its operands)",
    'carrier': 'chosen so a value fits a native register (a defect: the top grows by its carry or its need is computed)',
    'dead': 'declared and read by nothing (a defect: it leaves at its owner\'s next change)',
    'picked': 'no derivation on record (a defect: the campaign of the table ends when none is left)',
}
CEILED = ('picked', 'carrier', 'literal', 'dead')
CRATES = ('engine', 'engine-cuda', 'athena')
RUST = re.compile(r'^\s*(?:pub(?:\([a-z]+\))?\s+)?const\s+([A-Z][A-Z0-9_]*)\s*:\s*'
                  r'(u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)\s*=\s*(.+?);')
DEFINE = re.compile(r'^\s*#define\s+([A-Z][A-Z0-9_]*)\s+(\(?[-0-9A-Za-z_ ()*+<>]+?\)?)\s*(?://.*)?$')
RUST_SCOPE = re.compile(r'(_BITS(_[A-Z])?|_DIGITS|_LIMBS|_RATE|_ROOT|_SLACK|_L1)$|^GUARD$|^TEMPER_TOP$')
KERNEL_SCOPE = re.compile(r'(_BITS|_DIGITS|_LIMBS|_RATE|_ROOT|_STEPS|_BACK)$|^TEMPER_TOP$')
SHIFT = re.compile(r'(?:<<|>>)=?\s*([0-9]+)\b')
SHIFT_LEAST = 8
TOLERANCE = re.compile(r'\b(?:eps|epsilon|tolerance)_bits\b')
LOCATED = ('receiver', 'counted')
UNIT = re.compile(r'\bunit:[A-Za-z_][A-Za-z0-9_.:]*')
TABLE = 'crates/engine/WIDTHS.tsv'


def sources(root):
    """Every non-test source of the live crates: (path relative to the root, its lines)."""
    out = []
    for crate in CRATES:
        base = os.path.join(root, 'crates', crate)
        for folder, _, names in sorted(os.walk(base)):
            if os.sep + 'target' in folder:
                continue
            for name in sorted(names):
                if not name.endswith(('.rs', '.cu', '.cuh', '.h')):
                    continue
                path = os.path.relpath(os.path.join(folder, name), root).replace(os.sep, '/')
                if '/tests/' in path or path.endswith('tests.rs'):
                    continue
                with open(os.path.join(root, path), encoding='utf-8') as f:
                    out.append((path, f.read().split('\n')))
    return out


def declarations(files):
    """Every integer constant of the Rust sources and every `#define` of the kernels: name, owner, expression."""
    decls = []
    for path, lines in files:
        rust = path.endswith('.rs')
        for i, line in enumerate(lines):
            m = (RUST if rust else DEFINE).match(line)
            if not m:
                continue
            name, expr = (m.group(1), m.group(3)) if rust else (m.group(1), m.group(2))
            decls.append({'name': name, 'owner': path, 'line': i + 1, 'expr': expr.strip(), 'kernel': not rust})
    return decls


def evaluate(decl, by_name, depth=0):
    """A declaration's value where its expression is arithmetic over integers and named constants, else None."""
    if 'value' in decl:
        return decl['value']
    expr = re.sub(r'(\d)_(\d)', r'\1\2', decl['expr'])
    expr = re.sub(r'\b(0x[0-9A-Fa-f]+|\d+)(?:u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize|ull|ul|u)\b', r'\1', expr)
    expr = re.sub(r'\bas\s+(?:u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)\b', '', expr)
    expr = expr.replace('u32::MAX', str(2 ** 32 - 1)).replace('u64::MAX', str(2 ** 64 - 1)).replace('u8::MAX', '255')

    def named(m):
        if depth > 8:
            raise ValueError
        same = [d for d in by_name.get(m.group(0), []) if d['owner'] == decl['owner']]
        cands = same or by_name.get(m.group(0), [])
        values = {evaluate(d, by_name, depth + 1) for d in cands}
        if len(values) != 1 or None in values:
            raise ValueError
        return str(values.pop())

    value = None
    try:
        flat = re.sub(r'\b[A-Z][A-Z0-9_]*\b', named, expr)
        if re.fullmatch(r'[0-9a-fA-Fx ()*+\-<>/]+', flat):
            value = int(eval(flat.replace('/', '//'), {'__builtins__': {}}, {}))  # arithmetic on integers alone
    except (ValueError, SyntaxError, ZeroDivisionError, RecursionError):
        value = None
    decl['value'] = value
    return value


def literal(expr):
    """A bare number (with its type suffix or a cast), as against an expression over named widths."""
    return re.fullmatch(r'\(?\s*-?\s*(0x[0-9A-Fa-f_]+|[0-9_]+)\s*[a-z0-9]*\s*\)?', expr) is not None


def shifts(files):
    """Literal shift counts of at least SHIFT_LEAST places, by crate, outside comments."""
    out = dict.fromkeys(CRATES, 0)
    for path, lines in files:
        crate = path.split('/')[1]
        for line in lines:
            code = line.split('//')[0]
            out[crate] += sum(1 for m in SHIFT.finditer(code) if int(m.group(1)) >= SHIFT_LEAST)
    return out


def tolerances(files):
    """Code lines that hand a tolerance in by number, by crate, outside comments."""
    out = dict.fromkeys(CRATES, 0)
    for path, lines in files:
        crate = path.split('/')[1]
        out[crate] += sum(1 for line in lines if TOLERANCE.search(line.split('//')[0]))
    return out


def read_table(root):
    rows, ceilings, problems = [], {}, []
    path = os.path.join(root, TABLE)
    if not os.path.exists(path):
        return rows, ceilings, [f'{TABLE} is missing: python3 tools/width_census.py table > {TABLE} and class each row']
    with open(path, encoding='utf-8') as f:
        for n, line in enumerate(f.read().split('\n'), 1):
            if line.startswith('# ceiling '):
                parts = line.split()
                try:
                    ceilings[' '.join(parts[2:-1])] = int(parts[-1])
                except ValueError:
                    problems.append(f'{TABLE}:{n}: a ceiling line reads `# ceiling NAME COUNT`')
                continue
            if not line.strip() or line.startswith('#') or line.startswith('name\t'):
                continue
            cells = line.split('\t')
            if len(cells) != 5:
                problems.append(f'{TABLE}:{n}: a row has five cells (name, owner, value, class, need), this one {len(cells)}')
                continue
            rows.append(dict(zip(('name', 'owner', 'value', 'class', 'need'), cells), line=n))
    return rows, ceilings, problems


def census(root):
    """The declared widths in scope and every violation of the table. Returns (declarations in scope, problems, counts)."""
    files = sources(root)
    decls = declarations(files)
    by_name = {}
    for d in decls:
        by_name.setdefault(d['name'], []).append(d)
    rows, ceilings, problems = read_table(root)
    listed = {(r['name'], r['owner']) for r in rows}
    scope = [d for d in decls
             if (KERNEL_SCOPE if d['kernel'] else RUST_SCOPE).search(d['name']) or (d['name'], d['owner']) in listed]
    for d in scope:
        evaluate(d, by_name)
    declared = {}
    for d in scope:
        key = (d['name'], d['owner'])
        if key in declared:
            problems.append(f"{d['owner']}:{d['line']}: {d['name']} is declared twice in one file; the table keys a width by "
                            'its name and its file, so give the second its own name')
        declared[key] = d
    for key, d in declared.items():
        if key not in listed:
            problems.append(f"{d['owner']}:{d['line']}: {d['name']} = {d['expr']} sets a width and has no row in {TABLE}. "
                            'Add its row with its class and its need (the law that gives the width, or the read that will); '
                            'a width with no derivation is class `picked` and raises that ceiling, which the record of the '
                            'change answers for')
    counts = dict.fromkeys(CLASSES, 0)
    for r in rows:
        key = (r['name'], r['owner'])
        where = f"{TABLE}:{r['line']}: {r['name']}"
        if r['class'] not in CLASSES:
            problems.append(f"{where}: class `{r['class']}` is not one of {', '.join(CLASSES)}")
            continue
        counts[r['class']] += 1
        d = declared.get(key)
        if d is None:
            problems.append(f"{where}: no such declaration in {r['owner']}; remove the row with the width it described")
            continue
        if d['value'] is None:
            problems.append(f"{where}: `{d['expr']}` is not arithmetic this check can read; write it over integers and named widths")
        elif str(d['value']) != r['value']:
            problems.append(f"{where}: the table says {r['value']} and {r['owner']}:{d['line']} declares {d['value']}. A width is "
                            'changed in both, with the need that moved it written in the row')
        if not r['need'].strip():
            problems.append(f'{where}: the need is empty; state the law that gives the width, or the read that will')
        if r['class'] in LOCATED and not UNIT.search(r['need']):
            problems.append(f"{where}: class `{r['class']}` and its need names no unit. Write `unit:NAME`, the state that holds "
                            'the unit its places are counted from (a store\'s spread, a lane\'s power, a rate): a place under a '
                            'fixed point is a gauge')
        if r['class'] in ('derived', 'identity') and literal(d['expr']):
            problems.append(f"{where}: class `{r['class']}` but {r['owner']}:{d['line']} writes the bare literal `{d['expr']}`. "
                            'Write the derivation as the expression, or class the row `literal` or `picked`')
        if r['class'] == 'twin':
            m = re.match(r'=\s*([A-Z][A-Z0-9_]*)\s*@\s*(\S+)', r['need'])
            host = declared.get((m.group(1), m.group(2))) if m else None
            if host is None:
                problems.append(f'{where}: a twin\'s need opens `= NAME @ owner`, naming a declared host width')
            elif host['value'] != d['value']:
                problems.append(f"{where}: the kernel declares {d['value']} and its host twin {host['name']} @ {host['owner']} "
                                f"declares {host['value']}; the two are one width")
    for d in scope:
        if not d['kernel']:
            continue
        row = next((r for r in rows if (r['name'], r['owner']) == (d['name'], d['owner'])), None)
        hosts = [h for h in by_name.get(d['name'], []) if not h['kernel']]
        if row is not None and row['class'] != 'twin' and hosts:
            problems.append(f"{TABLE}:{row['line']}: {d['name']} is also declared on the host ({hosts[0]['owner']}); class the "
                            'kernel\'s row `twin` with the need `= NAME @ owner`')
    for cls in CEILED:
        if cls not in ceilings:
            problems.append(f'{TABLE}: no line `# ceiling {cls} COUNT`')
        elif counts[cls] != ceilings[cls]:
            verb = 'lower the ceiling to' if counts[cls] < ceilings[cls] else 'the ceilings only fall; derive the width, or raise it to'
            problems.append(f'{TABLE}: {counts[cls]} rows of class `{cls}` against a ceiling of {ceilings[cls]}: {verb} {counts[cls]}')
    found = shifts(files)
    for crate in CRATES:
        key = f'shifts {crate}'
        if key not in ceilings:
            problems.append(f'{TABLE}: no line `# ceiling {key} COUNT` (the crate holds {found[crate]})')
        elif found[crate] > ceilings[key]:
            problems.append(f"crates/{crate}: {found[crate]} literal shifts of {SHIFT_LEAST} places or more against a ceiling of "
                            f"{ceilings[key]}. A shift's count is a width: name it from the widths it follows from "
                            '(`<< (A_BITS - B_BITS)`), which the count does not read')
    handed = tolerances(files)
    for crate in CRATES:
        key = f'tolerances {crate}'
        if key not in ceilings:
            problems.append(f'{TABLE}: no line `# ceiling {key} COUNT` (the crate holds {handed[crate]})')
        elif handed[crate] > ceilings[key]:
            problems.append(f"crates/{crate}: {handed[crate]} code lines hand a tolerance in by number against a ceiling of "
                            f"{ceilings[key]}. A grain is a relation between grains: locate it from its store's own spread at "
                            "its reader's clock and carry it in the state")
    return scope, problems, counts, found, handed


def main(argv):
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if '--root' in argv:
        i = argv.index('--root')
        root = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    scope, problems, counts, found, handed = census(root)
    if argv[1:2] == ['table']:
        print('name\towner\tvalue\tclass\tneed')
        for d in sorted(scope, key=lambda d: (d['owner'], d['line'])):
            print(f"{d['name']}\t{d['owner']}\t{d['value']}\t\t")
        return 0
    for p in problems:
        print(f'width-census: {p}')
    held = ', '.join(f'{counts[c]} {c}' for c in CLASSES if counts[c])
    print(f"width-census: {len(scope)} declared widths ({held}); literal shifts "
          + ', '.join(f'{found[c]} {c}' for c in CRATES) + '; tolerances handed in by number '
          + ', '.join(f'{handed[c]} {c}' for c in CRATES) + (f'; {len(problems)} violations' if problems else '; the table holds'))
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
