#!/usr/bin/env -S python3 -I
"""splice_units.py SOURCE UNITS OUT: a state tool (the lead, November 28; the review's step 1 check of 08:32 UTC). The state SOURCE with
its level's unit store replaced by the one the state UNITS holds, every other line kept byte for byte.

The level's unit store is charged and founded only at a crossing and never stepped by a lap, so the store a crossing founded on one
state is the store a lap from it carries to its end; this moves a store written in the marks' new form (residues, `units J L`) into a
lap's end that carries it in the old (keyed circles, `units J L KEY`). The block runs from its `units` head through its rise block (the
`rise P₁ P₂` head and its 2 · RISE_DEPTH · 2 lines). Refused where either state has no store or the two rise stores differ.
"""
import sys

RISE_DEPTH = 2


def block(lines):
    at = next(i for i, l in enumerate(lines) if l.startswith('units '))
    rise = next(i for i in range(at, len(lines)) if lines[i].startswith('rise '))
    return at, rise + 1 + 2 * RISE_DEPTH * 2


def main():
    source, units, out = sys.argv[1:4]
    s = open(source).read().split('\n')
    u = open(units).read().split('\n')
    a, b = block(s)
    c, d = block(u)
    if s[b - 2 * RISE_DEPTH * 2 - 1:b] != u[d - 2 * RISE_DEPTH * 2 - 1:d]:
        sys.exit('SPLICE refused: the two rise stores differ')
    open(out, 'w').write('\n'.join(s[:a] + u[c:d] + s[b:]))
    print(f"SPLICE source_lines={len(s)} kept={len(s) - (b - a)} store_lines_out={b - a} store_lines_in={d - c} rise_equal=yes")


if __name__ == '__main__':
    main()
