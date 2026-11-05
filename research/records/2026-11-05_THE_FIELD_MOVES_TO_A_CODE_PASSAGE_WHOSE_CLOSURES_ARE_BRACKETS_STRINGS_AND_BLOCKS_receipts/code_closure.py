#!/usr/bin/env python3
"""Whether the written code closes what it opens, by span, beside the held code (the code passage; the unified-theory
reading of November 5, 16:36, fixed before the first write).

Usage: code_closure.py HELD.txt SAMPLE.tsv

Read inside each answer's code fence (the whole answer where it has none), outside comments:
- brackets `(` `[` `{`: an opener closes where its own closer meets it on the stack; a wrong closer, or none before the
  code ends, leaves it open;
- strings (`'`, `"`, and their triples): a literal closes at its own quote (a single-quoted one before its line ends);
- blocks: a line ending in `:` closes where an indented body follows it and the code dedents to its indent or ends.
Each opener's span is the places from its opening byte to its closing byte (a block's to the last byte of its body): near
under 6, far 6 or more (the field's near field, lcm(2, 3)). For each family and span, the share of openers that close at
that span, written and held, and their ratio; the rule reads a closure under 0.5 of held. Aggregates only.
"""
import re
import sys

NEAR = 6


def records(path):
    out = []
    for r in open(path, "rb").read().split(b"\x1e"):
        if b"\x1f" in r:
            out.append(r.split(b"\x1f", 1)[1].decode("utf-8", "replace"))
    return out


def code_of(a):
    m = re.search(r"```(?:python)?\n(.*?)(?:```|$)", a, re.S)
    return m.group(1) if m else a


def scan(code):
    """Openers of brackets and strings: (family, closed, span)."""
    out, stack, i, n = [], [], 0, len(code)
    pairs = {")": "(", "]": "[", "}": "{"}
    while i < n:
        c = code[i]
        if c == "#":
            while i < n and code[i] != "\n":
                i += 1
            continue
        if c in "'\"":
            q = code[i:i + 3] if code[i:i + 3] in ("'''", '"""') else c
            j = i + len(q)
            closed = False
            while j < n:
                if code[j] == "\\":
                    j += 2
                    continue
                if len(q) == 1 and code[j] == "\n":
                    break
                if code.startswith(q, j):
                    closed = True
                    j += len(q)
                    break
                j += 1
            out.append(("string", closed, j - i - 1 if closed else None))
            i = j
            continue
        if c in "([{":
            stack.append((c, i))
        elif c in ")]}":
            if stack and stack[-1][0] == pairs[c]:
                _, at = stack.pop()
                out.append(("bracket", True, i - at))
            elif stack:
                _, at = stack.pop()
                out.append(("bracket", False, None))
        i += 1
    out.extend(("bracket", False, None) for _ in stack)
    return out


def blocks(code):
    lines = code.split("\n")
    out = []
    offsets, at = [], 0
    for line in lines:
        offsets.append(at)
        at += len(line) + 1
    indent = lambda l: len(l) - len(l.lstrip(" \t"))
    for k, line in enumerate(lines):
        bare = line.split("#", 1)[0].rstrip()
        if not bare.endswith(":") or not bare.strip():
            continue
        h = indent(line)
        body = [m for m in range(k + 1, len(lines)) if lines[m].strip()]
        if not body or indent(lines[body[0]]) <= h:
            out.append(("block", False, None))
            continue
        last = body[0]
        for m in body:
            if indent(lines[m]) <= h:
                break
            last = m
        end = offsets[last] + len(lines[last]) - 1
        out.append(("block", True, end - (offsets[k] + len(bare) - 1)))
    return out


def tally(answers):
    t = {}
    for a in answers:
        code = code_of(a)
        for fam, closed, span in scan(code) + blocks(code):
            d = t.setdefault(fam, [0, 0, 0])
            d[0] += 1
            if closed:
                d[1 if span < NEAR else 2] += 1
    return t


def main():
    held = records(sys.argv[1])
    written = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            w = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace").decode("utf-8", "replace")
            written.append((int(k), w))
    tw = tally([w for _, w in written])
    th = tally([held[k] for k, _ in written])
    print("family\tspan\twritten opened\twritten closed share\theld opened\theld closed share\tratio")
    worst = None
    for fam in ("bracket", "string", "block"):
        ow, nw, fw = tw.get(fam, [0, 0, 0])
        oh, nh, fh = th.get(fam, [0, 0, 0])
        for span, cw, ch in (("near", nw, nh), ("far", fw, fh)):
            sw, sh = cw / ow if ow else 0.0, ch / oh if oh else 0.0
            ratio = sw / sh if sh else float("nan")
            print(f"{fam}\t{span}\t{ow}\t{sw:.3f}\t{oh}\t{sh:.3f}\t{ratio:.2f}")
            if sh and (worst is None or ratio < worst[0]):
                worst = (ratio, fam, span)
    if worst:
        print(f"RULE: the lowest closure against held is {worst[1]} {worst[2]} at {worst[0]:.2f} ({'under' if worst[0] < 0.5 else 'at or over'} 0.5)")


if __name__ == "__main__":
    main()
