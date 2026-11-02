"""Which library modules does the live Athena learner reach?

Reads crates/holonics/src: maps each module path to its file, collects every `crate::a::b...`
and `super::`/`self::` reference in code (use statements and inline paths; comments dropped), and
walks the reference graph from the roots given on the command line. Module-level reach overstates
use (an item-level reach would be smaller), so the unreached count is a lower bound. Prints lines reached and lines not reached, by
top-level module. A reading of the source only (no build).

Usage: python3 -I closure.py SRC_DIR ROOT_MODULE...   (module paths like hnn::tower::field)
"""

import os
import re
import sys
from collections import defaultdict


def module_files(src):
    files = {}
    for dirpath, _, names in os.walk(src):
        for name in names:
            if not name.endswith(".rs"):
                continue
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, src)[:-3].split(os.sep)
            if rel[-1] in ("mod", "lib"):
                rel = rel[:-1]
            files["::".join(rel)] = full
    return files


PATH = re.compile(r"\b(crate|super|self)((?:::[A-Za-z_][A-Za-z0-9_]*)+)")
USE_GROUP = re.compile(r"\buse\s+(crate|super|self)::([^;]*);", re.S)


def resolve(base, kind, parts, files):
    if kind == "crate":
        mod = []
    elif kind == "self":
        mod = list(base)
    else:
        mod = list(base[:-1])
    while parts and parts[0] == "super":
        mod = mod[:-1]
        parts = parts[1:]
    out = []
    path = mod + parts
    for k in range(len(path), 0, -1):
        key = "::".join(path[:k])
        if key in files:
            out.append(key)
            break
    return out


def expand_group(text):
    # Expand `a::{b, c::{d, e}}` into a::b, a::c::d, a::c::e (good enough for module reach).
    text = re.sub(r"\s+", "", text)
    out = []

    def rec(prefix, s):
        depth = 0
        start = 0
        items = []
        for i, ch in enumerate(s):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            elif ch == "," and depth == 0:
                items.append(s[start:i])
                start = i + 1
        items.append(s[start:])
        for item in items:
            if not item:
                continue
            if "{" in item:
                head, rest = item.split("{", 1)
                rec(prefix + [p for p in head.split("::") if p], rest[:-1])
            else:
                out.append(prefix + [p for p in item.split("::") if p and p != "self"])

    rec([], text)
    return out


def main(src, roots):
    files = module_files(src)
    edges = defaultdict(set)
    for mod, path in files.items():
        here = mod.split("::") if mod else []  # self:: is this module; super:: its parent
        # comment lines and trailing comments are dropped, so doc links count as no use
        text = "\n".join(l.split("//")[0] if not l.lstrip().startswith("//") else "" for l in open(path, encoding="utf-8"))
        for kind, rest in USE_GROUP.findall(text):
            for parts in expand_group(rest):
                for t in resolve(here, kind, parts, files):
                    edges[mod].add(t)
        for kind, rest in PATH.findall(text):
            parts = [p for p in rest.split("::") if p]
            for t in resolve(here, kind, parts, files):
                edges[mod].add(t)
    seen = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in files:
            continue
        seen.add(m)
        stack.extend(edges[m])
    lines = {m: sum(1 for _ in open(p, encoding="utf-8")) for m, p in files.items()}
    by_top_in = defaultdict(int)
    by_top_out = defaultdict(int)
    for m, n in lines.items():
        top = m.split("::")[0] if m else "(lib)"
        if top == "hnn" and m.count("::") >= 1:
            top = "hnn::" + m.split("::")[1]
        (by_top_in if m in seen else by_top_out)[top] += n
    total_in = sum(by_top_in.values())
    total_out = sum(by_top_out.values())
    print(f"modules reached {len(seen)} of {len(files)}; lines reached {total_in}, not reached {total_out}")
    keys = sorted(set(by_top_in) | set(by_top_out), key=lambda k: -(by_top_in[k] + by_top_out[k]))
    for k in keys:
        print(f"  {k:28s} reached {by_top_in[k]:7d}   not reached {by_top_out[k]:7d}")
    print("reached modules:")
    for m in sorted(seen):
        print("  ", m, lines[m])


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
