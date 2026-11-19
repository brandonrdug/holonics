#!/usr/bin/env -S python3 -I
"""Lean declarations of the holonics package, read from the text: name -> list of (file, kind, line, statement).

A declaration is a line (after attributes and modifiers) opening with a declaration keyword and a name, outside comments. Its
statement is the text from the name to the first `:=`, ` where`, or a line starting `|` at depth 0, whitespace folded."""
import json, os, re, sys

ROOT = sys.argv[1]
OUT = sys.argv[2]
KW = r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)"
MOD = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
ATTR = r"(?:@\[[^\]]*\]\s*)*"
HEAD = re.compile(rf"^\s*{ATTR}{MOD}{KW}\b\s*([^\s:(\[{{]+)?")

def strip_comments(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(text[i]); i += 1
    return "".join(out)

decls = {}
for lib in ("Holonics", "HolonicsResearch"):
    base = os.path.join(ROOT, "lean", lib)
    for d, _, fs in os.walk(base):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            path = os.path.join(d, f)
            rel = os.path.relpath(path, base)[:-5]
            lines = strip_comments(open(path, encoding="utf-8").read()).split("\n")
            ns = []
            for k, line in enumerate(lines):
                m = re.match(r"^\s*namespace\s+(\S+)", line)
                if m:
                    ns.append(m.group(1)); continue
                m = re.match(r"^\s*end\s+(\S+)\s*$", line)
                if m and ns and ns[-1] == m.group(1):
                    ns.pop(); continue
                m = HEAD.match(line)
                if not m:
                    continue
                kind, name = m.group(1), m.group(2) or ""
                if kind == "example" or not name:
                    continue
                buf, depth, j = line[m.end(2):], 0, k
                stmt = []
                while True:
                    cut = None
                    for idx, ch in enumerate(buf):
                        if ch in "([{⟨": depth += 1
                        elif ch in ")]}⟩": depth -= 1
                        elif depth <= 0 and (buf.startswith(":=", idx) or re.match(r"\swhere\b", buf[idx:])):
                            cut = idx; break
                    if cut is not None:
                        stmt.append(buf[:cut]); break
                    stmt.append(buf)
                    j += 1
                    if j >= len(lines) or j - k > 60:
                        break
                    buf = lines[j]
                    if depth <= 0 and re.match(r"^\s*\|", buf):
                        break
                    if depth <= 0 and HEAD.match(buf):
                        break
                proof = ""
                tail = lines[j] if j < len(lines) else ""
                pm = re.search(r":=\s*(.*)", tail)
                if pm:
                    proof = pm.group(1).strip()[:80]
                    if not proof and j + 1 < len(lines):
                        proof = lines[j + 1].strip()[:80]
                full = ".".join(ns + [name]) if not name.startswith("_root_.") else name[7:]
                rec = {"file": f"{lib}/{rel}", "kind": kind, "line": k + 1, "name": full,
                       "stmt": re.sub(r"\s+", " ", " ".join(stmt)).strip(), "proof": proof}
                decls.setdefault(name.split(".")[-1], []).append(rec)
json.dump(decls, open(OUT, "w"))
print("names", len(decls), "decls", sum(len(v) for v in decls.values()))
