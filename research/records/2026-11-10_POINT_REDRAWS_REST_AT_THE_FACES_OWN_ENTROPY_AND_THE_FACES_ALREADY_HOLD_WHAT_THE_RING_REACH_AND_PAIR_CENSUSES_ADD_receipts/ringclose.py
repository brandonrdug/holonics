#!/usr/bin/env python3
"""ringclose.py SAMPLE.tsv [MAXPROBLEM]: per write set, answers whose ( ) and [ ] counts balance, and whose backtick, double and
single quote counts are even (the ring census's residues at the answer's end)."""
import sys, codecs
lim = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
n = 0; c = dict(paren=0, bracket=0, backtick=0, dquote=0, squote=0)
for line in open(sys.argv[1], encoding="utf-8"):
    p, _, w = line.rstrip("\n").partition("\t")
    if not p.isdigit() or int(p) >= lim: continue
    t = codecs.decode(w.encode("latin-1", "backslashreplace"), "unicode_escape")
    n += 1
    c["paren"] += t.count("(") == t.count(")")
    c["bracket"] += t.count("[") == t.count("]")
    c["backtick"] += t.count("`") % 2 == 0
    c["dquote"] += t.count('"') % 2 == 0
    c["squote"] += t.count("'") % 2 == 0
print("answers", n, " ".join(f"{k}={v}" for k, v in c.items()))
