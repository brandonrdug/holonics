#!/usr/bin/env python3
"""Identifier repeats within an answer (the unified-theory reading of November 6, 18:50): for each SAMPLE.tsv, over the code
of each written answer (code_reading.py's code_of and identifier pattern), the pooled repeat share 1 - distinct/total (each
answer's distinct identifiers against its identifier tokens), the commonest identifier's share of all tokens, and the same
for held's own answers. Usage: repeat.py HELD.txt SAMPLE.tsv [SAMPLE.tsv ...]. A reading only."""
import collections, importlib.util, os, sys
spec = importlib.util.spec_from_file_location("code_reading", os.path.join(os.path.dirname(os.path.abspath(__file__)), "code_reading.py"))
cr = importlib.util.module_from_spec(spec); spec.loader.exec_module(cr)
held = cr.records(sys.argv[1])
def stats(answers):
    total = distinct = 0; pool = collections.Counter()
    for a in answers:
        ids = cr.IDENT.findall(cr.code_of(a))
        total += len(ids); distinct += len(set(ids)); pool.update(ids)
    top = pool.most_common(3)
    return f"tokens {total}, repeat share {1 - distinct / max(total, 1):.3f}, commonest {', '.join(f'{w} {c / max(total, 1):.3f}' for w, c in top)}"
ks = None
for path in sys.argv[2:]:
    written = []
    for line in open(path, "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            written.append((int(k), text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace").decode("utf-8", "replace")))
    ks = [k for k, _ in written]
    print(f"{path.split('/')[-2]}: {stats([w for _, w in written])}")
print(f"held: {stats([held[k][1] for k in ks])}")
