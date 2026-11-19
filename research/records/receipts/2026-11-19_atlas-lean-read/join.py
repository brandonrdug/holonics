#!/usr/bin/env -S python3 -I
import json, os, re, sys, collections
ROOT, DECLS, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
decls = json.load(open(DECLS))
rows, nolean, unresolved, resolved = [], [], [], 0
kinds = collections.Counter()
for shard in sorted(os.listdir(os.path.join(ROOT, "docs/atlas"))):
    if not shard.endswith(".tsv"): continue
    for n, line in enumerate(open(os.path.join(ROOT, "docs/atlas", shard), encoding="utf-8"), 1):
        f = line.rstrip("\n").split("\t")
        if len(f) < 7 or "formal-checked" not in f[6]: continue
        owners = [o.strip() for o in f[5].split(";")]
        leans = [o[2:] for o in owners if o.startswith("L:")]
        rec = {"shard": shard, "line": n, "id": f[0], "expr": f[2], "reads": f[3], "scope": f[4], "grade": f[6], "lean": []}
        if not leans:
            nolean.append(rec); rows.append(rec); continue
        for o in leans:
            word = o.split()[0]
            file, _, decl = word.partition(":")
            file = file[:-5] if file.endswith(".lean") else file
            last = decl.split(".")[-1] if decl else ""
            hits = [d for d in decls.get(last, []) if d["file"].split("/", 1)[1] == file] if last else []
            if not decl:
                rec["lean"].append({"owner": word, "status": "file-only"}); kinds["file-only"] += 1; continue
            if hits:
                h = hits[0]; resolved += 1; kinds[h["kind"]] += 1
                rec["lean"].append({"owner": word, "status": "declared", "kind": h["kind"], "name": h["name"], "stmt": h["stmt"][:1500], "proof": h["proof"]})
            else:
                rec["lean"].append({"owner": word, "status": "not-declared"}); unresolved.append((rec["id"], word)); kinds["not-declared"] += 1
        rows.append(rec)
json.dump(rows, open(OUT, "w"), ensure_ascii=False)
print("formal-checked rows", len(rows), "no L: owner", len(nolean), "L: owners declared", resolved, "kinds", dict(kinds))
open(OUT + ".nolean.txt", "w").write("\n".join(f"{r['shard']}:{r['line']} {r['id']}" for r in nolean) + "\n")
open(OUT + ".undeclared.txt", "w").write("\n".join(f"{i} {w}" for i, w in unresolved) + "\n")
