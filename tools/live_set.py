#!/usr/bin/env -S python3 -I
"""live_set.py: the live set, by coverage (C1 of the consolidation, #603; docs/plans/THE_CONSOLIDATION.md §9). A host instrument: it reads
what an instrumented build of the line's binary executed and writes the receipt's tables. No law, no state.

  live_set.py tables EXPORT.json ROOT OUT_DIR [PROFILE_LOG ...]
      EXPORT.json: `llvm-cov export -summary-only` of the instrumented binary over the run's merged profile. ROOT: the tree the binary was
      built from (a file's name is written relative to it; files outside it, the standard library's and the registry's, are counted apart).
      PROFILE_LOG: logs of the same build run with FIELD_PROFILE, whose `FIELD_PROFILE entry=<kernel> launches=<n>` lines give the kernels
      launched. Writes OUT_DIR/rust_files.tsv (file, executed lines, lines, executed functions, functions; every file of the tree the
      export names, the executed first) and OUT_DIR/kernels.tsv (kernel, launches, summed over the logs).
  live_set.py score RUST_FILES.tsv PREDICTION.txt
      PREDICTION.txt: one path a line (a directory ending in `/` predicts every file under it, a line with `*` is a pattern whose `*`
      reaches across directories; `#` starts a comment). Prints the executed
      files the prediction holds, the executed files it does not (the dependencies the plan missed), and the predicted files that executed
      no line.

  live_set.py declared KERNELS.tsv OUT.tsv SOURCE ...
      Joins the launched kernels to the `__global__` kernels the CUDA SOURCEs declare: OUT.tsv (kernel, source, launches; a declared
      kernel the run never launched has 0), and prints the launched kernels no source declares.

A file "executes" when at least one of its lines ran. Numbers only.
"""
import fnmatch
import json
import os
import re
import sys


def tables(export_path, root, out_dir, logs):
    data = json.load(open(export_path))
    root = os.path.realpath(root).rstrip("/") + "/"
    rows, outside = [], [0, 0]
    for block in data["data"]:
        for f in block["files"]:
            name = os.path.realpath(f["filename"])
            s = f["summary"]
            lines, funcs = s["lines"], s["functions"]
            if not name.startswith(root):
                outside[0] += 1
                outside[1] += int(lines["covered"] > 0)
                continue
            rows.append((name[len(root):], lines["covered"], lines["count"], funcs["covered"], funcs["count"]))
    rows.sort(key=lambda r: (r[1] == 0, r[0]))
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "rust_files.tsv"), "w") as w:
        w.write("file\texecuted_lines\tlines\texecuted_functions\tfunctions\n")
        for r in rows:
            w.write("\t".join(str(v) for v in r) + "\n")
    kernels = {}
    pat = re.compile(r"^FIELD_PROFILE entry=(\S+) launches=(\d+)")
    for log in logs:
        for line in open(log):
            m = pat.match(line)
            if m:
                kernels[m.group(1)] = kernels.get(m.group(1), 0) + int(m.group(2))
    with open(os.path.join(out_dir, "kernels.tsv"), "w") as w:
        w.write("kernel\tlaunches\n")
        for k, n in sorted(kernels.items(), key=lambda kv: (-kv[1], kv[0])):
            w.write(f"{k}\t{n}\n")
    executed = sum(1 for r in rows if r[1] > 0)
    print(f"LIVE_SET files={len(rows)} executed={executed} outside_files={outside[0]} outside_executed={outside[1]} kernels={len(kernels)} launches={sum(kernels.values())}")
    return rows, kernels


def read_rows(path):
    out = []
    with open(path) as f:
        next(f)
        for line in f:
            name, el, ln, ef, fn = line.rstrip("\n").split("\t")
            out.append((name, int(el), int(ln), int(ef), int(fn)))
    return out


def covers(p, name):
    return name == p or (p.endswith("/") and name.startswith(p)) or ("*" in p and fnmatch.fnmatchcase(name, p))


def predicted(prediction, name):
    return any(covers(p, name) for p in prediction)


def score(rows_path, prediction_path):
    rows = read_rows(rows_path)
    prediction = [l.split("#")[0].strip() for l in open(prediction_path)]
    prediction = [p for p in prediction if p]
    executed = [r[0] for r in rows if r[1] > 0]
    held = [n for n in executed if predicted(prediction, n)]
    missed = [n for n in executed if not predicted(prediction, n)]
    idle = [p for p in prediction if not any(covers(p, n) for n in executed)]
    print(f"LIVE_SET_SCORE executed={len(executed)} predicted_and_executed={len(held)} executed_outside_prediction={len(missed)} predicted_not_executed={len(idle)}")
    for n in missed:
        print(f"MISSED {n}")
    for p in idle:
        print(f"IDLE {p}")
    return held, missed, idle


GLOBAL = re.compile(r"__global__\s+void\s+(?:__launch_bounds__\s*\([^)]*\)\s*)?(\w+)(\s*##\s*\w+)?\s*\(")


def declared(kernels_path, out_path, sources):
    launched = {}
    with open(kernels_path) as f:
        next(f)
        for line in f:
            k, n = line.rstrip("\n").split("\t")
            launched[k] = int(n)
    decl = {}  # a kernel named in a macro (`name##PARAM`) is the family `name*`, whose launches are its instances'
    for src in sources:
        for m in GLOBAL.finditer(open(src).read()):
            decl.setdefault(m.group(1) + ("*" if m.group(2) else ""), os.path.basename(src))

    def launches(k):
        return sum(n for name, n in launched.items() if fnmatch.fnmatchcase(name, k)) if k.endswith("*") else launched.get(k, 0)

    def known(name):
        return name in decl or any(k.endswith("*") and fnmatch.fnmatchcase(name, k) for k in decl)

    rows = sorted(((k, f, launches(k)) for k, f in decl.items()), key=lambda r: (r[2] == 0, r[1], r[0]))
    with open(out_path, "w") as w:
        w.write("kernel\tsource\tlaunches\n")
        for r in rows:
            w.write(f"{r[0]}\t{r[1]}\t{r[2]}\n")
    undeclared = sorted(k for k in launched if not known(k))
    print(f"LIVE_SET_KERNELS declared={len(decl)} launched={sum(1 for r in rows if r[2])} not_launched={sum(1 for r in rows if not r[2])} launched_undeclared={len(undeclared)}")
    for k in undeclared:
        print(f"UNDECLARED {k}")
    return rows, undeclared


def main(argv):
    if len(argv) >= 5 and argv[1] == "tables":
        tables(argv[2], argv[3], argv[4], argv[5:])
    elif len(argv) >= 5 and argv[1] == "declared":
        declared(argv[2], argv[3], argv[4:])
    elif len(argv) == 4 and argv[1] == "score":
        score(argv[2], argv[3])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv)
