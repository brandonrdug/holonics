#!/usr/bin/env -S python3 -I
"""Controls for live_set.py: an export of known files and a profile log of known launches give the tables they should, and a prediction is
scored with its misses and its idle entries named."""
import io
import json
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import live_set  # noqa: E402


def summary(lines_covered, lines, funcs_covered, funcs):
    return {"lines": {"covered": lines_covered, "count": lines}, "functions": {"covered": funcs_covered, "count": funcs}}


def main():
    with tempfile.TemporaryDirectory() as tmp:
        root = os.path.join(tmp, "tree")
        for rel in ("crates/a/src/lib.rs", "crates/a/src/b.rs", "crates/c/src/lib.rs"):
            os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
            open(os.path.join(root, rel), "w").close()
        export = {"data": [{"files": [
            {"filename": os.path.join(root, "crates/a/src/lib.rs"), "summary": summary(10, 40, 2, 5)},
            {"filename": os.path.join(root, "crates/a/src/b.rs"), "summary": summary(0, 30, 0, 3)},
            {"filename": os.path.join(root, "crates/c/src/lib.rs"), "summary": summary(5, 5, 1, 1)},
            {"filename": "/rustc/library/core/src/option.rs", "summary": summary(3, 100, 1, 10)},
        ]}]}
        ep = os.path.join(tmp, "export.json")
        json.dump(export, open(ep, "w"))
        log = os.path.join(tmp, "profile.log")
        open(log, "w").write("FIELD_PROFILE entry=field_open launches=4 ms=1\nFIELD_PROFILE entry=field_tick launches=16 ms=2\nOTHER line\n")
        log2 = os.path.join(tmp, "profile2.log")
        open(log2, "w").write("FIELD_PROFILE entry=field_open launches=6 ms=1\n")
        out = os.path.join(tmp, "out")
        buf = io.StringIO()
        with redirect_stdout(buf):
            rows, kernels = live_set.tables(ep, root, out, [log, log2])
        assert "files=3 executed=2 outside_files=1 outside_executed=1 kernels=2 launches=26" in buf.getvalue(), buf.getvalue()
        assert [r[0] for r in rows] == ["crates/a/src/lib.rs", "crates/c/src/lib.rs", "crates/a/src/b.rs"], rows
        assert kernels == {"field_open": 10, "field_tick": 16}
        rf = open(os.path.join(out, "rust_files.tsv")).read().splitlines()
        assert rf[0] == "file\texecuted_lines\tlines\texecuted_functions\tfunctions" and rf[1] == "crates/a/src/lib.rs\t10\t40\t2\t5", rf
        kt = open(os.path.join(out, "kernels.tsv")).read().splitlines()
        assert kt == ["kernel\tlaunches", "field_tick\t16", "field_open\t10"], kt
        pred = os.path.join(tmp, "prediction.txt")
        open(pred, "w").write("crates/a/  # every file of a\ncrates/z/src/lib.rs\n\n")
        pred2 = os.path.join(tmp, "prediction2.txt")
        open(pred2, "w").write("crates/*/lib.rs\ncrates/*/mod.rs\n")
        buf = io.StringIO()
        with redirect_stdout(buf):
            held, missed, idle = live_set.score(os.path.join(out, "rust_files.tsv"), pred)
        assert held == ["crates/a/src/lib.rs"] and missed == ["crates/c/src/lib.rs"] and idle == ["crates/z/src/lib.rs"], (held, missed, idle)
        assert "MISSED crates/c/src/lib.rs" in buf.getvalue() and "IDLE crates/z/src/lib.rs" in buf.getvalue()
        with redirect_stdout(io.StringIO()):
            held, missed, idle = live_set.score(os.path.join(out, "rust_files.tsv"), pred2)
        assert held == ["crates/a/src/lib.rs", "crates/c/src/lib.rs"] and missed == [] and idle == ["crates/*/mod.rs"], (held, missed, idle)
        cu = os.path.join(tmp, "k.cu")
        open(cu, "w").write('extern "C" __global__ void field_open(int a) {}\nextern "C" __global__ void __launch_bounds__(256) field_tick(int b) {}\n'
                            '__global__ void field_idle(int c) {}\n#define C(L) extern "C" __global__ void __launch_bounds__(32, 6) field_c_l##L(int w) {}\n')
        kt2 = os.path.join(out, "kernels.tsv")
        open(kt2, "a").write("field_ghost\t3\nfield_c_l5\t2\nfield_c_l6\t1\n")
        with redirect_stdout(io.StringIO()):
            rows, undeclared = live_set.declared(kt2, os.path.join(out, "declared.tsv"), [cu])
        assert rows == [("field_c_l*", "k.cu", 3), ("field_open", "k.cu", 10), ("field_tick", "k.cu", 16), ("field_idle", "k.cu", 0)] and undeclared == ["field_ghost"], (rows, undeclared)
    print("live_set controls: 9 passed")


if __name__ == "__main__":
    main()
