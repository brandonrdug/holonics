#!/usr/bin/env -S python3 -I
"""Controls of block_directions.py on drawn states (four learner texts written here; no saved state is read).

  count     k is the least count of the largest values holding 15/16 of their sum, and 0 where nothing moved;
  planted   a shared travel of one direction in enc's first lane reads k 1 over the whole width and in lane 1, and 0 in lane 2;
            three equal directions in q, one in lane 1 and two in lane 2, read 3, 1 and 2; two directions in out's face rows
            (a block read transposed) read 2, 1 and 1; D2's own count beside; every unplanted block reads 0;
  skipped   blocks whose shapes differ between the states (a, b and w, when the second span's states hold more contacts) are
            named and skipped, and the rest are still read.
"""
import contextlib
import io
import os
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import block_directions as bd  # noqa: E402
import state_travel as st  # noqa: E402

PASSED = []


def check(name, condition):
    if not condition:
        raise SystemExit(f"FAILED {name}")
    PASSED.append(name)


def declaration(contacts):
    return {"alphabet": 3, "width": 8, "heads": 2, "modes": 1, "still": 1, "contacts": contacts, "ticks": 1, "frames": 2, "reach": 16,
            "lanes": 2, "carry": 2, "triads": 0}


def text(d, values):
    """A learner text of declaration d whose material is zero but for the named families."""
    fam, total = st.layout(d)
    theta = np.zeros(total, dtype=np.int64)
    for name, at, shape, _ in fam:
        if name in values:
            v = np.asarray(values[name], dtype=np.int64).reshape(-1)
            assert v.size == int(np.prod(shape)), (name, v.size, shape)
            theta[at:at + v.size] = v
    head = " ".join(str(d[k]) for k in ("alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"))
    return f"hnn-field-learner-v3 12 0 0 -\nhnn-field-v14e {head} 0 {d['carry']}\n" + " ".join(map(str, theta)) + "\n"


def main():
    check("count", bd.k_of(np.array([8.0, 4.0, 2.0, 1.0, 1.0])) == 4)
    check("count of one", bd.k_of(np.array([3.0, 0.0])) == 1)
    check("count of nothing", bd.k_of(np.zeros(4)) == 0)

    e = np.eye(8, dtype=np.int64)
    v = e[0] + 2 * e[1]
    enc1, enc2 = np.outer([1, 2, 3, 4], v), np.outer([2, 1, 1, 1], v)
    x = np.zeros((4, 3), dtype=np.int64)
    x[0, 0] = x[1, 1] = x[2, 2] = 1
    q = x @ np.stack([e[2], e[4], e[7]], axis=1).T
    y = np.zeros((4, 2), dtype=np.int64)
    y[0, 0] = y[1, 1] = 1
    out = np.stack([e[1], e[5]], axis=1) @ y.T
    d4, d8 = declaration(4), declaration(8)
    texts = [text(d4, {}), text(d4, {"enc": enc1, "q": q, "out": out}), text(d8, {}), text(d8, {"enc": enc2, "q": q, "out": out})]
    with tempfile.TemporaryDirectory() as root:
        paths = []
        for i, t in enumerate(texts):
            p = os.path.join(root, f"S{i}")
            with open(p, "w") as f:
                f.write(t)
            paths.append(p)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            rows = bd.read(paths)
    ks = {(name, lane): k for name, lane, k in rows}
    lines = printed.getvalue().splitlines()
    planted = {("enc", "all"): 1, ("enc", 1): 1, ("enc", 2): 0, ("q", "all"): 3, ("q", 1): 1, ("q", 2): 2, ("out", "all"): 2, ("out", 1): 1,
               ("out", 2): 1}
    for key, k in planted.items():
        check(f"planted {key}", ks.get(key) == k)
    check("unplanted blocks read 0", all(k == 0 for key, k in ks.items() if key[0] not in ("enc", "q", "out")))
    check("unplanted blocks read", {name for name, _ in ks} >= {"before", "after", "v", "probe", "read", "moment_face", "carry_turn", "carry_leak"})
    check("D2's own count", any(line.startswith("DIRECTIONS block=q lane=all rows=4 columns=8 k=3 k_d1=3 k_d2=3 ") for line in lines)
          and any(line.startswith("DIRECTIONS block=enc lane=all rows=4 columns=8 k=1 k_d1=1 k_d2=1 ") for line in lines))
    for name in ("a", "b", "w"):
        check(f"skipped {name}", any(line.startswith(f"DIRECTIONS_SKIPPED block={name} ") for line in lines) and (name, "all") not in ks)
    check("range", "DIRECTIONS_RANGE whole-width k from 1 (enc) to 3 (q) over 3 blocks that moved" in lines)
    print(f"block_directions controls: {len(PASSED)} passed")


if __name__ == "__main__":
    main()
