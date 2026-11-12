#!/usr/bin/env -S python3 -I
"""block_directions.py A0 A1 B0 B1: how many directions each block's travel holds, by block and by lane (theory, November 12: the
Fable thread's census of directions by block, which asks whether one width read by every block is what each needs), read on the
host from four saved states of one line, lap means in order (no card, no learning; arithmetic on the states' material lines).

D1 = A1 - A0 and D2 = B1 - B0 are two spans of the line's travel that share no lap. Each block whose entries have a face side (the
width D) is read as a matrix with the face side as its columns: enc, before, after, q, v, probe, a, b, read as stored, the carry
circles' turn rows and leak rows apart, the triads' three legs apart; out, moment_face, w and w_triad transposed. For each block,
over the whole width and over each lane's columns:
  cross  the singular values of D1^T D2, the travel both spans share: a direction one span holds and the other does not (its heat,
         a walk's noise about the drift) adds nothing to it on the mean. Printed as shares of their sum, largest first;
  k      the least count of those directions whose singular values hold 15/16 of their sum (0 where the block did not move);
  k_d1, k_d2  the same count on D1's and on D2's own singular values (heat included).
rms_d1 and rms_d2 are the spans' rms entries in the block's integers. A block whose shape differs between the states is named
SKIPPED. Floats here are a ruler's, on the host. Numbers only.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import state_travel as st  # noqa: E402

KEEP, OF = 15, 16
TRANSPOSED = ("out", "moment_face", "w", "w_triad")


def blocks(d, theta):
    """{block: matrix with the face side as its columns} of one state."""
    fam, total = st.layout(d)
    assert total == len(theta), (total, len(theta))
    out = {}
    for name, at, shape, _ in fam:
        if len(shape) != 2:
            continue
        m = theta[at:at + shape[0] * shape[1]].reshape(shape).astype(np.float64)
        if name in TRANSPOSED:
            m = m.T
        if m.shape[1] != d["width"]:
            continue
        if name == "carry":
            c = m.shape[0] // 2
            out["carry_turn"], out["carry_leak"] = m[:c], m[c:]
        elif name == "triad":
            j = m.shape[0] // 6
            out["triad_a"], out["triad_b"], out["triad_g"] = m[:2 * j], m[2 * j:4 * j], m[4 * j:]
        else:
            out[name] = m
    return out


def k_of(s):
    """The least count of the largest values holding KEEP/OF of their sum (0 for a sum of 0)."""
    total = float(s.sum())
    if total <= 0:
        return 0
    return int(np.argmax(np.cumsum(s) * OF >= KEEP * total)) + 1


def read(paths):
    states = [st.state(p) for p in paths]
    widths = {s[0]["width"] for s in states}
    lanes = {s[0]["lanes"] for s in states}
    assert len(widths) == 1 and len(lanes) == 1, "four states of one width and one lane count"
    width, lane_count = widths.pop(), lanes.pop()
    lane_width = width // lane_count
    forms = [blocks(d, theta) for d, theta in states]
    for i, (path, (d, _)) in enumerate(zip(paths, states)):
        print(f"# state {'A0 A1 B0 B1'.split()[i]} {path} declaration {d}")
    print(f"# D1 = A1 - A0, D2 = B1 - B0; k holds {KEEP}/{OF} of the singular values' sum; a lane is {lane_width} columns of {width}")
    rows = []
    for name in forms[0]:
        shapes = {f[name].shape if name in f else None for f in forms}
        if len(shapes) != 1:
            print(f"DIRECTIONS_SKIPPED block={name} shapes={sorted(map(str, shapes))}")
            continue
        d1, d2 = forms[1][name] - forms[0][name], forms[3][name] - forms[2][name]
        for lane in ["all"] + list(range(1, lane_count + 1)):
            cols = slice(None) if lane == "all" else slice((lane - 1) * lane_width, lane * lane_width)
            a, b = d1[:, cols], d2[:, cols]
            cross = np.linalg.svd(a.T @ b, compute_uv=False)
            total = float(cross.sum())
            shares = ",".join(f"{v / total:.4f}" for v in cross) if total > 0 else "-"
            k = k_of(cross)
            k1, k2 = k_of(np.linalg.svd(a, compute_uv=False)), k_of(np.linalg.svd(b, compute_uv=False))
            rms1, rms2 = float(np.sqrt((a ** 2).mean())), float(np.sqrt((b ** 2).mean()))
            print(f"DIRECTIONS block={name} lane={lane} rows={a.shape[0]} columns={a.shape[1]} k={k} k_d1={k1} k_d2={k2} "
                  f"rms_d1={rms1:.5g} rms_d2={rms2:.5g} cross={shares}")
            rows.append((name, lane, k))
    whole = [(name, k) for name, lane, k in rows if lane == "all" and k > 0]
    if whole:
        lo, hi = min(whole, key=lambda r: r[1]), max(whole, key=lambda r: r[1])
        print(f"DIRECTIONS_RANGE whole-width k from {lo[1]} ({lo[0]}) to {hi[1]} ({hi[0]}) over {len(whole)} blocks that moved")
    return rows


def main(argv):
    if len(argv) != 5:
        raise SystemExit(__doc__)
    read(argv[1:])


if __name__ == "__main__":
    main(sys.argv)
