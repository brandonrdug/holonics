#!/usr/bin/env python3 -I
"""state_travel.py G L2 L4: the travel of a grown field's entries, read on the host from three saved learner states (no card, no
learning; arithmetic on the states' material lines).

G is the state a growth in contacts wrote (Field::contacted: 32 pair contacts added, f 32 -> 64), L2 and L4 later states of the
same line (hnn-field-learner-v3 text: line 3 is the field's material, one integer an entry). Each family's entries are split into
  new   the new contacts' entries: the a and b rows, W's columns, the contacts' biases of the contacts Field::contacted founded
        (real parts at 16..31, imaginary parts at 48..63 of 64);
  lane  the entries the lane growth founded (Field::laned: the face coordinates past the first lane, `width/lanes ..`), where not new:
        the columns of the key, value, probe, pair-drive charts and the encodings, the rows of the current's return, W,
        the moment's chart, and the readout's lift's rows and columns, and the face biases' entries;
  old   the rest.
For each (family, subset): the rms of the entries at G, L2 and L4; the rms displacement from G at L2 and L4 and their ratio
disp(L4)/disp(L2); the cosine of the displacements L2-G and L4-L2 (1: one straight line, 0: wandering). Raw integers and in the
family's own unit (an entry over 2^grain: 2^-16 for the face's grain, 2^-24 the material's). Then W's new columns' rms at L4
against the old columns'. Numbers only.
"""
import sys

import numpy as np


def layout(d):
    a, dw, heads, modes, still, f, frames, lanes = d["alphabet"], d["width"], d["heads"], d["modes"], d["still"], d["contacts"], d["frames"], d["lanes"]
    m2 = 2 * heads * modes
    tm = sum(1 for h in range(heads) if h % frames >= still) * modes
    paced = sum(1 for h in range(heads) if h % frames >= still)
    FACE, MAT = 16, 24
    fam = []
    at = 0

    def push(name, shape, grain):
        nonlocal at
        n = int(np.prod(shape))
        fam.append((name, at, shape, grain))
        at += n

    push("enc", (a + 1, dw), FACE); push("before", (a + 1, dw), FACE); push("after", (a + 1, dw), FACE)
    push("q", (m2, dw), MAT); push("q_bias", (m2,), FACE); push("v", (m2, dw), MAT); push("v_bias", (m2,), FACE)
    push("out", (dw, m2), MAT); push("out_bias", (dw,), FACE)
    push("a", (f, dw), MAT); push("a_bias", (f,), FACE); push("b", (f, dw), MAT); push("b_bias", (f,), FACE)
    push("w", (dw, f), MAT); push("w_bias", (dw,), FACE)
    push("read", (dw, dw), MAT); push("read_bias", (a,), FACE)
    push("moment_before", ((a + 1) * 2 * tm,), FACE); push("moment_after", ((a + 1) * 2 * tm,), FACE)
    push("temper", (2 * heads,), MAT)
    push("probe", (m2, dw), MAT); push("probe_bias", (m2,), FACE)
    push("pace", (paced * (a + 1),), MAT)
    push("moment_face", (dw, m2), MAT); push("moment_face_bias", (dw,), FACE); push("lift_bias", (dw,), FACE)
    return fam, at


def state(path):
    lines = open(path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    theta = np.array([int(x) for x in lines[2].split(" ")], dtype=np.int64)
    return d, theta


def masks(name, shape, d, old_f, new_f):
    """Boolean arrays (new, lane) over a family's shape; old is the rest."""
    dw, lanes = d["width"], d["lanes"]
    lane_from = dw // lanes if lanes > 1 else dw
    f = d["contacts"]
    new_contact = np.zeros(f, dtype=bool)
    # Field::contacted: old real parts keep 0..old_f/2, the new real parts follow (old_f/2 .. new_f/2), the old imaginary parts then
    # the new ones in the second half.
    half_old, half_new = old_f // 2, new_f // 2
    new_contact[half_old:half_new] = True
    new_contact[half_new + half_old:] = True
    new = np.zeros(shape, dtype=bool)
    lane = np.zeros(shape, dtype=bool)
    if name in ("a", "b"):
        new[new_contact, :] = True
        lane[:, lane_from:] = True
    elif name in ("a_bias", "b_bias"):
        new[new_contact] = True
    elif name == "w":
        new[:, new_contact] = True
        lane[lane_from:, :] = True
    elif name in ("enc", "before", "after", "q", "v", "probe"):
        lane[:, lane_from:] = True
    elif name in ("out", "moment_face"):
        lane[lane_from:, :] = True
    elif name == "read":
        lane[lane_from:, :] = True
        lane[:, lane_from:] = True
    elif name in ("out_bias", "w_bias", "moment_face_bias", "lift_bias"):
        lane[lane_from:] = True
    lane &= ~new
    return new, lane


def main():
    g_path, l2_path, l4_path = sys.argv[1:4]
    (dg, g), (d2, l2), (d4, l4) = state(g_path), state(l2_path), state(l4_path)
    assert dg == d2 == d4, (dg, d2, d4)
    fam, total = layout(dg)
    assert total == len(g) == len(l2) == len(l4), (total, len(g), len(l2), len(l4))
    old_f = dg["contacts"] // 2  # the growth doubled the contacts
    new_f = dg["contacts"]
    rms = lambda x: float(np.sqrt(np.mean(x.astype(np.float64) ** 2))) if x.size else 0.0
    print(f"# G {g_path}\n# L2 {l2_path}\n# L4 {l4_path}\n# declaration {dg}; contacts {old_f} -> {new_f}; lane coordinates from {dg['width'] // dg['lanes']}")
    print("family\tsubset\tentries\tgrain\trms_G\trms_L2\trms_L4\tdisp_L2\tdisp_L4\tratio_L4_L2\tcos_L2G_L4L2\t(rms in raw integers; units are the same over 2^grain)")
    rows = {}
    for name, at, shape, grain in fam:
        n = int(np.prod(shape))
        gg, a2, a4 = (x[at:at + n].reshape(shape) for x in (g, l2, l4))
        new, lane = masks(name, shape, dg, old_f, new_f)
        for sub, m in (("old", ~(new | lane)), ("new", new), ("lane", lane)):
            if not m.any():
                continue
            v0, v2, v4 = gg[m], a2[m], a4[m]
            d2, d42 = (v2 - v0).astype(np.float64), (v4 - v2).astype(np.float64)
            d4 = (v4 - v0).astype(np.float64)
            r2, r4 = rms(d2), rms(d4)
            denom = np.linalg.norm(d2) * np.linalg.norm(d42)
            cos = float(d2 @ d42 / denom) if denom > 0 else float("nan")
            rows[(name, sub)] = (rms(v0), rms(v2), rms(v4))
            print(f"{name}\t{sub}\t{m.sum()}\t{grain}\t{rms(v0):.4g}\t{rms(v2):.4g}\t{rms(v4):.4g}\t{r2:.4g}\t{r4:.4g}\t{(r4 / r2 if r2 > 0 else float('nan')):.4f}\t{cos:.3f}")
    # The same in the family's own unit (entry / 2^grain) for the contacts' families and their lane entries.
    print("# in the family's own unit (entry / 2^grain): family subset rms_G rms_L4 disp_L2 disp_L4")
    for name, at, shape, grain in fam:
        n = int(np.prod(shape))
        gg, a2, a4 = (x[at:at + n].reshape(shape) for x in (g, l2, l4))
        new, lane = masks(name, shape, dg, old_f, new_f)
        for sub, m in (("old", ~(new | lane)), ("new", new), ("lane", lane)):
            if not m.any() or not (name in ("w", "a", "b", "a_bias", "b_bias") or sub == "lane"):
                continue
            s = 2.0 ** -grain
            print(f"{name}\t{sub}\t{rms(gg[m]) * s:.5g}\t{rms(a4[m]) * s:.5g}\t{rms((a2 - gg)[m]) * s:.5g}\t{rms((a4 - gg)[m]) * s:.5g}")
    # W per column (a contact's return into the face, over the face coordinates of the first lane and the lane): the spread of the
    # columns' rms at L4 and of their displacements' ratio, the new columns and the old.
    at_w = next(at for name, at, _, _ in fam if name == "w")
    dw_, f_ = dg["width"], dg["contacts"]
    cols = [x[at_w:at_w + dw_ * f_].reshape(dw_, f_).astype(np.float64) for x in (g, l2, l4)]
    new_c = np.zeros(f_, dtype=bool)
    new_c[old_f // 2:new_f // 2] = True
    new_c[new_f // 2 + old_f // 2:] = True
    for label, sel in (("new", new_c), ("old", ~new_c)):
        c4 = np.sqrt((cols[2][:, sel] ** 2).mean(axis=0))
        d2c = np.sqrt(((cols[1] - cols[0])[:, sel] ** 2).mean(axis=0))
        d4c = np.sqrt(((cols[2] - cols[0])[:, sel] ** 2).mean(axis=0))
        q = lambda v: "/".join(f"{x:.4g}" for x in (v.min(), np.median(v), v.max()))
        print(f"W columns {label} ({sel.sum()}): rms at L4 min/median/max {q(c4)}; disp(L2) {q(d2c)}; disp(L4) {q(d4c)}; ratio L4/L2 {q(d4c / np.where(d2c > 0, d2c, np.nan))}")
    w_new, w_old = rows[("w", "new")], rows[("w", "old")]
    print(f"W: new columns' rms at L4 {w_new[2]:.4g} against the old columns' {w_old[2]:.4g}: ratio {w_new[2] / w_old[2]:.3f} (at G: new {w_new[0]:.4g}, old {w_old[0]:.4g}; at L2: new {w_new[1]:.4g}, old {w_old[1]:.4g})")


main()
