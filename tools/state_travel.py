#!/usr/bin/env -S python3 -I
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

state_travel.py rank CONTACTS_BEFORE STATE STATE [STATE ...]: the rank of the contacts' travel (theory, November 11), from two or
more saved states of one line, in order. A contact's return column of W and its a and b rows are each one direction of the face's
width. For the new contacts and for the old, each family is read as a matrix of one column a contact:
  FORM  a state's own matrix; LAP k the displacement between states k and k+1: its rms, the participation ratio of its squared
        singular values pr = (sum s^2)^2 / sum s^4 (1: every contact moves along one direction; the count of contacts: every
        contact its own), and the shares of the first and the first four;
  PAIR  k laps k and k+1: the cosine of the two displacements, and how much of lap k+1's squared length lies in the first 1, 2, 4,
        8 and 16 directions of lap k's (f1 .. f16; a drawn subspace holds r / width), with the participation ratio of those held
        shares. Noise that two laps do not share adds only its chance share, so the held shares read the travel the laps have in common.
The old contacts' rows are the reading's own control: they wander. A step is a moment over the root of its second moment, entry by
entry, so a displacement is the drift over its noise and not the covector's sum; where the noise is even along a part the
directions are kept. CONTACTS_BEFORE is the count before the growth (32 for the growth to 64). Numbers only.
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
    if d.get("carry"):
        push("gchart", (f, dw), MAT)
    return fam, at


def state(path):
    lines = open(path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    d["carry"] = words[0] == "hnn-field-v14k"
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


def spectrum(m):
    """The squared singular values' shares of a matrix, largest first, and its left singular vectors."""
    u, sv, _ = np.linalg.svd(m, full_matrices=False)
    total = float((sv ** 2).sum())
    return (sv ** 2 / total if total > 0 else sv * 0.0), u


def shape_line(p):
    """pr, the first share and the first four's, of shares that sum to one."""
    sq = float((p ** 2).sum())
    return (1.0 / sq if sq > 0 else float("nan")), float(p[:1].sum()), float(p[:4].sum())


def held_shares(u, m):
    """How much of m's squared length lies along each column of u (lap k's directions, largest first)."""
    total = float((m ** 2).sum())
    return ((u.T @ m) ** 2).sum(axis=1) / total if total > 0 else np.zeros(u.shape[1])


def contact_forms(d, theta, old_f):
    """{(family, subset): matrix of one column a contact} for W's columns and the a and b rows, new contacts and old."""
    fam, total = layout(d)
    assert total == len(theta), (total, len(theta))
    at = {name: a for name, a, _, _ in fam}
    dw, f = d["width"], d["contacts"]
    new_c = np.zeros(f, dtype=bool)
    new_c[old_f // 2:f // 2] = True
    new_c[f // 2 + old_f // 2:] = True
    w = theta[at["w"]:at["w"] + dw * f].reshape(dw, f).astype(np.float64)
    a = theta[at["a"]:at["a"] + f * dw].reshape(f, dw).astype(np.float64)
    b = theta[at["b"]:at["b"] + f * dw].reshape(f, dw).astype(np.float64)
    out = {}
    for sub, sel in (("new", new_c), ("old", ~new_c)):
        if sel.any():
            out[("w", sub)], out[("a", sub)], out[("b", sub)] = w[:, sel], a[sel].T, b[sel].T
    return out


def rank(old_f, paths):
    states = [state(p) for p in paths]
    d = states[0][0]
    assert all(s[0] == d for s in states), "states of one declaration"
    assert 0 < old_f <= d["contacts"] and old_f % 4 == 0, "the contacts before the growth, by fours"
    forms = [contact_forms(d, theta, old_f) for _, theta in states]
    rms = lambda m: float(np.sqrt((m ** 2).mean())) if m.size else 0.0
    print(f"# declaration {d}; contacts {old_f} -> {d['contacts']}; a drawn subspace of r directions holds r/{d['width']}")
    for i, path in enumerate(paths):
        print(f"# state {i} {path}")
    keys = sorted(forms[0])
    for i in range(len(states)):
        for key in keys:
            m = forms[i][key]
            pr, top1, top4 = shape_line(spectrum(m)[0])
            print(f"TRAVEL_FORM state={i} family={key[0]} contacts={key[1]} columns={m.shape[1]} rms={rms(m):.5g} pr={pr:.2f} top1={top1:.4f} top4={top4:.4f}")
    laps = [{key: forms[i + 1][key] - forms[i][key] for key in keys} for i in range(len(states) - 1)]
    spectra = [{key: spectrum(lap[key]) for key in keys} for lap in laps]
    for k, lap in enumerate(laps):
        for key in keys:
            pr, top1, top4 = shape_line(spectra[k][key][0])
            print(f"TRAVEL_LAP lap={k} family={key[0]} contacts={key[1]} rms={rms(lap[key]):.5g} pr={pr:.2f} top1={top1:.4f} top4={top4:.4f}")
    for k in range(len(laps) - 1):
        for key in keys:
            m0, m1 = laps[k][key], laps[k + 1][key]
            denom = float(np.linalg.norm(m0) * np.linalg.norm(m1))
            cos = float((m0 * m1).sum() / denom) if denom > 0 else float("nan")
            h = held_shares(spectra[k][key][1], m1)
            sq = float((h ** 2).sum())
            held = " ".join(f"f{r}={float(h[:r].sum()):.4f}" for r in (1, 2, 4, 8, 16) if r <= len(h))
            print(f"TRAVEL_PAIR laps={k},{k + 1} family={key[0]} contacts={key[1]} cos={cos:.4f} {held} pr_held={(float(h.sum()) ** 2 / sq if sq > 0 else float('nan')):.2f}")


def main():
    if len(sys.argv) >= 5 and sys.argv[1] == "rank":
        rank(int(sys.argv[2]), sys.argv[3:])
        return
    if len(sys.argv) != 4:
        sys.exit(__doc__)
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


if __name__ == "__main__":
    main()
