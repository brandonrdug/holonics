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

state_travel.py scale CONTACTS_BEFORE STATE STATE [STATE ...]: how much of each block's travel is along the block itself (theory,
November 11), from two or more saved states of one line, in order. Every read of a site's face goes through the lane chart, a ratio
to the lane's own power, and the classes are read through the encoding against the lift; so for each lane the code does not change
when everything written into that lane's face coordinates (the letters' rows of enc, before and after, the rows of moment_face, out
and W, the face biases) is scaled by one factor and the lift's rows of that lane by its inverse. Travel along that scale is travel
the code does not read. For each block (a family's entries of one lane, the new contacts' or the old):
  SCALE lap k   the block's rms and its travel's, rho the cosine of the travel with the block at the lap's start, and eps the
                relative lengthening the lap gave it, <d, x> / |x|^2, in parts a thousand;
  SCALE_PAIR    the cosine of two successive laps' travels, and cos_tan, the same cosine with each travel's component along its
                own block removed.
  GAUGE lap k   by lane: eps pooled over the blocks that write the lane's face and over the lift's rows that read it back.
role names a block's place in that scale: writes (the lane's face), lifts (the lift's rows), reads (charts that read the lane's
ratio), other. Numbers only.

state_travel.py weighed CONTACTS_BEFORE SECTIONS SITES STATE STATE STATE [STATE ...]: the lap cosine in the deposit's own metric (theory,
November 11), from three or more saved states of one line, in order; SECTIONS a lap and SITES a lap are the line's (they only set the
unit of the two prices). The deposit steps entry i by 2^-rate m_i / s_i, its first moment over the root s_i of its second, so every
entry's noise travels alike whatever its covector's size, and an entry whose covector is small and of one sign travels as far as any.
A step d changes the section's code by -sum g_i d_i at first order, and a lap's travel reads the mean covector as
g_i = s_i d_i 2^rate / SECTIONS; so the code two laps' common travel is worth weighs each entry's product d1_i d2_i by s_i. s is read
from the state between the two laps (the learner's text: the field's two lines, then the first moments and the second, each on one
line). For each block of `scale` (with carry circles their charts by lane, the turn rows Q and the leak rows H apart, and their
biases q_b and h_b apart: the turn is a phase and the leak a modulus, so one block would mix two laws):
  WEIGHED_LAP   the block's entries and how many have opened (s above 0), its travel's rms, and heat: 2^-rate s_i / 4 summed, the
                standing spread's cost if every entry rests in its own noise (an entry at rest under this step holds a variance
                2^-rate s / 2H at curvature H, a cost 2^-rate s / 4 whatever H), at the rates the lap ran at (the `rates` line of
                the state the lap ended in, each entry's own, or else its `parts` line) and at the base rate, in millionths of a bit a site as a section line prices a step;
                and own, the lap's travel priced at the covector that would have moved it alone, sum s_i d_i^2 2^(rate - 32 -
                2 grain) / SITES in the same unit. A walk of free steps holds 4 heat there between lap ends and two thirds of
                that between lap means, and a part at rest in a well holds less by its relaxation time over the lap; a travel
                that repeats holds the same in own, in fall one lap on and in fall two laps on;
  WEIGHED_PAIR  cos, the plain cosine of two successive laps' travels; cos_w, the cosine with every product weighed by s_i; q1 .. q4,
                the entries in order of falling s cut into four groups of equal summed s, each with its count and its plain cosine
                (q1 the few entries of the largest covectors, q4 the many of the smallest); and fall, the first-order fall of the
                code the later lap's travel made along the drift the earlier lap's travel read, sum s_i d1_i d2_i 2^(rate - 32 -
                2 grain) / SITES, in the same unit (below zero: the later lap went back); eps_w, the weighed cosine's own spread
                if the entries' products had no common sign, the root of sum (s_i d1_i d2_i)^2 over the same norm.
  WEIGHED_LAG   with four states or more: the plain and the weighed cosine of a lap's travel with the travel two laps on, and
                three (weighed by the root after the first), and fall, that product priced as WEIGHED_PAIR's. A block at rest
                about a fixed position, its lap ends related by r^k at k laps, reads -(1 - r)/2 at one lap, -r(1 - r)/2 at two
                and -r^2 (1 - r)/2 at three; a drift adds its share of the squared travel to each. So the three cosines read a
                block's memory and its drift apart. Between lap means a free walk's two successive travels share a sixth of a
                lap's variance (atlas `deposition.lap-mean-quarter-floor`) and travels two laps apart share none, so the fall
                two laps on is the first that holds only what repeats; WEIGHED_LAG_TOTAL sums it over every block.
  WEIGHED_TOTAL the heats and the falls summed over every block. Numbers only.

state_travel.py mean OUT HEAD STATE [STATE ...]: writes OUT, a new file: HEAD's learner text with its material replaced by the mean,
entry by entry, of the STATEs' materials, each mean released to the nearest integer (a half away from zero). Everything else (the
head line with its lap count, the moments, the `parts` line) is HEAD's, so a read of OUT draws the paths and masks a read of HEAD
draws. With one STATE it is that state's material under HEAD's lap count. A state under a deposit at rest is a draw about its rest
position; the mean of draws taken a lap apart lies nearer to it than any of them. OUT is a ruler's state: it is read, and no lap
trains from it. HEAD must hold no held step (a step is of one material). Numbers only.

state_travel.py graft OUT HEAD DONOR FAMILY [FAMILY ...]: writes OUT, a new file: HEAD's learner text with the named families' entries
of its material replaced by DONOR's (the families as `layout` names them: enc, before, after, q, q_bias, v, v_bias, out, out_bias, a,
a_bias, b, b_bias, w, w_bias, read, read_bias, moment_before, moment_after, temper, probe, probe_bias, pace, moment_face,
moment_face_bias, lift_bias, and carry and carry_bias with carry circles, whose turn and leak halves are also named apart: carry/turn,
carry/leak, carry_bias/turn, carry_bias/leak). Every other entry and every other line is HEAD's. A read of OUT beside
HEAD's and DONOR's tells how much of a reading's difference between two states those families carry; where a reading is first order
in the states' difference, the shifts of grafts that partition the material add up to the whole difference, and what the sum leaves
is the reading's curvature between them. A name may also be `part:NAME`, the entries of one founded part as the rate law names
them (tools/part_rates.py: w_new .. b_lane, carry and the first lane's letter rows enc_first, before_first, after_first, and w_carry,
a_carry, b_carry with carry circles), or `FAMILY/old`, a family's entries of no part (the base
rate's); the parts and the families' old entries partition the material, so a lap's difference between two lap means is split by the
rate each entry trains at. A name may also be `block:BLOCK/LANE/CONTACTS`, one block of `scale` as its lines name it (block,
lane and contacts: block:w/2/old, block:moment_before/0/all), the unit the block law of part_rates.py moves (theory, November 12,
G92): the blocks partition the material, so a lap's end against its mean is split by block, each block's shift the code its own
part of the end's displacement costs with every other block at the mean. The parts, the families' old entries and the blocks
read the count of contacts before the growth from HEAD's `parts` line, or from a name `contacts:N` where HEAD carries none (where
it carries one the two agree). No entry is named twice. OUT is a ruler's state: it is read, and no lap trains from it. Numbers
only.
"""
import os
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
    c = d.get("carry", 0)
    if c > 0:
        # [theory, November 11 17:25] The carry circles' charts (turn rows then leak rows) and their biases.
        push("carry", (2 * c, dw), MAT); push("carry_bias", (2 * c,), FACE)
    return fam, at


def state(path):
    lines = open(path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    assert words[0] != "hnn-field-v14k", "the carry founded at zero friction is retired (hnn-field-v14k): its states are receipts only"
    # The carry circles' count: hnn-field-v14e (the leak's log chart) and the retired hnn-field-v14t (its linear chart), read here as receipts
    # (the same layout; only the leak's chart differs).
    d["carry"] = int(words[12]) if words[0] in ("hnn-field-v14e", "hnn-field-v14t") else 0
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


def scale_blocks(d, old_f):
    """[(block, lane, contacts, role, family, mask)]: each family cut by lane and by new or old contacts, with its place in the
    lane's scale (see the docstring)."""
    fam, _ = layout(d)
    shapes = {name: shape for name, _, shape, _ in fam}
    dw, f, lanes = d["width"], d["contacts"], d["lanes"]
    lw = dw // lanes if lanes > 1 else dw
    new_c = np.zeros(f, dtype=bool)
    new_c[old_f // 2:f // 2] = True
    new_c[f // 2 + old_f // 2:] = True
    lane_of = [np.arange(dw) // lw == k for k in range(lanes)]
    out = []

    def add(block, lane, contacts, role, family, mask):
        if mask.any():
            out.append((block, lane, contacts, role, family, mask))

    for k, sel in enumerate(lane_of, 1):
        for name in ("enc", "before", "after"):
            m = np.zeros(shapes[name], dtype=bool); m[:, sel] = True
            add(name, k, "all", "writes", name, m)
        for name in ("moment_face", "out"):
            m = np.zeros(shapes[name], dtype=bool); m[sel, :] = True
            add(name, k, "all", "writes", name, m)
        for sub, cols in (("new", new_c), ("old", ~new_c)):
            m = np.zeros(shapes["w"], dtype=bool); m[np.ix_(sel, cols)] = True
            add("w", k, sub, "writes", "w", m)
        for name in ("out_bias", "w_bias", "moment_face_bias"):
            m = np.zeros(shapes[name], dtype=bool); m[sel] = True
            add(name, k, "all", "writes", name, m)
        m = np.zeros(shapes["read"], dtype=bool); m[sel, :] = True
        add("read_rows", k, "all", "lifts", "read", m)
        m = np.zeros(shapes["lift_bias"], dtype=bool); m[sel] = True
        add("lift_bias", k, "all", "lifts", "lift_bias", m)
        for name in ("q", "v", "probe"):
            m = np.zeros(shapes[name], dtype=bool); m[:, sel] = True
            add(name, k, "all", "reads", name, m)
        for name in ("a", "b"):
            for sub, rows in (("new", new_c), ("old", ~new_c)):
                m = np.zeros(shapes[name], dtype=bool); m[np.ix_(rows, sel)] = True
                add(name, k, sub, "reads", name, m)
    for name in ("a_bias", "b_bias"):
        for sub, rows in (("new", new_c), ("old", ~new_c)):
            m = np.zeros(shapes[name], dtype=bool); m[rows] = True
            add(name, 0, sub, "other", name, m)
    for name in ("q_bias", "v_bias", "probe_bias", "read_bias", "moment_before", "moment_after", "temper", "pace"):
        add(name, 0, "all", "other", name, np.ones(shapes[name], dtype=bool))
    if "carry" in shapes:
        # [theory, November 11 22:40, G87] The circles' turn rows Q (0..C) and leak rows H (C..2C) by lane, and q_b and h_b, apart.
        c = shapes["carry"][0] // 2
        for k, sel in enumerate(lane_of, 1):
            for block, rows in (("carry_turn", slice(0, c)), ("carry_leak", slice(c, 2 * c))):
                m = np.zeros(shapes["carry"], dtype=bool); m[rows, sel] = True
                add(block, k, "all", "reads", "carry", m)
        for block, rows in (("carry_bias_turn", slice(0, c)), ("carry_bias_leak", slice(c, 2 * c))):
            m = np.zeros(shapes["carry_bias"], dtype=bool); m[rows] = True
            add(block, 0, "all", "other", "carry_bias", m)
    return out


def scale(old_f, paths):
    states = [state(p) for p in paths]
    d = states[0][0]
    assert all(s[0] == d for s in states), "states of one declaration"
    assert 0 < old_f <= d["contacts"] and old_f % 4 == 0, "the contacts before the growth, by fours"
    fam, total = layout(d)
    assert all(len(theta) == total for _, theta in states), "the material's length"
    where = {name: (at, shape, grain) for name, at, shape, grain in fam}
    blocks = scale_blocks(d, old_f)
    print(f"# declaration {d}; contacts {old_f} -> {d['contacts']}; lane width {d['width'] // d['lanes']}")
    for i, path in enumerate(paths):
        print(f"# state {i} {path}")

    def take(theta, family, mask):
        at, shape, _ = where[family]
        return theta[at:at + int(np.prod(shape))].reshape(shape)[mask].astype(np.float64)

    forms = [[take(theta, family, mask) for (_, _, _, _, family, mask) in blocks] for _, theta in states]
    rms = lambda x: float(np.sqrt((x ** 2).mean())) if x.size else 0.0
    tans = []
    for k in range(len(states) - 1):
        lap_tan = []
        pooled = {}
        for j, (block, lane, contacts, role, family, mask) in enumerate(blocks):
            x, dv = forms[k][j], forms[k + 1][j] - forms[k][j]
            xx, dd, xd = float(x @ x), float(dv @ dv), float(x @ dv)
            rho = xd / np.sqrt(xx * dd) if xx > 0 and dd > 0 else float("nan")
            eps = xd / xx if xx > 0 else float("nan")
            lap_tan.append((dv, dv - (xd / xx) * x if xx > 0 else dv))
            print(f"TRAVEL_SCALE lap={k} block={block} lane={lane} contacts={contacts} role={role} entries={x.size} form_rms={rms(x):.5g} travel_rms={rms(dv):.5g} rho={rho:+.4f} eps_ppk={1000 * eps:+.4f}")
            if role in ("writes", "lifts"):
                unit = 4.0 ** -where[family][2]
                got = pooled.setdefault((lane, role), [0.0, 0.0])
                got[0] += xd * unit
                got[1] += xx * unit
        for lane in sorted({lane for (lane, _) in pooled}):
            w, r = pooled.get((lane, "writes")), pooled.get((lane, "lifts"))
            f3 = lambda g: f"{1000 * g[0] / g[1]:+.4f}" if g and g[1] > 0 else "nan"
            print(f"TRAVEL_GAUGE lap={k} lane={lane} writes_eps_ppk={f3(w)} lifts_eps_ppk={f3(r)}")
        tans.append(lap_tan)
    for k in range(len(tans) - 1):
        for j, (block, lane, contacts, role, _, _) in enumerate(blocks):
            (d0, t0), (d1, t1) = tans[k][j], tans[k + 1][j]
            cosine = lambda u, v: float(u @ v / np.sqrt((u @ u) * (v @ v))) if (u @ u) > 0 and (v @ v) > 0 else float("nan")
            print(f"TRAVEL_SCALE_PAIR laps={k},{k + 1} block={block} lane={lane} contacts={contacts} role={role} cos={cosine(d0, d1):+.4f} cos_tan={cosine(t0, t1):+.4f}")


def learner(path):
    """A saved learner's declaration, material, the roots of its second moments, its base rate's bits, its `parts` line (None
    without one) and its `rates` line, each entry's own rate (None without one; theory, November 12):
    `(d, theta, s, rate_bits, (contacts_before, octaves), own)`."""
    lines = open(path).read().split("\n")
    d, theta = state(path)
    assert len(lines) > 4, "a learner's text with its two moments' lines"
    first_len = lines[3].count(" ") + 1
    second = np.array(lines[4].split(" "), dtype=np.float64)
    assert first_len == len(theta) == len(second), "each moment's line is the material's length"
    parts, own = None, None
    for line in lines[5:]:
        if line.startswith("parts "):
            v = [int(x) for x in line.split(" ")[1:]]
            parts = (v[0], v[1:])
        elif line.startswith("rates "):
            own = np.array(line.split(" ")[1:], dtype=np.int64)
            assert len(own) == len(theta), "a learner's own rates, one an entry"
    return d, theta, np.sqrt(np.maximum(second, 0.0)), int(lines[0].split(" ")[1]), parts, own


def entry_rates(d, total, rate_bits, parts, own=None):
    """Each entry's deposit rate in bits (FieldLearner::entry_rates): where the state carries each entry's own rate (its `rates` line,
    the block law's; theory, November 12), that rate; otherwise the base rate, less its founded part's octaves, never under one."""
    if own is not None:
        assert len(own) == total, "a learner's own rates, one an entry"
        return np.array(own, dtype=np.int64)
    rates = np.full(total, rate_bits, dtype=np.int64)
    if parts is not None:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import part_rates

        contacts_before, octaves = parts
        founded = np.array(part_rates.founded_parts(d, contacts_before))
        assert len(founded) == total
        for p, k in enumerate(part_rates.expand(d, octaves)):
            rates[founded == p] = max(rate_bits - k, 1)
    return rates


def weighed(old_f, sections, sites, paths):
    states = [learner(p) for p in paths]
    d = states[0][0]
    assert all(s[0] == d for s in states), "states of one declaration"
    assert len(states) >= 3, "two laps, three states"
    assert 0 < old_f <= d["contacts"] and old_f % 4 == 0, "the contacts before the growth, by fours"
    assert sections > 0 and sites > 0
    fam, total = layout(d)
    assert all(len(s[1]) == total for s in states), "the material's length"
    where = {name: (at, shape, grain) for name, at, shape, grain in fam}
    blocks = []
    grain_of = np.zeros(total, dtype=np.int64)
    seen = np.zeros(total, dtype=np.int64)
    for block, lane, contacts, role, family, mask in scale_blocks(d, old_f):
        at, shape, grain = where[family]
        idx = at + np.flatnonzero(mask.ravel())
        grain_of[idx] = grain
        seen[idx] += 1
        blocks.append((block, lane, contacts, role, idx))
    assert (seen == 1).all(), "the blocks hold every entry once"
    print(f"# declaration {d}; contacts {old_f} -> {d['contacts']}; lane width {d['width'] // d['lanes']}; {sections} sections and {sites} sites a lap")
    for i, path in enumerate(paths):
        print(f"# state {i} {path} rate_bits={states[i][3]} parts={'-' if states[i][4] is None else ','.join(str(k) for k in states[i][4][1])} rates={'-' if states[i][5] is None else 'own'}")
    micro = 1e6
    per_section = sites / sections
    travels, rates = [], []
    for k in range(len(states) - 1):
        theta0 = states[k][1]
        _, theta1, s1, rate_bits, parts, own = states[k + 1]
        dv = (theta1 - theta0).astype(np.float64)
        rate = entry_rates(d, total, rate_bits, parts, own)
        heat = np.exp2(-rate.astype(np.float64) - 32) * s1 / (4 * per_section) * micro
        heat_base = np.exp2(-float(rate_bits) - 32) * s1 / (4 * per_section) * micro
        own = s1 * dv * dv * np.exp2(rate.astype(np.float64) - 32 - 2 * grain_of) / sites * micro
        for block, lane, contacts, role, idx in blocks:
            x = dv[idx]
            print(f"TRAVEL_WEIGHED_LAP lap={k} block={block} lane={lane} contacts={contacts} role={role} entries={idx.size} open={int((s1[idx] > 0).sum())} travel_rms={float(np.sqrt((x ** 2).mean())):.5g} heat_micro={float(heat[idx].sum()):.4f} heat_base_micro={float(heat_base[idx].sum()):.4f} own_micro={float(own[idx].sum()):.4f}")
        print(f"TRAVEL_WEIGHED_TOTAL lap={k} heat_micro={float(heat.sum()):.4f} heat_base_micro={float(heat_base.sum()):.4f} own_micro={float(own.sum()):.4f}")
        travels.append(dv)
        rates.append(rate)
    cosine = lambda u, v, w: float((w * u * v).sum() / np.sqrt((w * u * u).sum() * (w * v * v).sum())) if (w * u * u).sum() > 0 and (w * v * v).sum() > 0 else float("nan")
    for k in range(len(travels) - 1):
        s_mid = states[k + 1][2]
        d1, d2 = travels[k], travels[k + 1]
        fall = s_mid * d1 * d2 * np.exp2(rates[k].astype(np.float64) - 32 - 2 * grain_of) / sites * micro
        for block, lane, contacts, role, idx in blocks:
            u, v, w = d1[idx], d2[idx], s_mid[idx]
            order = np.argsort(-w, kind="stable")
            ws = w[order]
            whole = float(ws.sum())
            groups = np.minimum((4 * (np.cumsum(ws) - ws / 2) / whole).astype(np.int64), 3) if whole > 0 else np.zeros(len(ws), dtype=np.int64)
            quarters = []
            for q in range(4):
                sel = order[groups == q]
                quarters.append(f"q{q + 1}_n={sel.size} q{q + 1}_cos={cosine(u[sel], v[sel], np.ones(sel.size)):+.4f}")
            norm = float(np.sqrt((w * u * u).sum() * (w * v * v).sum()))
            spread = float(np.sqrt(((w * u * v) ** 2).sum()) / norm) if norm > 0 else float("nan")
            print(f"TRAVEL_WEIGHED_PAIR laps={k},{k + 1} block={block} lane={lane} contacts={contacts} role={role} cos={cosine(u, v, np.ones(idx.size)):+.4f} cos_w={cosine(u, v, w):+.4f} {' '.join(quarters)} fall_micro={float(fall[idx].sum()):+.4f} eps_w={spread:.4f}")
        print(f"TRAVEL_WEIGHED_TOTAL laps={k},{k + 1} fall_micro={float(fall.sum()):+.4f}")
    # The travel's memory: a lap's travel with the travel two and three laps on (weighed by the root after the first of them).
    for lag in (2, 3):
        for k in range(len(travels) - lag):
            s_after = states[k + 1][2]
            d1, d2 = travels[k], travels[k + lag]
            fall = s_after * d1 * d2 * np.exp2(rates[k].astype(np.float64) - 32 - 2 * grain_of) / sites * micro
            for block, lane, contacts, role, idx in blocks:
                u, v, w = d1[idx], d2[idx], s_after[idx]
                print(f"TRAVEL_WEIGHED_LAG laps={k},{k + lag} lag={lag} block={block} lane={lane} contacts={contacts} role={role} cos={cosine(u, v, np.ones(idx.size)):+.4f} cos_w={cosine(u, v, w):+.4f} fall_micro={float(fall[idx].sum()):+.4f}")
            print(f"TRAVEL_WEIGHED_LAG_TOTAL laps={k},{k + lag} lag={lag} fall_micro={float(fall.sum()):+.4f}")


def mean(out, head, paths):
    lines = open(head).read().split("\n")
    d, theta_head = state(head)
    assert lines[0].split(" ")[0] == "hnn-field-learner-v3" and lines[0].split(" ")[4] == "-", "a learner's text with no held step"
    total = [0] * len(theta_head)
    for p in paths:
        dp, theta = state(p)
        assert dp == d and len(theta) == len(total), "states of one declaration"
        total = [t + int(x) for t, x in zip(total, theta)]
    n = len(paths)
    near = lambda t: (2 * abs(t) + n) // (2 * n) * (1 if t >= 0 else -1)
    material = [near(t) for t in total]
    assert all(-(1 << 31) <= x < (1 << 31) for x in material), "the material's 32-bit carrier"
    lines[2] = " ".join(str(x) for x in material)
    with open(out, "x") as f:
        f.write("\n".join(lines))
    moved = np.array(material, dtype=np.float64) - theta_head.astype(np.float64)
    print(f"STATE_MEAN states={n} entries={len(material)} moved={int((moved != 0).sum())} rms_from_head={float(np.sqrt((moved ** 2).mean())):.5g}")


CARRY_HALVES = ("carry/turn", "carry/leak", "carry_bias/turn", "carry_bias/leak")


def graft(out, head, donor, names):
    lines = open(head).read().split("\n")
    d, theta = state(head)
    dd, other = state(donor)
    assert lines[0].split(" ")[0] == "hnn-field-learner-v3" and lines[0].split(" ")[4] == "-", "a learner's text with no held step"
    fam, total = layout(d)
    assert dd == d and total == len(theta) == len(other), "states of one declaration"
    spans = {name: (at, int(np.prod(shape))) for name, at, shape, _ in fam}
    declared = [n for n in names if n.startswith("contacts:")]
    names = [n for n in names if not n.startswith("contacts:")]
    assert len(declared) <= 1 and names and len(set(names)) == len(names), "names of the layout, each once, and at most one contacts:N"
    founded = None
    if any(n.startswith("part:") or n.startswith("block:") or n.endswith("/old") for n in names):
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import part_rates

        carried = part_rates.parts_line(lines, d)
        before = int(declared[0].split(":", 1)[1]) if declared else None
        assert carried is not None or before is not None, "a part, a block or a family's old entries need HEAD's parts line or contacts:N"
        assert carried is None or before is None or carried[0] == before, "contacts:N is HEAD's parts line's count"
        before = carried[0] if carried is not None else before
        assert 0 < before <= d["contacts"] and before % 4 == 0, "the contacts before the growth, by fours"
        founded = np.array(part_rates.founded_parts(d, before))
        assert len(founded) == total
        blocks = {f"block:{block}/{lane}/{contacts}": (family, mask) for block, lane, contacts, _, family, mask in scale_blocks(d, before)}
    else:
        assert not declared, "contacts:N goes with a part, a block or a family's old entries"
    named = np.zeros(total, dtype=np.int64)
    for n in names:
        chosen = np.zeros(total, dtype=bool)
        if n.startswith("block:"):
            assert n in blocks, f"blocks of scale: {' '.join(blocks)}"
            family, mask = blocks[n]
            chosen[spans[family][0] + np.flatnonzero(mask.ravel())] = True
        elif n.startswith("part:"):
            assert n[5:] in part_rates.PART_NAMES, f"parts of the rate law: {' '.join(part_rates.PART_NAMES)}"
            chosen = founded == part_rates.PART_NAMES.index(n[5:])
        elif n.endswith("/old"):
            assert n[:-4] in spans, f"families of the layout: {' '.join(spans)}"
            at, k = spans[n[:-4]]
            chosen[at:at + k] = founded[at:at + k] == part_rates.OLD
        elif n in CARRY_HALVES:
            family, half = n.split("/")
            assert d["carry"] > 0, f"{n} names a carry circles' half, and this declaration has no circles"
            at, k = spans[family]
            row = k // (2 * d["carry"])  # D entries a row of the charts, one of the biases
            start = at + (0 if half == "turn" else d["carry"] * row)
            chosen[start:start + d["carry"] * row] = True
        else:
            assert n in spans, f"families of the layout, each once: {' '.join(spans)}"
            at, k = spans[n]
            chosen[at:at + k] = True
        assert chosen.any(), f"{n} names no entry of this declaration"
        named += chosen
    assert (named <= 1).all(), "no entry is named twice"
    material = np.where(named == 1, other, theta)
    lines[2] = " ".join(str(int(x)) for x in material)
    with open(out, "x") as f:
        f.write("\n".join(lines))
    moved = (material - theta).astype(np.float64)
    print(f"STATE_GRAFT families={','.join(names)} entries={int(named.sum())} of={total} moved={int((moved != 0).sum())} rms_from_head={float(np.sqrt((moved ** 2).mean())):.5g}")


def main():
    if len(sys.argv) >= 5 and sys.argv[1] == "mean":
        mean(sys.argv[2], sys.argv[3], sys.argv[4:])
        return
    if len(sys.argv) >= 6 and sys.argv[1] == "graft":
        graft(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:])
        return
    if len(sys.argv) >= 8 and sys.argv[1] == "weighed":
        weighed(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5:])
        return
    if len(sys.argv) >= 5 and sys.argv[1] == "rank":
        rank(int(sys.argv[2]), sys.argv[3:])
        return
    if len(sys.argv) >= 5 and sys.argv[1] == "scale":
        scale(int(sys.argv[2]), sys.argv[3:])
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
