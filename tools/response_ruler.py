#!/usr/bin/env -S python3 -I
"""A ruler: a receiver's response to a perturbation of each of its sources (the lead, November 17; Brandon's lens of 00:38Z: a level of
loudness says where a basin is driven, a response says what is at stake).

Usage: response_ruler.py table STATE CODEC BASE.tsv OUT.tsv [RECORDS]
       response_ruler.py read DIR

`table` takes a `read-tension` table of records (`label<TAB>prompt<TAB>run<TAB>places`) and writes each record followed by one
perturbed copy for every site of its prompt: that site's symbol replaced by the symbol whose encoding row stands nearest its own in
the state (the smallest change of symbol the field's own geometry offers; printable symbols only, so the table stays text), the run
and the opened places the same. The procedure names no digit and no operator, and is the same for every stream.

`read` pairs each perturbed copy with its record on a `read-tension` directory of that table and prints:

- `RESPONSE_SITE`: by tick and by the perturbed site's distance back from the open place, the mean squared change of the open
  place's pair chart, as a share of the chart's own mean power (its loudness there) and as a share of the responses' sum.
- `RESPONSE_PAIR` (a ruler's labels: the arithmetic layout of the records): the share of the response's power, at a column both
  operands hold, that comes from the two aligned operand digits.
- `RESPONSE_MODES`: products located from the covector alone on the m leading principal coordinates of the responses (the directions
  of the open place's chart that answer when a source changes), by part and tick, on the held half of the records; the same with
  each response scaled to unit length first (`direction`: a source counts once whatever the size of its perturbation); beside the
  chart's leading coordinates of variance and the pair's table. No label enters the coordinates or the legs; the parts and
  the table are the ruler's.

A ruler: it perturbs text outside the machine and reads a state; it writes none.
"""
import hashlib
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def nearest(state, codec):
    with open(state) as f:
        f.readline()
        head = f.readline().split()
        a, d = int(head[1]), int(head[2])
        theta = np.array(f.readline().split()[: (a + 1) * d], dtype=np.float64).reshape(a + 1, d)
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(x) for x in f.readline().split()]
    cls = {b: (k if k < void else k + 1) for k, b in enumerate(units)}
    ok = [b for b in units if 32 <= b < 127 and b != 92]
    rows = theta[[cls[b] for b in ok]]
    rows = rows - rows.mean(axis=0)
    unit = rows / np.linalg.norm(rows, axis=1, keepdims=True)
    cos = unit @ unit.T
    np.fill_diagonal(cos, -2.0)
    return {chr(b): chr(ok[j]) for b, j in zip(ok, cos.argmax(axis=1))}


def table(state, codec, base, out, records=None):
    near = nearest(state, codec)
    n = 0
    with open(base) as f, open(out, "x") as g:
        for k, line in enumerate(f):
            if records is not None and k >= records:
                break
            label, prompt, run, places = line.rstrip("\n").split("\t")
            g.write(f"{label}\t{prompt}\t{run}\t{places}\n")
            for j, c in enumerate(prompt):
                if c == "\\" or c not in near:
                    continue
                g.write(f"resp|{j}|{label}\t{prompt[:j]}{near[c]}{prompt[j + 1:]}\t{run}\t{places}\n")
                n += 1
    digits = "".join(near[str(k)] for k in range(10))
    print(f"RESPONSE_TABLE perturbed={n} nearest_of_0..9={digits} nearest_of_space={near[' ']!r} of_plus={near['+']!r} of_equals={near['=']!r}")


def read(d):
    import tension_ruler as t

    rows, lam, chart, cur, prod, ticks = t.load(d)
    key = {}
    for i, r in enumerate(rows):
        key[(r[0], int(r[1]), int(r[2]))] = i
    base = [i for i, r in enumerate(rows) if not r[0].startswith("resp|")]
    base_of = {}
    deltas, meta = [], []
    for i, r in enumerate(rows):
        if not r[0].startswith("resp|"):
            continue
        _, j, label = r[0].split("|", 2)
        b = key.get((label, int(r[1]), int(r[2])))
        if b is None:
            continue
        deltas.append(chart[i] - chart[b])
        meta.append((b, int(j), int(r[2])))
    deltas = np.array(deltas)
    mb = np.array([m[0] for m in meta])
    mj = np.array([m[1] for m in meta])
    mt = np.array([m[2] for m in meta])
    labels = [rows[b][0] for b in mb]
    half = np.array([hashlib.sha256(f"half:{rows[i][0]}".encode()).digest()[0] % 2 for i in range(len(rows))])
    # The open place's site and the perturbed site's distance back from it.
    prompt_len = np.array([len(l.split(":")[3]) + 3 + len(l.split(":")[4]) + 3 for l in labels])
    place = np.array([int(rows[b][1]) for b in mb])
    back = prompt_len + place - mj
    power = (deltas**2).sum(axis=1)
    loud = (chart[mb] ** 2).sum(axis=1)
    print(f"RESPONSE_READ rows={len(rows)} base_rows={len(base)} responses={len(deltas)} ticks={ticks}")
    print("RESPONSE_SITE tick sites_back responses response_over_loudness share_of_response")
    for k in range(ticks):
        sel = mt == k
        total = power[sel].sum()
        for dist in sorted(set(back[sel])):
            s = sel & (back == dist)
            if s.sum() < 200:
                continue
            print(f"RESPONSE_SITE {k} {dist} {s.sum()} {power[s].mean() / loud[s].mean():.5f} {power[s].sum() / total:.4f}")
    # The aligned pair's share, at a column both operands hold (the ruler's layout of `a + b = value`).
    kinds = {b: t.place_kind(rows[b][0], int(rows[b][1])) for b in set(mb)}
    print("RESPONSE_PAIR tick places share_from_aligned_a share_from_aligned_b share_from_other_digits share_from_signs_and_spaces")
    for k in range(ticks):
        acc = np.zeros(4)
        n = 0
        for b in set(mb[mt == k]):
            kind = kinds[b]
            if kind[7] != 2:
                continue
            _, _, _, a, bb, _ = rows[b][0].split(":")
            kv = kind[2]
            ak, bk = len(a) - 1 - kv, len(a) + 3 + len(bb) - 1 - kv
            s = (mb == b) & (mt == k)
            for j, p in zip(mj[s], power[s]):
                is_digit = j < len(a) or len(a) + 3 <= j < len(a) + 3 + len(bb)
                acc[0 if j == ak else 1 if j == bk else 2 if is_digit else 3] += p
            n += 1
        if n:
            print(f"RESPONSE_PAIR {k} {n} " + " ".join(f"{x:.4f}" for x in acc / acc.sum()))
    # Products on the leading response coordinates, located from the covector alone.
    base = np.array(base)
    kind_b = [t.place_kind(rows[i][0], int(rows[i][1])) for i in base]
    part = np.array([t.PARTS.index(t.part_of(kd)) for kd in kind_b])
    tick = np.array([int(rows[i][2]) for i in base])
    fit, test = half[base] == 0, half[base] == 1
    lam_b, chart_b = lam[base], chart[base]
    da, db = (np.array([kd[i] for kd in kind_b]) for i in (4, 5))
    pair = (t.onehot(da)[:, :, None] * t.onehot(db)[:, None, :]).reshape(len(base), 100)
    print("RESPONSE_MODES part tick test_rows coordinates m linear products_5 products_10 table")
    for pid, pname in enumerate(t.PARTS):
        for k in range(ticks):
            sel = (tick == k) & (part == pid)
            f, te = sel & fit, sel & test
            if te.sum() < 200 or pname == "top":
                continue
            fit_base = set(base[f])
            dsel = np.array([(m[0] in fit_base) and m[2] == k for m in meta])
            _, _, vr = np.linalg.svd(deltas[dsel], full_matrices=False)
            centred = chart_b - chart_b[f].mean(axis=0)
            _, _, vv = np.linalg.svd(centred[f], full_matrices=False)
            unit = deltas[dsel] / np.maximum(np.linalg.norm(deltas[dsel], axis=1, keepdims=True), 1e-12)
            _, _, vu = np.linalg.svd(unit, full_matrices=False)
            for cname, basis in (("response", vr), ("direction", vu), ("variance", vv)):
                for m in (8, 16):
                    z = centred @ basis[:m].T
                    a, b = t.locate(z[f], lam_b[f], 10, sweeps=20, starts=3)
                    out = [t.removed(z, lam_b, f, te)] + [t.removed(np.hstack([z, t.products_of(z, a[:j], b[:j])]), lam_b, f, te) for j in (5, 10)]
                    print(f"RESPONSE_MODES {pname} {k} {te.sum()} {cname} {m} " + " ".join(f"{v:.4f}" for v in out) + f" {t.removed(pair, lam_b, f, te):.4f}", flush=True)


if __name__ == "__main__":
    if len(sys.argv) >= 6 and sys.argv[1] == "table":
        table(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], int(sys.argv[6]) if len(sys.argv) > 6 else None)
    elif len(sys.argv) == 3 and sys.argv[1] == "read":
        read(sys.argv[2])
    else:
        sys.exit(__doc__)
