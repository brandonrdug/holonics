#!/usr/bin/env -S python3 -I
"""Controls of state_travel.py's rank reading on drawn states (host arithmetic; no saved state of a line is read).

Three small states of one declaration are written with a planted travel of the new contacts' W columns and a rows:
  one direction   every new column of W moves along one direction of the width on both laps: pr near 1, the first share and f1 near 1;
  own directions  every new contact's a row moves along its own orthogonal direction on both laps: pr the count of new contacts,
                  f1 one over that count, and the first directions together hold the whole;
  wander          the old contacts move by noise drawn anew each lap: the cosine near zero and the held shares near chance.

Controls of its scale reading, on three more drawn states with a planted travel of the second lane's blocks:
  along itself    `before`'s lane columns lengthen by one part in 64 a lap, the lift's lane rows and bias shorten by the same: rho near 1 and
                  -1, eps near +15.6 and -15.6 parts a thousand, and the lane's pooled lifts read the same;
  across itself   `q`'s lane columns move by one vector orthogonal to them on both laps: rho near 0, both cosines near 1;
  both            `out`'s lane rows lengthen by one part in 64 and move across by a vector of the same length that reverses on the
                  second lap: rho near 0.71, the cosine near 0 and the cosine across near -1.
"""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
import state_travel  # noqa: E402

D = {"alphabet": 5, "width": 16, "heads": 4, "modes": 2, "still": 2, "contacts": 16, "ticks": 4, "frames": 4, "reach": 16, "lanes": 2, "carry": False}
OLD_F = 8


def write(path, theta):
    words = ["hnn-field-v14"] + [str(D[k]) for k in ("alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes")] + ["0"]
    with open(path, "w") as f:
        f.write("hnn-field-learner-v3 12\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n")


def fields(line):
    return {k: v for k, v in (w.split("=", 1) for w in line.split(" ")[1:])}


def rank_controls():
    rng = np.random.default_rng(20261111)
    fam, total = state_travel.layout(D)
    at = {name: a for name, a, _, _ in fam}
    dw, f = D["width"], D["contacts"]
    new_c = np.zeros(f, dtype=bool)
    new_c[OLD_F // 2:f // 2] = True
    new_c[f // 2 + OLD_F // 2:] = True
    n_new = int(new_c.sum())
    base = rng.integers(-1000, 1000, size=total).astype(np.int64)
    direction = rng.integers(-50, 50, size=dw)
    own = np.linalg.qr(rng.normal(size=(dw, dw)))[0][:, :n_new]  # orthonormal columns, one a new contact
    states = [base]
    for lap in range(2):
        theta = states[-1].copy()
        w = theta[at["w"]:at["w"] + dw * f].reshape(dw, f)
        a = theta[at["a"]:at["a"] + f * dw].reshape(f, dw)
        w[:, new_c] += np.outer(direction, np.arange(1, n_new + 1)) * (lap + 1)        # one direction, a contact's own length
        a[new_c] += np.rint(own.T * 4000).astype(np.int64)                              # every contact its own direction
        w[:, ~new_c] += rng.integers(-300, 300, size=(dw, f - n_new))                   # wander
        a[~new_c] += rng.integers(-300, 300, size=(f - n_new, dw))
        states.append(theta)
    with tempfile.TemporaryDirectory() as tmp:
        paths = [os.path.join(tmp, f"s{i}") for i in range(3)]
        for p, theta in zip(paths, states):
            write(p, theta)
        out = io.StringIO()
        with redirect_stdout(out):
            state_travel.rank(OLD_F, paths)
    rows = [l for l in out.getvalue().split("\n") if l.startswith("TRAVEL_")]
    pick = lambda kind, **want: [fields(l) for l in rows if l.startswith(kind + " ") and all(fields(l).get(k) == v for k, v in want.items())]
    # One direction: W's new columns.
    for lap in pick("TRAVEL_LAP", family="w", contacts="new"):
        assert float(lap["pr"]) < 1.01 and float(lap["top1"]) > 0.99, lap
    (pair,) = pick("TRAVEL_PAIR", family="w", contacts="new")
    assert float(pair["cos"]) > 0.99 and float(pair["f1"]) > 0.99, pair
    # Own directions: the new contacts' a rows.
    for lap in pick("TRAVEL_LAP", family="a", contacts="new"):
        assert abs(float(lap["pr"]) - n_new) < 0.05 and abs(float(lap["top1"]) - 1 / n_new) < 0.01, lap
    (pair,) = pick("TRAVEL_PAIR", family="a", contacts="new")
    assert float(pair["cos"]) > 0.99 and abs(float(pair["f1"]) - 1 / n_new) < 0.02 and float(pair["f4"]) > 0.49, pair
    assert abs(float(pair["pr_held"]) - n_new) < 0.1, pair
    # Wander: the old contacts.
    for family in ("w", "a"):
        (pair,) = pick("TRAVEL_PAIR", family=family, contacts="old")
        assert abs(float(pair["cos"])) < 0.3, pair
        assert float(pair["f4"]) < 3 * 4 / dw, pair
    # The untouched family: b's rows did not move.
    for lap in pick("TRAVEL_LAP", family="b"):
        assert float(lap["rms"]) == 0.0, lap
    print(f"state_travel rank: {len(rows)} lines, three controls hold")


def scale_controls():
    rng = np.random.default_rng(20261112)
    fam, total = state_travel.layout(D)
    where = {name: (a, shape) for name, a, shape, _ in fam}
    dw = D["width"]
    lane = np.arange(dw) >= dw // D["lanes"]

    def view(theta, name):
        a, shape = where[name]
        return theta[a:a + int(np.prod(shape))].reshape(shape)

    base = rng.integers(-100000, 100000, size=total).astype(np.int64)
    across = {}
    for name, cut in (("q", lambda m: m[:, lane]), ("out", lambda m: m[lane, :])):
        x = cut(view(base, name)).astype(np.float64).ravel()
        t = rng.normal(size=x.size)
        t -= (t @ x) / (x @ x) * x
        across[name] = t / np.linalg.norm(t)
    states = [base]
    for lap in range(2):
        theta = states[-1].copy()
        before, read, q, out = (view(theta, name) for name in ("before", "read", "q", "out"))
        before[:, lane] += np.rint(before[:, lane] / 64).astype(np.int64)
        read[lane, :] -= np.rint(read[lane, :] / 64).astype(np.int64)
        lift_bias = view(theta, "lift_bias")
        lift_bias[lane] -= np.rint(lift_bias[lane] / 64).astype(np.int64)
        q[:, lane] += np.rint(across["q"] * 20000).astype(np.int64).reshape(q[:, lane].shape)
        x = out[lane, :].astype(np.float64)
        length = np.linalg.norm(x) / 64
        sign = 1 if lap == 0 else -1
        out[lane, :] += np.rint(x / 64 + sign * length * across["out"].reshape(x.shape)).astype(np.int64)
        states.append(theta)
    with tempfile.TemporaryDirectory() as tmp:
        paths = [os.path.join(tmp, f"s{i}") for i in range(3)]
        for p, theta in zip(paths, states):
            write(p, theta)
        out_text = io.StringIO()
        with redirect_stdout(out_text):
            state_travel.scale(OLD_F, paths)
    rows = [l for l in out_text.getvalue().split("\n") if l.startswith("TRAVEL_")]
    pick = lambda kind, **want: [fields(l) for l in rows if l.startswith(kind + " ") and all(fields(l).get(k) == v for k, v in want.items())]
    # Along itself.
    for lap in pick("TRAVEL_SCALE", block="before", lane="2"):
        assert float(lap["rho"]) > 0.999 and abs(float(lap["eps_ppk"]) - 1000 / 64) < 0.1, lap
    for lap in pick("TRAVEL_SCALE", block="read_rows", lane="2"):
        assert float(lap["rho"]) < -0.999 and abs(float(lap["eps_ppk"]) + 1000 / 64) < 0.1, lap
    for lap in pick("TRAVEL_SCALE", block="before", lane="1"):
        assert float(lap["travel_rms"]) == 0.0, lap
    for lap in pick("TRAVEL_GAUGE", lane="2"):
        assert abs(float(lap["lifts_eps_ppk"]) + 1000 / 64) < 0.5 and float(lap["writes_eps_ppk"]) > 0, lap
    (pair,) = pick("TRAVEL_SCALE_PAIR", block="before", lane="2")
    assert float(pair["cos"]) > 0.999, pair
    # Across itself.
    for lap in pick("TRAVEL_SCALE", block="q", lane="2"):
        assert abs(float(lap["rho"])) < 0.05, lap
    (pair,) = pick("TRAVEL_SCALE_PAIR", block="q", lane="2")
    assert float(pair["cos"]) > 0.99 and float(pair["cos_tan"]) > 0.99, pair
    # Both.
    for lap in pick("TRAVEL_SCALE", block="out", lane="2"):
        assert abs(float(lap["rho"]) - 0.7071) < 0.05, lap
    (pair,) = pick("TRAVEL_SCALE_PAIR", block="out", lane="2")
    assert abs(float(pair["cos"])) < 0.1 and float(pair["cos_tan"]) < -0.95, pair
    print(f"state_travel scale: {len(rows)} lines, three controls hold")


def main():
    rank_controls()
    scale_controls()


if __name__ == "__main__":
    main()
