#!/usr/bin/env -S python3 -I
"""Controls of state_travel.py's rank reading on drawn states (host arithmetic; no saved state of a line is read).

Three small states of one declaration are written with a planted travel of the new contacts' W columns and a rows:
  one direction   every new column of W moves along one direction of the width on both laps: pr near 1, the first share and f1 near 1;
  own directions  every new contact's a row moves along its own orthogonal direction on both laps: pr the count of new contacts,
                  f1 one over that count, and the first directions together hold the whole;
  wander          the old contacts move by noise drawn anew each lap: the cosine near zero and the held shares near chance.
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


def main():
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


if __name__ == "__main__":
    main()
