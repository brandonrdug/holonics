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

Controls of its weighed reading, on three more drawn states that carry second moments and a `parts` line (the key chart's lane two
octaves fast). In each of two blocks half the entries hold a second moment's root three times the other half's:
  small covectors travel   in `q`'s lane columns the entries of the small root move the same way on both laps and the others reverse
                           entry by entry: the plain cosine 1/2, the weighed cosine 1/4, the last quarter's cosine 1 and the first
                           three near 0; the fall is that of the small entries alone at the lane's rate (1/4 of a millionth);
  large covectors travel   in `v`'s lane columns the reverse: the plain cosine 1/2 again, the weighed 3/4, the first three quarters'
                           cosines 1 and the last 0; the fall 3 millionths;
  heat                     the key chart's lane, two octaves fast, holds four times its base heat (0.2441 of a millionth); the totals
                           are the blocks' sums, and a block that never opened holds none.

Controls of its mean, on the same kind of states: the mean of two materials that differ by one in an entry lies a half away from
zero (1 and 2 give 2, -1 and -2 give -2, 3 and -3 give 0), the mean of three is their third, every line but the material is the
head's, one state under another head is its own material, and a file that stands is not overwritten.
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


def write(path, theta, second=None, parts=None):
    words = ["hnn-field-v14"] + [str(D[k]) for k in ("alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes")] + ["0"]
    with open(path, "w") as f:
        f.write("hnn-field-learner-v3 12 0 0 -\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n")
        if second is not None:
            f.write(" ".join("0" for _ in theta) + "\n" + " ".join(str(int(x)) for x in second) + "\n")
        if parts is not None:
            f.write("parts " + " ".join(str(k) for k in parts) + "\n")


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


def weighed_controls():
    rng = np.random.default_rng(20261113)
    fam, total = state_travel.layout(D)
    where = {name: (a, shape) for name, a, shape, _ in fam}
    dw = D["width"]
    lane = np.arange(dw) >= dw // D["lanes"]
    rows = D["heads"] * D["modes"]  # half the charts' rows

    def view(x, name):
        a, shape = where[name]
        return x[a:a + int(np.prod(shape))].reshape(shape)

    base = rng.integers(-100000, 100000, size=total).astype(np.int64)
    root, step = 1 << 30, 1 << 18
    second = [0] * total  # integers past 64 bits: a second moment is a square on the step's grain

    def set_second(name, r, value):
        a, (_, cols) = where[name]
        for c in np.flatnonzero(lane):
            second[a + r * cols + c] = value

    for name, top in (("q", 3 * root), ("v", 3 * root)):
        for r in range(2 * rows):
            set_second(name, r, (top if r < rows else root) ** 2)
    flip = np.where(np.arange(rows * int(lane.sum())) % 2 == 0, 1, -1).reshape(rows, int(lane.sum()))
    states = [base]
    for lap in range(2):
        theta = states[-1].copy()
        q, v = view(theta, "q"), view(theta, "v")
        turn = flip if lap == 1 else 1
        q[:rows, lane] += step * turn      # the large roots reverse entry by entry
        q[rows:, lane] += step             # the small roots travel
        v[:rows, lane] += step             # the large roots travel
        v[rows:, lane] += step * turn      # the small roots reverse
        states.append(theta)
    sections, sites = 1000, 16_000_000
    octaves = [0] * 16
    octaves[6] = 2  # q_lane
    with tempfile.TemporaryDirectory() as tmp:
        paths = [os.path.join(tmp, f"s{i}") for i in range(3)]
        for p, theta in zip(paths, states):
            write(p, theta, second, [OLD_F] + octaves)
        out_text = io.StringIO()
        with redirect_stdout(out_text):
            state_travel.weighed(OLD_F, sections, sites, paths)
    lines = [l for l in out_text.getvalue().split("\n") if l.startswith("TRAVEL_")]
    pick = lambda kind, **want: [fields(l) for l in lines if l.startswith(kind + " ") and all(fields(l).get(k) == v for k, v in want.items())]
    n = 2 * rows * int(lane.sum())
    # Small covectors travel.
    (pair,) = pick("TRAVEL_WEIGHED_PAIR", block="q", lane="2")
    assert abs(float(pair["cos"]) - 0.5) < 1e-3 and abs(float(pair["cos_w"]) - 0.25) < 1e-3, pair
    assert float(pair["q4_cos"]) > 0.999 and all(abs(float(pair[f"q{i}_cos"])) < 0.06 for i in (1, 2, 3)), pair
    assert int(pair["q4_n"]) == n // 2 and sum(int(pair[f"q{i}_n"]) for i in (1, 2, 3)) == n // 2, pair
    assert abs(float(pair["fall_micro"]) - 0.25) < 1e-3, pair
    assert abs(float(pair["eps_w"]) - (5 * n) ** 0.5 / (2 * n)) < 1e-3, pair
    # Large covectors travel.
    (pair,) = pick("TRAVEL_WEIGHED_PAIR", block="v", lane="2")
    assert abs(float(pair["cos"]) - 0.5) < 1e-3 and abs(float(pair["cos_w"]) - 0.75) < 1e-3, pair
    assert abs(float(pair["q4_cos"])) < 1e-3 and all(float(pair[f"q{i}_cos"]) > 0.999 for i in (1, 2, 3)), pair
    assert abs(float(pair["fall_micro"]) - 3.0) < 1e-3, pair
    # Heat.
    for lap in pick("TRAVEL_WEIGHED_LAP", block="q", lane="2"):
        assert int(lap["entries"]) == n and int(lap["open"]) == n, lap
        assert abs(float(lap["heat_base_micro"]) - 0.2441) < 1e-3 and abs(float(lap["heat_micro"]) - 4 * 0.2441) < 2e-3, lap
    for lap in pick("TRAVEL_WEIGHED_LAP", block="v", lane="2"):
        assert abs(float(lap["heat_micro"]) - 0.2441) < 1e-3 and lap["heat_micro"] == lap["heat_base_micro"], lap
    for lap in pick("TRAVEL_WEIGHED_LAP", block="q", lane="1"):
        assert int(lap["open"]) == 0 and float(lap["heat_micro"]) == 0.0 and float(lap["travel_rms"]) == 0.0, lap
    totals = [fields(l) for l in lines if l.startswith("TRAVEL_WEIGHED_TOTAL ")]
    heats = [t for t in totals if "heat_micro" in t]
    falls = [t for t in totals if "fall_micro" in t]
    assert len(heats) == 2 and all(abs(float(t["heat_micro"]) - 5 * 0.2441) < 2e-3 and abs(float(t["heat_base_micro"]) - 2 * 0.2441) < 1e-3 for t in heats), heats
    assert len(falls) == 1 and abs(float(falls[0]["fall_micro"]) - 3.25) < 1e-3, falls
    print(f"state_travel weighed: {len(lines)} lines, three controls hold")


def lag_controls():
    """Four states: the probe chart's lane columns travel one way on the first lap, wander on the second, and on the third the large
    roots repeat the first lap and the small roots reverse it. Two laps on, the plain cosine is 0 and the weighed one 1/2."""
    rng = np.random.default_rng(20261114)
    fam, total = state_travel.layout(D)
    where = {name: (a, shape) for name, a, shape, _ in fam}
    dw = D["width"]
    lane = np.arange(dw) >= dw // D["lanes"]
    rows = D["heads"] * D["modes"]
    a, (_, cols) = where["probe"]
    root, step = 1 << 30, 1 << 18
    second = [0] * total
    for r in range(2 * rows):
        for c in np.flatnonzero(lane):
            second[a + r * cols + c] = ((3 * root) if r < rows else root) ** 2
    base = rng.integers(-100000, 100000, size=total).astype(np.int64)
    states = [base]
    for lap in range(3):
        theta = states[-1].copy()
        probe = theta[a:a + 2 * rows * cols].reshape(2 * rows, cols)
        if lap == 0:
            probe[:, lane] += step
        elif lap == 1:
            probe[:, lane] += step * rng.choice([-1, 1], size=(2 * rows, int(lane.sum())))
        else:
            probe[:rows, lane] += step
            probe[rows:, lane] -= step
        states.append(theta)
    with tempfile.TemporaryDirectory() as tmp:
        paths = [os.path.join(tmp, f"s{i}") for i in range(4)]
        for p, theta in zip(paths, states):
            write(p, theta, second, [OLD_F] + [0] * 16)
        out_text = io.StringIO()
        with redirect_stdout(out_text):
            state_travel.weighed(OLD_F, 1000, 16_000_000, paths)
    lines = [l for l in out_text.getvalue().split("\n") if l.startswith("TRAVEL_WEIGHED_LAG ")]
    rows_of = [fields(l) for l in lines if fields(l)["block"] == "probe" and fields(l)["lane"] == "2"]
    assert [r["lag"] for r in rows_of] == ["2"], rows_of
    assert abs(float(rows_of[0]["cos"])) < 1e-3 and abs(float(rows_of[0]["cos_w"]) - 0.5) < 1e-3, rows_of
    assert not any(fields(l)["lag"] == "3" for l in lines), "four states hold one pair two laps apart and none three apart"
    print(f"state_travel lag: {len(lines)} lines, the control holds")


def mean_controls():
    rng = np.random.default_rng(20261114)
    _, total = state_travel.layout(D)
    a = rng.integers(-100000, 100000, size=total).astype(np.int64)
    b = a + rng.integers(-9, 10, size=total)
    c = a + rng.integers(-9, 10, size=total)
    a[:3], b[:3], c[:3] = (1, -1, 3), (2, -2, -3), (2, -2, -3)
    second = [7] * total
    with tempfile.TemporaryDirectory() as tmp:
        pa, pb, pc = (os.path.join(tmp, name) for name in "abc")
        write(pa, a, second, [OLD_F] + [0] * 16)
        write(pb, b, second, [OLD_F] + [1] * 16)
        write(pc, c, [9] * total, [OLD_F] + [2] * 16)
        quiet = io.StringIO()
        with redirect_stdout(quiet):
            state_travel.mean(os.path.join(tmp, "two"), pb, [pa, pb])
            state_travel.mean(os.path.join(tmp, "three"), pc, [pa, pb, pc])
            state_travel.mean(os.path.join(tmp, "one"), pc, [pa])
        (_, two), (_, three), (_, one) = (state_travel.state(os.path.join(tmp, name)) for name in ("two", "three", "one"))
        assert list(two[:3]) == [2, -2, 0], two[:3]
        want = [int(np.floor((2 * abs(t) + 3) / 6)) * (1 if t >= 0 else -1) for t in (a + b + c)]
        assert list(three) == want and list(one) == list(a)
        assert abs(two - (a + b) / 2).max() <= 0.5
        for name, head in (("two", pb), ("three", pc), ("one", pc)):
            got, kept = open(os.path.join(tmp, name)).read().split("\n"), open(head).read().split("\n")
            assert len(got) == len(kept) and all(g == k for i, (g, k) in enumerate(zip(got, kept)) if i != 2), name
        try:
            with redirect_stdout(quiet):
                state_travel.mean(os.path.join(tmp, "two"), pb, [pa, pb])
            raise AssertionError("a standing file was overwritten")
        except FileExistsError:
            pass
    print(f"state_travel mean: {len(quiet.getvalue().splitlines())} lines, the controls hold")


def main():
    rank_controls()
    scale_controls()
    weighed_controls()
    lag_controls()
    mean_controls()


if __name__ == "__main__":
    main()
