#!/usr/bin/env python3
"""Whether a tower's state at a label still carries the image: an exterior exact probe.

Usage:
  python3 -I tools/listener/probe.py faces TRAIN.bin HELD.bin WIDTH LEVELS MODES  # read-tower-classes-at
  python3 -I tools/listener/probe.py chart PREFIX                                 # the foil

An exterior reading, never learner material, and no floats. `faces` reads the records
`read-tower-classes-at` writes (LE u32 class, WIDTH LE i32 top face on 2^-16, then LEVELS x MODES
(re, im) LE i64 carried modes), read as integers: a common scale cancels in every comparison. It
probes three readings of one cell: the top face (what the readout reads), the carried modes, and
each mode's energy re^2 + im^2 (blind to the mode's phase). `chart` reads `compose.py`'s digit class and mark files, takes
every image->label section (marks stroke 5, end 7, label 1), draws the stroke back to its raster
(`render.py`) and pools it 4x4 to 7x7, so the same probe reads what the chart itself carries.

Both probes are fitted on the training cells and name the held-out cells; ties name the smaller class.
- nearest class mean: argmin_c sum_k (n_c x_k - S_ck)^2 / n_c^2, compared as Fractions;
- the same, each coordinate scaled by its pooled within-class scatter W_kk (coordinates with
  W_kk = 0 dropped), so no coordinate's grain decides the reading;
- pooled within-class covariance, equal priors: a_c = W^-1 mu_c by an exact solve and
  g_c(x) = a_c.x - a_c.mu_c / 2 (the pooled covariance's factor N - K cancels); refused when W is
  singular, and read only up to 64 coordinates (the exact solve's cost grows as the cube).
"""

from fractions import Fraction
from pathlib import Path
import struct
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import render  # noqa: E402  the stroke chart drawn back


def faces(path, width, levels, modes):
    raw = Path(path).read_bytes()
    carried = 2 * levels * modes
    size = 4 + 4 * width + 8 * carried
    if len(raw) % size:
        raise ValueError(f"{path}: {len(raw)} bytes is not a whole number of {size}-byte cells")
    top, state, energy = [], [], []
    for i in range(0, len(raw), size):
        c = struct.unpack_from("<I", raw, i)[0]
        t = list(struct.unpack_from(f"<{width}i", raw, i + 4))
        m = list(struct.unpack_from(f"<{carried}q", raw, i + 4 + 4 * width))
        top.append((c, t))
        state.append((c, m))
        energy.append((c, [m[2 * k] ** 2 + m[2 * k + 1] ** 2 for k in range(levels * modes)]))
    return top, state, energy


def chart(prefix, side):
    raw = Path(f"{prefix}.{side}.classes").read_bytes()
    classes = struct.unpack(f">{len(raw) // 2}H", raw)
    marks = Path(f"{prefix}.{side}.marks").read_bytes()
    if len(marks) != len(classes):
        raise ValueError(f"{prefix}.{side}: classes and marks differ in length")
    cells, i = [], 0
    while i < len(classes):
        if marks[i] != 5:
            i += 1
            continue
        j = i
        while j < len(classes) and marks[j] == 5:
            j += 1
        if j + 1 < len(classes) and marks[j] == 7 and marks[j + 1] == 1:
            image, slips = render.strokes(bytes(classes[i:j]))
            if slips:
                raise ValueError(f"{prefix}.{side}: a stroke at {i} does not draw back ({slips} slips)")
            pooled = [sum(image[(4 * r + y) * 28 + 4 * c + x] for y in range(4) for x in range(4)) for r in range(7) for c in range(7)]
            cells.append((classes[j + 1], pooled))
        i = j
    return cells


def fit(train, width):
    labels = sorted({c for c, _ in train})
    n = {c: 0 for c in labels}
    sums = {c: [0] * width for c in labels}
    for c, x in train:
        n[c] += 1
        for k in range(width):
            sums[c][k] += x[k]
    return labels, n, sums


def nearest_mean(model, x):
    labels, n, sums = model
    return min(labels, key=lambda c: (Fraction(sum((n[c] * xk - s) ** 2 for xk, s in zip(x, sums[c])), n[c] * n[c]), c))


def scatter(train, model, width):
    labels, n, sums = model
    w = [sum(x[k] * x[k] for _, x in train) - sum(Fraction(sums[c][k] ** 2, n[c]) for c in labels) for k in range(width)]
    return [k for k in range(width) if w[k] != 0], w


def nearest_scaled(model, kept, w, x):
    labels, n, sums = model
    return min(labels, key=lambda c: (sum(Fraction((n[c] * x[k] - sums[c][k]) ** 2, n[c] * n[c]) / w[k] for k in kept), c))


def solve(a, b):
    """Exact Gauss-Jordan for A X = B; None when A is singular."""
    m, r = len(a), len(b[0])
    rows = [a[i][:] + b[i][:] for i in range(m)]
    for col in range(m):
        pivot = next((i for i in range(col, m) if rows[i][col] != 0), None)
        if pivot is None:
            return None
        rows[col], rows[pivot] = rows[pivot], rows[col]
        rows[col] = [v / rows[col][col] for v in rows[col]]
        for i in range(m):
            if i != col and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [u - f * v for u, v in zip(rows[i], rows[col])]
    return [row[m:] for row in rows]


def pooled(train, model, width):
    labels, n, sums = model
    xx = [[0] * width for _ in range(width)]
    for _, x in train:
        for p in range(width):
            if x[p]:
                for q in range(width):
                    xx[p][q] += x[p] * x[q]
    w = [[Fraction(xx[p][q]) - sum(Fraction(sums[c][p] * sums[c][q], n[c]) for c in labels) for q in range(width)] for p in range(width)]
    mu = {c: [Fraction(s, n[c]) for s in sums[c]] for c in labels}
    solved = solve(w, [[mu[c][k] for c in labels] for k in range(width)])
    if solved is None:
        return None
    a = {c: [solved[k][j] for k in range(width)] for j, c in enumerate(labels)}
    return labels, a, {c: sum(u * v for u, v in zip(a[c], mu[c])) / 2 for c in labels}


def discriminant(model, x):
    labels, a, b = model
    return max(labels, key=lambda c: (sum(u * v for u, v in zip(a[c], x)) - b[c], -c))


def report(train, held, width):
    model = fit(train, width)
    labels = model[0]
    counts = {c: sum(1 for d, _ in held if d == c) for c in labels}
    print(f"cells train={len(train)} held_out={len(held)} labels={''.join(chr(c) for c in labels)} held_out_by_label={[counts[c] for c in labels]} chance={len(held) // len(labels)} majority={max(counts.values())}")
    for name, rows in (("train", train), ("held_out", held)):
        print(f"nearest_mean {name} {sum(nearest_mean(model, x) == c for c, x in rows)} of {len(rows)}")
    kept, w = scatter(train, model, width)
    for name, rows in (("train", train), ("held_out", held)):
        print(f"nearest_mean_scaled {name} {sum(nearest_scaled(model, kept, w, x) == c for c, x in rows)} of {len(rows)} (coordinates {len(kept)} of {width})")
    if width > 64:
        return
    lda = pooled(train, model, width)
    if lda is None:
        print("pooled_covariance refused: singular")
        return
    for name, rows in (("train", train), ("held_out", held)):
        print(f"pooled_covariance {name} {sum(discriminant(lda, x) == c for c, x in rows)} of {len(rows)}")


def main(argv):
    if len(argv) == 7 and argv[1] == "faces":
        width, levels, modes = int(argv[4]), int(argv[5]), int(argv[6])
        train, held = faces(argv[2], width, levels, modes), faces(argv[3], width, levels, modes)
        for name, k, size in (("top_face", 0, width), ("carried_modes", 1, 2 * levels * modes), ("mode_energies", 2, levels * modes)):
            print(f"== {name}")
            report(train[k], held[k], size)
    elif len(argv) == 3 and argv[1] == "chart":
        report(chart(argv[2], "train"), chart(argv[2], "dev"), 49)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv)
