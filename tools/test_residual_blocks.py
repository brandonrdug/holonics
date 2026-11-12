#!/usr/bin/env -S python3 -I
"""Controls of residual_blocks.py, the residual at half rank, on drawn residuals (host arithmetic; no saved state of a line is read).

  a hand that cancels  keyed signs of one size, D a place: M_k doubles a step, so every k with at least 256 blocks reads its excess
                       inside 1 +- 4 sqrt(2 / blocks) (the spread of a mean of that many squares) and at most 2% of its blocks past
                       three roots;
  a sign that holds    +D and -D in runs of 64 places: M_k quadruples a step for k = 1 to 6 (the excess 2^k), a block of 128 holds one
                       run of each sign and sums to nothing, so M_k = 0 from k = 7; the blocks stand past three roots at k = 4, 5 and 6
                       only, where 2^k > 9;
  an offset            a constant added to every code leaves every BLOCKS and HELD line as it stands and moves the mean alone;
  the quarters         q1 to q4 partition `all`, each in the passage's order, a place in the quarter floor(4 t / n) + 1;
  a planted run        256 places of +D among the keyed signs: at the region's largest excess the first block named is the run's;
  the tail             blocks and tail are the places' quotient and remainder by 2^k, and the table stops at the last k with 16 blocks;
  the edges            a region under 16 places prints under_16; equal charges print no excess and name no block;
  refusals             another header, rows out of the passage's order, a place at or past its answer's length, a negative code and a
                       word that is not an integer.
"""
import io
import math
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import residual_blocks  # noqa: E402

D = 1 << 20  # one bit a place on the codes' 2^-20 bits
N = 1 << 14  # places of the drawn passages


def signs(n, seed):
    """Keyed signs, +1 or -1: the top bit of test_part_rates.py's draws."""
    x, out = seed, []
    for _ in range(n):
        x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        out.append(1 if x >> 63 else -1)
    return out


def passage(charges, lengths, base=2 * D):
    """Rows for the charges in the passage's order, answers of the given lengths in turn: code = base + v over entropy base."""
    rows, k, t, j = [], 0, 0, 0
    for v in charges:
        n = lengths[j % len(lengths)]
        rows.append((k, t, n, base + v, base))
        t += 1
        if t == n:
            k, t, j = k + 1, 0, j + 1
    return rows


def write(path, rows, head=None):
    with open(path, "w") as f:
        f.write("\t".join(head or residual_blocks.HEAD) + "\n")
        for row in rows:
            f.write("\t".join(str(x) for x in row) + "\n")


def run(path):
    out = io.StringIO()
    old = sys.argv
    sys.argv = ["residual_blocks.py", path]
    try:
        with redirect_stdout(out):
            residual_blocks.main()
    finally:
        sys.argv = old
    return out.getvalue().split("\n")[:-1]


def fields(lines, head, region=None):
    """The key=value words of the printed lines that begin with head, a dict a line, of one region when it is named."""
    got = [dict(w.split("=", 1) for w in l.split(" ")[1:]) for l in lines if l.startswith(head + " ")]
    return [f for f in got if region is None or f["region"] == region]


def main():
    with tempfile.TemporaryDirectory() as tmp:
        def p(name):
            return os.path.join(tmp, name)

        # A hand that cancels.
        noise = [(i // 64, i % 64, D * s) for i, s in enumerate(signs(N, 1))]
        table, root = residual_blocks.moments(noise)
        assert [r[0] for r in table] == list(range(11)), "2^14 places hold 16 blocks of 2^10 and no more"
        m0 = table[0][3]
        checked = 0
        for k, blocks, tail, m, past in table:
            if blocks >= 256:
                excess = m / ((1 << k) * m0)
                assert abs(excess - 1) <= 4 * math.sqrt(2 / blocks), (k, excess)
                assert past <= blocks // 50, (k, past, blocks)
                checked += 1
        assert checked == 7 and root > 0
        print("residual_blocks: keyed signs, a hand that cancels, double a step: the excess near 1 and few blocks past three roots")

        # A sign that holds.
        wave = [(i // 64, i % 64, D if (i // 64) % 2 == 0 else -D) for i in range(N)]
        table, root = residual_blocks.moments(wave)
        assert root == N * (N * D) ** 2
        assert [r[3] for r in table] == [D * D * 4 ** k if k <= 6 else 0 for k in range(11)]
        assert [r[4] for r in table] == [N >> k if 4 <= k <= 6 else 0 for k in range(11)]
        write(p("wave"), passage([v for _, _, v in wave], [N]))
        lines = fields(run(p("wave")), "RESIDUAL_BLOCKS", "all")
        assert [f["ratio"] for f in lines] == ["-"] + ["4.0000"] * 6 + ["0.0000"] + ["-"] * 3
        assert [f["excess"] for f in lines] == [f"{2 ** k:.4f}" if k <= 6 else "0.0000" for k in range(11)]
        assert lines[0]["m2_nats2"] == f"{math.log(2.0) ** 2:.6g}", "one bit a place squared, in nats"
        assert [f["share"] for f in lines] == ["1.0000" if 4 <= k <= 6 else "0.0000" for k in range(11)]
        print("residual_blocks: runs of 64 of one sign quadruple a step to k = 6, cancel from k = 7, and stand past three roots at k = 4 to 6")

        # An offset, on answers of four lengths.
        lengths = [37, 64, 100, 129]
        rows = passage([D * s for s in signs(N, 2)], lengths)
        write(p("a"), rows)
        write(p("b"), [(k, t, n, c + D, h) for k, t, n, c, h in rows])
        a, b = run(p("a")), run(p("b"))
        assert [l for l in a if not l.startswith("RESIDUAL_REGION ")] == [l for l in b if not l.startswith("RESIDUAL_REGION ")]
        assert fields(a, "RESIDUAL_HELD") == fields(b, "RESIDUAL_HELD")
        for x, y in zip(fields(a, "RESIDUAL_REGION"), fields(b, "RESIDUAL_REGION")):
            assert (x["places"], x["problems"]) == (y["places"], y["problems"])
            moved = float(y["mean_charge_nats_a_place"]) - float(x["mean_charge_nats_a_place"])
            assert abs(moved - math.log(2.0)) < 2e-6, moved
        print("residual_blocks: a bit added to every code moves the mean a place by ln 2 nats and leaves every block as it stands")

        # The quarters.
        read = residual_blocks.read_rows(p("a"))
        by = residual_blocks.regions(read)
        letters = {(k, t): n for k, t, n, _ in read}
        assert sorted(by["q1"] + by["q2"] + by["q3"] + by["q4"]) == by["all"] and by["all"] == sorted(by["all"])
        for q in range(1, 5):
            series = by[f"q{q}"]
            assert series == sorted(series) and all(4 * t // letters[(k, t)] + 1 == q for k, t, _ in series)
        places = {f["region"]: int(f["places"]) for f in fields(a, "RESIDUAL_REGION")}
        assert places["all"] == N == sum(places[f"q{q}"] for q in range(1, 5))
        print("residual_blocks: q1 to q4 partition the passage, each in its order, a place in the quarter floor(4 t / n) + 1")

        # A planted run: answers of 256, the run fills problem 16.
        plant = [D * s for s in signs(N, 3)]
        plant[4096:4352] = [D] * 256
        write(p("plant"), passage(plant, [256]))
        held = fields(run(p("plant")), "RESIDUAL_HELD", "all")
        assert held and int(held[0]["k"]) >= 8 and held[0]["first"] == "16:0", held[:1]
        last = tuple(int(x) for x in held[0]["last"].split(":"))
        assert last >= (16, 255) and float(held[0]["sum_nats"]) > 0
        print(f"residual_blocks: a planted run of 256 is the first block named at the largest excess (k = {held[0]['k']})")

        # The tail, on 5,000 places in answers of 50.
        write(p("tail"), passage([D * s for s in signs(5000, 4)], [50]))
        out = run(p("tail"))
        for region, count in {f["region"]: int(f["places"]) for f in fields(out, "RESIDUAL_REGION")}.items():
            lines = fields(out, "RESIDUAL_BLOCKS", region)
            assert [int(f["k"]) for f in lines] == list(range(len(lines))) and count >> len(lines) < 16 <= count >> (len(lines) - 1)
            for f in lines:
                size = 1 << int(f["k"])
                assert (int(f["block"]), int(f["blocks"]), int(f["tail"])) == (size, count // size, count % size), f
        print("residual_blocks: blocks and tail are the places' quotient and remainder by 2^k, to the last k with 16 blocks")

        # The edges.
        write(p("short"), passage([D, -D, D] * 4, [4]))
        out = run(p("short"))
        assert len(out) == 5 and all(l.startswith("RESIDUAL_REGION ") and l.endswith(" blocks=under_16") for l in out), out
        write(p("equal"), passage([5] * 64, [64]))
        out = run(p("equal"))
        blocks = fields(out, "RESIDUAL_BLOCKS", "all")
        assert blocks and all(f["excess"] == "-" and f["ratio"] == "-" and f["past_three_roots"] == "0" for f in blocks)
        assert not fields(out, "RESIDUAL_HELD")
        print("residual_blocks: a region under 16 places prints under_16; equal charges read no excess and name no block")

        # Refusals.
        good = passage([D, -D] * 8, [16])
        cases = {
            "another header": (good, ["problem", "place", "letters", "code", "entropy"]),
            "rows out of order": (good[:3] + [good[4], good[3]] + good[5:], None),
            "a row twice": (good[:4] + [good[3]] + good[4:], None),
            "a place at its answer's length": (good + [(1, 16, 16, 2 * D, 2 * D)], None),
            "a negative code": (good[:-1] + [(0, 15, 16, -1, 0)], None),
        }
        for name, (case, head) in cases.items():
            write(p("refused"), case, head)
            try:
                run(p("refused"))
            except AssertionError:
                pass
            else:
                raise AssertionError(f"not refused: {name}")
        with open(p("word"), "w") as f:
            f.write("\t".join(residual_blocks.HEAD) + "\n0\t0\t16\t1.5\t0\n")
        try:
            run(p("word"))
        except ValueError:
            pass
        else:
            raise AssertionError("not refused: a word that is not an integer")
        print("residual_blocks: another header, rows out of order or twice, a place past its answer, a negative code and a float are refused")
    print("residual_blocks: 8 lines, the controls hold")


if __name__ == "__main__":
    main()
