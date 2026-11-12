#!/usr/bin/env python3
"""The residual at half rank (theory, November 12; the Einstein record §14.11, U6): a host ruler on the private
RESIDUAL.tsv that `residual-field` writes, a saved state's held references read with every place locked.

    python3 -I tools/residual_blocks.py RESIDUAL.tsv

At each place the charge v = c - H on the codes' 2^-20 bits: the letter's surprise less its face's entropy, the face's
temperature covector, whose mean is zero under the true conditional (atlas `ratio.face-temperature-covector`). A region is
the whole passage or one quarter of every answer, by the place's share of its answer (floor(4 t / n)), the quarters the
held joint's series is read by. For each region the charges less the region's mean are summed over consecutive blocks of
2^k of the region's places in the passage's order (problem, then place; whole blocks only, the places past the last whole
block left out and counted as `tail`), and the blocks' second moment M_k is read against k.

- Where the field holds the region's law, what is left of the charge is a hand that cancels: M_k doubles a step
  (M_k / M_(k-1) = 2) and the excess M_k / (2^k M_0) stays 1.
- Where it lacks a law the charge keeps a sign over a block: M_k quadruples a step, so the excess doubles.
- A block whose sum stands past three roots of the root law's 2^k M_0 is past three standard deviations of a hand that
  cancels (under a normal root law 0.0027 of the blocks). At the region's largest excess its blocks past three roots are
  named, at most eight, by their first and last problem and place: there the sign holds.

Printed in nats (ln 2 a ruler's float on the host): RESIDUAL_REGION (places, the mean charge a place), RESIDUAL_BLOCKS
(k, the block's length, the blocks, the tail, M_k, the ratio to M_(k-1), the excess, the blocks past three roots and their
share) for every k with at least 16 blocks, and RESIDUAL_HELD. Numbers only: the passage's letters never enter.

The sums are integers: with N places and S their summed charge, each place enters as N v - S, so a block's sum is N times
its centred sum, and M_k is formed from those integers before one division.
"""
import math
import sys

HEAD = ["problem", "place", "letters", "code_bits_q20", "entropy_bits_q20"]
NATS2 = (math.log(2.0) / (1 << 20)) ** 2  # (nats a 2^-20 bit)^2
LEAST_BLOCKS = 16
NAMED = 8


def read_rows(path):
    """The rows of RESIDUAL.tsv as (problem, place, letters, v), v = code - entropy on 2^-20 bits, in the passage's order."""
    out = []
    with open(path) as f:
        head = f.readline().rstrip("\n").split("\t")
        assert head == HEAD, "residual-field's RESIDUAL.tsv"
        last = (-1, -1)
        for line in f:
            k, t, n, c, h = (int(x) for x in line.rstrip("\n").split("\t"))
            assert (k, t) > last, "the passage's order: problem, then place"
            assert 0 <= t < n and c >= 0 and h >= 0, "a place inside its answer, a code and an entropy"
            last = (k, t)
            out.append((k, t, n, c - h))
    return out


def regions(rows):
    """The region's places in the passage's order: `all`, and `q1` to `q4` by the place's quarter of its answer."""
    by = {"all": [], "q1": [], "q2": [], "q3": [], "q4": []}
    for k, t, n, v in rows:
        by["all"].append((k, t, v))
        by[f"q{4 * t // n + 1}"].append((k, t, v))
    return by


def block_sums(series, k):
    """Each whole block of 2^k places' sum of N v - S (an integer: N times the block's centred sum), and the tail."""
    n, s = len(series), sum(v for _, _, v in series)
    size = 1 << k
    count = n // size
    sums = [sum(n * v - s for _, _, v in series[b * size:(b + 1) * size]) for b in range(count)]
    return sums, n - count * size


def moments(series):
    """For every k with at least LEAST_BLOCKS whole blocks: (k, blocks, tail, M_k on (2^-20 bits)^2, past three roots), with the
    root law's sums (the blocks of one place: their count and summed square). M_k is formed from the integers over one division by
    blocks N^2, and a block stands past three roots where its sum's square times the places exceeds nine times 2^k times the root
    law's summed square: the N^2 of both sides cancels, so the comparison is between integers."""
    n = len(series)
    out = []
    root = None
    k = 0
    while n >> k >= LEAST_BLOCKS:
        sums, tail = block_sums(series, k)
        square = sum(b * b for b in sums)
        if root is None:
            root = square
        past = sum(1 for b in sums if b * b * n > 9 * (1 << k) * root)
        out.append((k, len(sums), tail, square / (len(sums) * n * n), past))
        k += 1
    return out, root


def held_blocks(series, k, root):
    """The blocks of 2^k past three roots of the root law, largest first, at most NAMED: (first, last, centred sum)."""
    n = len(series)
    sums, _ = block_sums(series, k)
    size = 1 << k
    past = [(b, s) for b, s in enumerate(sums) if s * s * n > 9 * (1 << k) * root]
    past.sort(key=lambda x: (-abs(x[1]), x[0]))
    return [(series[b * size][:2], series[(b + 1) * size - 1][:2], s / n) for b, s in past[:NAMED]]


def main():
    assert len(sys.argv) == 2, "residual_blocks.py RESIDUAL.tsv"
    rows = read_rows(sys.argv[1])
    for name, series in regions(rows).items():
        n = len(series)
        if n < LEAST_BLOCKS:
            print(f"RESIDUAL_REGION region={name} places={n} blocks=under_{LEAST_BLOCKS}")
            continue
        mean = sum(v for _, _, v in series) / n * math.log(2.0) / (1 << 20)
        print(f"RESIDUAL_REGION region={name} places={n} problems={len({k for k, _, _ in series})} mean_charge_nats_a_place={mean:.6f}")
        table, root = moments(series)
        m0 = table[0][3]
        last = None
        for k, blocks, tail, m, past in table:
            ratio = "-" if last is None or last == 0 else f"{m / last:.4f}"
            excess = "-" if m0 == 0 else f"{m / ((1 << k) * m0):.4f}"
            print(
                f"RESIDUAL_BLOCKS region={name} k={k} block={1 << k} blocks={blocks} tail={tail} m2_nats2={m * NATS2:.6g} "
                f"ratio={ratio} excess={excess} past_three_roots={past} share={past / blocks:.4f}"
            )
            last = m
        top = max(table[1:], key=lambda r: (r[3] / (1 << r[0]), -r[0]), default=None)
        if top is not None and root > 0:
            for (k0, t0), (k1, t1), s in held_blocks(series, top[0], root):
                print(f"RESIDUAL_HELD region={name} k={top[0]} first={k0}:{t0} last={k1}:{t1} sum_nats={s * math.log(2.0) / (1 << 20):+.4f}")


if __name__ == "__main__":
    main()
