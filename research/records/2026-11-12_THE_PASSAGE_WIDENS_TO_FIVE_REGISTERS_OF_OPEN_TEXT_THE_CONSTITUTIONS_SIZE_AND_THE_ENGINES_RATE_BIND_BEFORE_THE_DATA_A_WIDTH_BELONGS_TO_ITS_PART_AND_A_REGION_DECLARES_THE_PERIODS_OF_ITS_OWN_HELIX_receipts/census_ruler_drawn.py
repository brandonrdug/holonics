#!/usr/bin/env -S python3 -I
"""The census ruler drawn on spans of known kind (a ruler's floats on a host; numpy; nothing of the machine is read).

tools/block_directions.py reads k, the least count of directions holding 15/16 of the singular values' sum of D1^T D2, for two
spans of a block's travel. This draws D1 and D2 with standard normal entries and prints the mean k over 40 draws a case:

  apart    two independent spans of full rank (they share no direction beyond chance);
  shared   the second span is s times the first plus (1 - s) times an independent one;
  confined both spans lie in one column space of r directions (each a product of an independent rows-by-r draw and one r-by-columns draw).

Usage: census_ruler_drawn.py
"""
import numpy as np

KEEP, OF, DRAWS = 15, 16, 40


def k_of(values):
    values = np.sort(values)[::-1]
    total = np.cumsum(values)
    return int(np.searchsorted(total, total[-1] * KEEP / OF) + 1)


def mean_k(rng, rows, columns, shared=0.0, confined=None):
    cross, alone = [], []
    for _ in range(DRAWS):
        if confined is None:
            d1, d2 = rng.standard_normal((rows, columns)), rng.standard_normal((rows, columns))
        else:
            basis = rng.standard_normal((confined, columns))
            d1, d2 = rng.standard_normal((rows, confined)) @ basis, rng.standard_normal((rows, confined)) @ basis
        d2 = shared * d1 + (1 - shared) * d2
        cross.append(k_of(np.linalg.svd(d1.T @ d2, compute_uv=False)))
        alone.append(k_of(np.linalg.svd(d1, compute_uv=False)))
    return sum(cross) / DRAWS, sum(alone) / DRAWS


def main():
    rng = np.random.default_rng(20261112)
    for columns in (64, 32):
        for rows in (101, 64, 128, 32):
            k, alone = mean_k(rng, rows, columns)
            print(f"apart rows={rows} columns={columns} k={k:.1f} k_of_one_span={alone:.1f}")
    for s in (0.25, 0.5, 0.75):
        k, _ = mean_k(rng, 101, 64, shared=s)
        print(f"shared s={s} rows=101 columns=64 k={k:.1f}")
    for r in (8, 16, 24, 32, 40, 48, 56):
        k, alone = mean_k(rng, 101, 64, confined=r)
        print(f"confined r={r} rows=101 columns=64 k={k:.1f} k_of_one_span={alone:.1f}")


if __name__ == "__main__":
    main()
