#!/usr/bin/env -S python3 -I
"""A ruler: the geometry the engine's free rows hold for its symbols (the lead, November 17; Brandon's question of 00:18Z on symbols as
geometry; atlas `radix.digit-shift-spectrum`).

Usage: symbol_geometry_ruler.py STATE CODEC

The engine that trains takes a byte as a class, and a class indexes a row of its own in three tables (`enc`, `before`, `after`, each
`(A + 1) × D`; THE_MACHINE's guard 9 names the repair as owed). Nothing in that form places one symbol beside another, so whatever
geometry the symbols have is what deposition has written into separate rows. This reads it from a state's text:

- `SYMBOL_RING`: the ten digits' rows, centred, expanded over the characters of ℤ/10 in the digits' own order: the share of their power
  at each frequency k (k and 10 − k together), beside the mean and the largest share k = 1 takes over orders drawn at random, and the
  count of random orders that reach the true order's share. Rows that know nothing of the digits' order give every k the share of its
  count of characters (2/9, and 1/9 at k = 5).
- `SYMBOL_NEXT`: the mean cosine between the rows of digits d and d + 1 (mod 10) beside the mean over all other pairs.
- `SYMBOL_CASE`: the mean cosine between a letter's lower- and upper-case rows beside the mean over pairs of unlike letters.

A ruler: it names digits and letters by their bytes, outside the machine, and reads the state; it writes nothing.
"""
import random
import sys

import numpy as np


def main():
    state, codec = sys.argv[1], sys.argv[2]
    with open(state) as f:
        f.readline()
        head = f.readline().split()
        theta = np.array(f.readline().split(), dtype=np.int64)
    a, d = int(head[1]), int(head[2])
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(x) for x in f.readline().split()]
    cls = {b: (k if k < void else k + 1) for k, b in enumerate(units)}
    n = (a + 1) * d
    tables = {name: theta[i * n:(i + 1) * n].reshape(a + 1, d).astype(np.float64) for i, name in enumerate(("enc", "before", "after"))}
    rng = random.Random(0)
    print(f"SYMBOL_READ alphabet={a} width={d} void={void} digit_classes={[cls[48 + k] for k in range(10)]}")
    for name, t in tables.items():
        rows = t[[cls[48 + k] for k in range(10)]]
        rows = rows - rows.mean(axis=0)

        def shares(order):
            f = np.fft.fft(rows[order], axis=0)
            p = (np.abs(f) ** 2).sum(axis=1)
            p = p / p[1:].sum()
            return [p[k] + p[10 - k] for k in range(1, 5)] + [p[5]]

        true = shares(list(range(10)))
        draws = []
        for _ in range(20000):
            o = list(range(10))
            rng.shuffle(o)
            draws.append(shares(o)[0])
        draws = np.array(draws)
        print(f"SYMBOL_RING table={name} share_k1..k5=" + " ".join(f"{x:.4f}" for x in true) + f" random_orders_k1_mean={draws.mean():.4f} max={draws.max():.4f} reaching_true={(draws >= true[0]).sum()}/20000")
        unit = rows / np.linalg.norm(rows, axis=1, keepdims=True)
        cos = unit @ unit.T
        nxt = np.mean([cos[k, (k + 1) % 10] for k in range(10)])
        rest = np.mean([cos[i, j] for i in range(10) for j in range(10) if i != j and (i - j) % 10 not in (1, 9)])
        line = np.mean([cos[k, k + 1] for k in range(9)])
        print(f"SYMBOL_NEXT table={name} cosine_d_d+1_ring={nxt:.4f} cosine_d_d+1_line={line:.4f} other_pairs={rest:.4f}")
        low = [cls[97 + k] for k in range(26) if 97 + k in cls and 65 + k in cls]
        up = [cls[65 + k] for k in range(26) if 97 + k in cls and 65 + k in cls]
        both = t[low + up]
        both = both - both.mean(axis=0)
        u = both / np.linalg.norm(both, axis=1, keepdims=True)
        m = len(low)
        same = np.mean([u[k] @ u[m + k] for k in range(m)])
        unlike = np.mean([u[i] @ u[m + j] for i in range(m) for j in range(m) if i != j])
        print(f"SYMBOL_CASE table={name} letters={m} cosine_same_letter={same:.4f} cosine_unlike_letters={unlike:.4f}")


if __name__ == "__main__":
    main()
