"""How long each mode keeps a value and how fast it turns: the readers at U against the carriers.

CROSSING_DEMAND.py: U's readers read the units through modes 4, 15, 2, 6 and 14; the modes that
carry a value from B to U alike for both result lengths are 41, 56 and 48 (CARRY_B_TO_U.py), and 16
is where the founding against U's demand placed the crossing (FOUND_PLACE_AT_B.py). Here every
mode's move h -> lambda h + beta conj(h) at every cell of the eight training parts
(char/block{c}_allmoves.i32, /2^30): the median of |lambda| (what the mode keeps of its value per
cell), of |arg lambda| (how far it turns it), and of |beta| (the pump), and each mode's rank among
the 64 by its median turn (0 turns least)."""
import numpy as np
lam, bet = [], []
for c in range(8):
    mv = np.fromfile(f"char/block{c}_allmoves.i32", dtype=np.int32).reshape(-1, 258)
    lam.append((mv[:, 2::4] + 1j * mv[:, 3::4]) / 2**30); bet.append((mv[:, 4::4] + 1j * mv[:, 5::4]) / 2**30)
lam, bet = np.concatenate(lam), np.concatenate(bet)
keep, turn, pump = np.median(np.abs(lam), 0), np.median(np.abs(np.angle(lam)), 0), np.median(np.abs(bet), 0)
rank = np.empty(64, dtype=int); rank[np.argsort(turn)] = np.arange(64)
print(f"cells {len(lam)}; every mode: keeps {np.median(keep):.3f} (median), turns {np.median(turn):.3f} rad")
for name, ms in [("U's readers", [4, 15, 2, 6, 14]), ("the carriers B to U", [41, 56, 48]), ("the placement found by U's demand", [16]), ("the antinodes B to U", [47, 38, 55, 7])]:
    print(name)
    for m in ms:
        print(f"   mode {m}: keeps {keep[m]:.3f}, turns {turn[m]:.3f} rad (rank {rank[m]} of 64), pump {pump[m]:.3f}")
