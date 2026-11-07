#!/usr/bin/env python3
"""Each family's step length rho (2^-rho, rho on 2^-24 bits) carried in learner states' `family-lengths` lines, side by side
(theory, November 7 19:51, read (c)). A reading only."""
import sys
names = "enc before after q q_bias v v_bias out out_bias a a_bias b b_bias w w_bias read read_bias moment_before moment_after temper probe probe_bias pace moment_face moment_face_bias lift_bias pair_c face_temper".split()
rows = []
for p in sys.argv[1:]:
    line = [l for l in open(p).read().split("\n") if l.startswith("family-lengths")][0].split()[1:]
    rows.append([int(line[3 * i]) for i in range(len(line) // 3)])
print("family\t" + "\t".join(p.split("/")[-1] for p in sys.argv[1:]) + "\t(rho in bits; the step is 2^-rho)")
for i, n in enumerate(names):
    if any(r[i] for r in rows):
        print(n + "\t" + "\t".join(f"{r[i] / 2 ** 24:.3f}" for r in rows))
