#!/usr/bin/env python3 -I
"""round_state.py STATE S OUT [SUBSET]: a copy of a saved learner state with its stored material numbers rounded to their leading S significant
binary digits at their own scale (theory's G21, Brandon's lens: a value is its few significant digits at the scale its region holds).

Every material entry x != 0 with more than S significant bits (bit length of |x| above S) is rounded to nearest (ties away from zero) to
S bits: |x| = q 2^k with q of S bits, sign kept; zero stays zero; an entry of S bits or fewer is untouched. The moments, the carried
remainders and the head are copied unchanged, so the copy reads as the same learner with a coarser material; S >= 33 (or 0 as `none`) is the
unrounded copy, the parity check. The state read stays untouched (OUT is created new).

SUBSET (default all): `faces` (the encodings, the readout's lift and its biases, the moment's chart: enc before after read read_bias lift_bias
moment_face moment_face_bias), `contacts` (a a_bias b b_bias w w_bias), `heads` (q q_bias v v_bias probe probe_bias out out_bias pace temper
moment_before moment_after), `lane` (the second lane's entries of every family, as state_travel.py's lane subset: the face coordinates
past the first lane). Prints, per part, the entries and the mean significant bits a number carries before the rounding and how many the
rounding moved. Numbers only.
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from state_travel import layout, masks, state  # noqa: E402

FACES = ("enc", "before", "after", "read", "read_bias", "lift_bias", "moment_face", "moment_face_bias")
CONTACTS = ("a", "a_bias", "b", "b_bias", "w", "w_bias")
HEADS = ("q", "q_bias", "v", "v_bias", "probe", "probe_bias", "out", "out_bias", "pace", "temper", "moment_before", "moment_after")


def round_bits(theta, s):
    """The entries rounded to nearest to their leading s significant bits (zero and sign kept; ties away from zero)."""
    x = theta.astype(np.int64)
    mag = np.abs(x)
    bits = np.zeros(mag.shape, dtype=np.int64)
    nz = mag > 0
    bits[nz] = np.floor(np.log2(mag[nz])).astype(np.int64) + 1
    # exact bit length (log2 of an int64 below 2^53 is exact enough; fix the boundary by comparison)
    over = nz & (mag >= (1 << np.minimum(bits, 62)))
    bits[over] += 1
    under = nz & (bits > 0) & (mag < (1 << np.maximum(bits - 1, 0)))
    bits[under] -= 1
    shift = np.maximum(bits - s, 0)
    half = np.where(shift > 0, 1 << np.maximum(shift - 1, 0), 0)
    q = np.where(shift > 0, (mag + half) >> shift, mag)
    out = np.where(shift > 0, q << shift, mag)
    return (np.sign(x) * out).astype(np.int64), bits


def main():
    if len(sys.argv) not in (4, 5):
        sys.exit(__doc__)
    path, s_arg, out_path = sys.argv[1:4]
    subset = sys.argv[4] if len(sys.argv) == 5 else "all"
    s = int(s_arg)
    d, theta = state(path)
    fam, total = layout(d)
    chosen = np.zeros(total, dtype=bool)
    groups = {"faces": FACES, "contacts": CONTACTS, "heads": HEADS}
    if subset not in ("all", "lane", *groups):
        sys.exit("SUBSET: all, faces, contacts, heads or lane")
    for name, at, shape, grain in fam:
        n = int(np.prod(shape))
        if subset == "all" or (subset in groups and name in groups[subset]):
            chosen[at:at + n] = True
        elif subset == "lane":
            # The second lane's entries (state_travel's lane subset; the new contacts are no lane entry).
            new, lane = masks(name, shape, d, d["contacts"] // 2, d["contacts"])
            chosen[at:at + n] = lane.reshape(-1)
    rounded, bits = round_bits(theta, s if s < 33 else 62)
    out = np.where(chosen, rounded, theta.astype(np.int64))
    moved = int((out != theta).sum())
    nz = chosen & (theta != 0)
    print(f"ROUND s={s} subset={subset} entries={int(chosen.sum())} nonzero={int(nz.sum())} mean_bits_before={bits[nz].mean():.2f} moved={moved}")
    lines = open(path).read().split("\n")
    lines[2] = " ".join(str(int(v)) for v in out)
    with open(out_path, "x") as f:
        f.write("\n".join(lines))


if __name__ == "__main__":
    main()
