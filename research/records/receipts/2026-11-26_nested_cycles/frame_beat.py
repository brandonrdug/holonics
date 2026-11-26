#!/usr/bin/env -S python3 -I
"""What a frame's clock does to a steady act of the tube limb: a host ruler.

The body (`tools/tube_limb.py`) is driven by one act held still: a pitch level, a loudness level and four areas. Its sound is then
read two ways, each as the limb's own return value `v = 16 b + m` (a sixteenth of an octave of power a step):

  frame   the limb's frames of 160 samples (10 ms at 16 kHz), by the limb's own functions (`loudness`, `bands`): what the babble
          slice returns to her before its chart
  cycle   cells cut at the source's own pulses: a cell holds K whole periods of the folds, K the count nearest one frame's
          length, so a cell's length is itself a count of samples against periods

A steady act is no news. What `v` still does from cell to cell is the reading clock's own beat against the source's, and it is
reported by pitch level: the range of `v`, the spread between its tenth and ninetieth hundredths (so one empty frame does not set
the figure), its count of distinct values, and the empirical entropy of the cell's value (nats a cell, the order-zero count over
the run), for the loudness and for each of the three bands. The run is 3 s; its first half second
(the body's glide to the act) is left out. The planted control is the same reading of a tone whose period divides the frame, which
must read a range of zero on both clocks.

Usage:  frame_beat.py PATH_TO_tube_limb.py
"""
import importlib.util
import math
import sys
from collections import Counter

import numpy as np


def load(path):
    spec = importlib.util.spec_from_file_location("tube_limb", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def entropy(values):
    counts = Counter(values)
    n = sum(counts.values())
    return -sum(c / n * math.log(c / n) for c in counts.values())


def cells_v(tl, x, edges):
    """v of each cell's summed squares, the cells cut at `edges`."""
    return [tl.v_of(1 + int(np.sum(x[a:b].astype(np.int64) ** 2))) for a, b in zip(edges[:-1], edges[1:])]


def band_cells(tl, x, edges):
    """Each cell's three bands' power as v, as the limb's `bands` reads a frame: the cell's spectrum over its own length (a Hann
    window over the cell), the bands' edges at 500 and 2,000 Hz. Under a held act every cell of a run has one length."""
    out = [[], [], []]
    for a, b in zip(edges[:-1], edges[1:]):
        seg = x[a:b].astype(float)
        spec = np.abs(np.fft.rfft(seg * np.hanning(len(seg)))) ** 2
        hz = np.fft.rfftfreq(len(seg), 1 / tl.CLOCK)
        for k, (lo, hi) in enumerate(((0, 500), (500, 2000), (2000, 8001))):
            out[k].append(tl.v_of(1 + int(spec[(hz >= lo) & (hz < hi)].sum())))
    return out


def line(tag, vs):
    vs = [int(v) for v in vs]
    s = sorted(vs)
    mid = s[(9 * len(s)) // 10] - s[len(s) // 10]
    return f"{tag} range={max(vs) - min(vs):3d} tenth_to_ninetieth={mid:3d} distinct={len(set(vs)):3d} entropy={entropy(vs) + 0.0:.3f}"


def main():
    tl = load(sys.argv[1])
    frames, skip = 300, 50
    areas = (9, 4, 7, 10)  # one open shape, held
    print(f"FRAME_BEAT clock_hz={tl.CLOCK} frame_samples={tl.FRAME} run_frames={frames} skipped={skip} areas={areas} loud=8")
    # The planted control: a tone of period 40 samples (a frame holds four periods), read by both clocks.
    t = np.arange(frames * tl.FRAME)
    tone = np.round(8000 * np.sin(2 * np.pi * t / 40)).astype(np.int64)
    fe = list(range(skip * tl.FRAME, frames * tl.FRAME + 1, tl.FRAME))
    print("PLANTED tone period=40 " + line("frame", cells_v(tl, tone, fe)) + " | " + line("cycle", cells_v(tl, tone, fe)))
    for level in range(1, tl.LEVELS):
        period = tl.period_of(level)
        acts = [(level, 8) + areas] * frames
        x = tl.render(acts)
        start = skip * tl.FRAME
        fe = list(range(start, len(x) + 1, tl.FRAME))
        k = max(1, round(tl.FRAME / period))
        ce = list(range(start, len(x) + 1, k * period))
        fv, cv = tl.loudness(x)[skip:frames].tolist(), cells_v(tl, x, ce)
        fb, cb = tl.bands(x)[skip:frames].T.tolist(), band_cells(tl, x, ce)
        print(f"PITCH level={level:2d} period={period:3d} hz={tl.CLOCK / period:6.1f} radians_a_frame={2 * math.pi * tl.FRAME / period:5.2f} "
              f"periods_a_cell={k}")
        print("  loudness  " + line("frame", fv) + " | " + line("cycle", cv))
        for b, name in enumerate(("under 500 ", "500-2000  ", "over 2000 ")):
            print(f"  {name}" + line("frame", fb[b]) + " | " + line("cycle", cb[b]))


if __name__ == "__main__":
    main()
