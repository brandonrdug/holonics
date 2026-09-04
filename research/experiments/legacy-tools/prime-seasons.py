#!/usr/bin/env python3
"""prime-seasons.py -- Tier 0 arithmetic side-instrument (ENGINE-FREE).

Implements verbatim: src/soma/observations/2026-07-11_tier0_prime-seasons.md

No RNG anywhere. Every step deterministic. This is external mathematics on primes
and lucky numbers -- a side instrument. Raw numbers only: no interpretation, no
grading, no peak-picking. See the declaration for the full statement of material,
windows, statistics, foils, and expectations.

Explicit readings taken where the declaration left a construction detail open
(also dumped to the head of run.log; also reported by the dispatching agent):

  R1. Window grid: non-overlapping bins of width 0.05 in u=ln(x). Window i's
      CENTER is c_i = ln(10^4) + i*0.05 for i = 0,1,2,... while c_i <= ln(N_end)
      (N_end = 2^28 for primes, 2^22 for luckies -- both grids share the same
      origin c_0 = ln(10^4)). A value u is assigned window index
      round((u - c_0) / 0.05), i.e. window i spans [c_i-0.025, c_i+0.025).
  R2. A consecutive-gap-pair triple (p,q,r) is assigned to a window by u=ln(q)
      (the middle prime/lucky of the triple). Individual primes (Chebyshev) are
      assigned windows by their own ln(p).
  R3. "Whole-range census" (used only to pick the top-10 mirror classes) is
      taken over the ENTIRE sieved sequence (2..N, unrestricted by the window
      grid -- i.e. every consecutive triple in the raw sieve, including the
      handful below ln(10^4)), separately for primes and for luckies. The
      per-window census and the spectral read are then restricted to the
      declared window grid (ln 10^4 .. ln N), with the >=1000-pair rule gating
      "usable".
  R4. F1 (order surrogate) reuses the REAL primes' top-10 mirror classes (same
      tracked classes, shuffled data) -- it is a foil on the SAME measurement,
      not a fresh classification of the shuffled data.
  R5. F2 (luckies) runs an independently fresh whole-range census on the
      luckies to find ITS OWN top-10 mirror classes ("the identical census"
      procedure, run fresh on different material, per its own foil framing).
  R6. Chebyshev per-window counts use the SAME window grid as the shape census
      (ln 10^4 .. ln 2^28), for ALL windows in that grid, not just the
      spectral-"usable" subset (usability is a gap-pair criterion, irrelevant
      to a raw residue-class prime count); the running lead and inversions are
      the cumulative sum over ALL grid windows in increasing-u order.
  R7. OTHER is carried as an 11th tracked class through the spectral read
      (section 2 lists it among "tracked classes"; the amplitude tables report
      it alongside the top 10).
  R8. Bit-reversal permutation for a window of m gaps: L = next power of two >=
      m; for i=0..L-1 in natural order compute bitrev_nbits(i); keep those
      bitrev(i) < m, in the order encountered. This yields a length-m
      permutation of the window's own gap sequence (multiset exactly
      preserved; adjacency destroyed).

No other parameter was ambiguous; N, window width, the 1000-pair gate, the
frequency lists, the zero list, and the assertion are copied verbatim from the
declaration.
"""

import csv
import math
import os
import sys
import time
import traceback

try:
    import numpy as np
except ImportError:
    sys.stderr.write(
        "ERROR: numpy is not importable by this interpreter "
        "(checked via `python3 -c \"import numpy\"`).\n"
        "Per the declaration's mechanics, `pip install --user numpy` is "
        "acceptable if needed; no system-wide install was attempted here.\n"
    )
    sys.exit(1)

# ------------------------------------------------------------------ constants

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
OUT_DIR = os.path.join(REPO_ROOT, "src", "soma", "observations",
                       "2026-07-11_prime-seasons-out")

N_PRIME = 2 ** 28
N_LUCKY = 2 ** 22

WINDOW_WIDTH = 0.05
MIN_PAIRS_USABLE = 1000
U_START = math.log(1e4)          # ln(10^4) -- shared origin for BOTH grids (R1)

ZETA_ORDINATES = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
CONTROLS = [8.0, 10.0, 12.0, 16.5, 18.0, 19.5, 23.0, 27.5, 29.0, 34.5, 36.0,
            39.0, 42.0, 45.0, 47.0, 50.5, 52.0, 55.5, 58.0, 63.0]
ZERO_LIST_BELOW_65 = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
                       37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
                       52.970321, 56.446248, 59.347044, 60.831779, 65.112544]
ALL_FREQS = ZETA_ORDINATES + CONTROLS          # 25 total; first 5 are zeta
CODE_MULT = 1_000_000                          # class-pair encoding margin

LOGF = None   # set in main()


def log(msg):
    line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"
    print(line, flush=True)
    if LOGF is not None:
        LOGF.write(line + "\n")
        LOGF.flush()


# ------------------------------------------------------------------ material

def sieve_primes(n):
    """Sieve of Eratosthenes, primes 2..n inclusive. Raw sequence, no sampling."""
    is_p = np.ones(n + 1, dtype=bool)
    is_p[0:2] = False
    limit = int(math.isqrt(n))
    for i in range(2, limit + 1):
        if is_p[i]:
            is_p[i * i:: i] = False
    return np.flatnonzero(is_p).astype(np.int64)


def lucky_sieve(n):
    """The classic lucky sieve, deterministic: start from odd numbers 1..n;
    repeatedly take the next surviving value k > previous and delete every
    k-th survivor (1-indexed positions k, 2k, 3k, ...); stop when the next
    candidate value exceeds the current survivor count."""
    arr = np.arange(1, n + 1, 2, dtype=np.int64)
    previous = 1
    while True:
        idx = int(np.searchsorted(arr, previous, side="right"))
        if idx >= len(arr):
            break
        k = int(arr[idx])
        if k > len(arr):
            break
        mask = np.ones(len(arr), dtype=bool)
        mask[k - 1:: k] = False
        arr = arr[mask]
        previous = k
    return arr


# ------------------------------------------------------------------ windows

def n_windows_for(u_end):
    return int(math.floor((u_end - U_START) / WINDOW_WIDTH)) + 1


def window_index(u):
    """u (float array) -> window index (int array); window i's center is
    U_START + i*WINDOW_WIDTH, window spans [center-W/2, center+W/2)."""
    return np.floor((u - U_START) / WINDOW_WIDTH + 0.5).astype(np.int64)


def window_centers(n_win):
    return U_START + np.arange(n_win, dtype=np.float64) * WINDOW_WIDTH


# ------------------------------------------------------------------ gap-pair census

def consecutive_gap_pairs(seq):
    """seq: sorted 1-D int64 array. Returns (gaps, gap1, gap2, mid) where
    gap1[j]=gaps[j], gap2[j]=gaps[j+1], mid[j]=seq[j+1] -- j indexes the
    (n-2) consecutive-gap-pair triples (p,q,r) = (seq[j], seq[j+1], seq[j+2])."""
    gaps = np.diff(seq)
    gap1 = gaps[:-1]
    gap2 = gaps[1:]
    mid = seq[1:-1]
    return gaps, gap1, gap2, mid


def reduced_classes(gap1, gap2):
    """Reduced ratio class (a:b), mirror-merged (a<=b), packed into one int
    code = a*CODE_MULT + b for fast tabulation."""
    g = np.gcd(gap1, gap2)
    a = gap1 // g
    b = gap2 // g
    ca = np.minimum(a, b)
    cb = np.maximum(a, b)
    return ca * CODE_MULT + cb


def decode(code):
    code = int(code)
    return code // CODE_MULT, code % CODE_MULT


def class_label(code):
    a, b = decode(code)
    return f"{a}:{b}"


def whole_range_top10(code):
    """Rank mirror classes by total count over the WHOLE (unrestricted)
    sequence (reading R3). Ties broken by ascending code for determinism."""
    vals, counts = np.unique(code, return_counts=True)
    order = np.lexsort((vals, -counts))     # primary: -counts desc; secondary: vals asc
    vals = vals[order]
    counts = counts[order]
    top_codes = vals[:10].copy()
    top_counts = counts[:10].copy()
    total = int(code.shape[0])
    return top_codes, top_counts, total


# ------------------------------------------------------------------ per-window tabulation

def per_window_class_counts(mid, code, u_end, top_codes):
    """Bin (mid,code) pairs into the declared window grid [U_START, u_end],
    tabulating total-per-window and per-class-per-window counts for the
    top_codes (OTHER = total - sum(top_codes))."""
    n_win = n_windows_for(u_end)
    u = np.log(mid.astype(np.float64))
    idx_full = window_index(u)                  # monotonic non-decreasing
    valid = (idx_full >= 0) & (idx_full < n_win)
    idx_v = idx_full[valid]
    code_v = code[valid]
    total_per_window = np.bincount(idx_v, minlength=n_win)
    class_counts = np.zeros((len(top_codes), n_win), dtype=np.int64)
    for ci, cc in enumerate(top_codes):
        m = code_v == cc
        class_counts[ci] = np.bincount(idx_v[m], minlength=n_win)
    other_counts = total_per_window - class_counts.sum(axis=0)
    return n_win, idx_full, total_per_window, class_counts, other_counts


# ------------------------------------------------------------------ spectral read

def spectral_amplitudes(u_centers_usable, fractions_by_class):
    """fractions_by_class: (C, W) array, W = usable-window count.
    Returns (C, 25) amplitude array, de-meaned per class over usable windows."""
    freqs = np.array(ALL_FREQS, dtype=np.float64)
    phase = np.exp(1j * np.outer(freqs, u_centers_usable))     # (25, W)
    demeaned = fractions_by_class - fractions_by_class.mean(axis=1, keepdims=True)
    amp = np.abs(demeaned.astype(np.complex128) @ phase.T)     # (C, 25)
    return amp


# ------------------------------------------------------------------ F1: order surrogate

def bit_reversal_permutation(m):
    """Deterministic bit-reversal permutation of {0,...,m-1} (R8): pad
    conceptually to L = next power of two >= m; for i=0..L-1 in natural order
    compute bitrev(i) over log2(L) bits; keep those bitrev(i) < m, in the
    order encountered. Length-m permutation; multiset-preserving."""
    if m <= 1:
        return np.arange(m, dtype=np.int64)
    L = 1
    nbits = 0
    while L < m:
        L <<= 1
        nbits += 1
    i = np.arange(L, dtype=np.int64)
    rev = np.zeros(L, dtype=np.int64)
    for b in range(nbits):
        rev |= ((i >> b) & 1) << (nbits - 1 - b)
    return rev[rev < m]


def surrogate_window_counts(gaps, idx_full, usable_windows, n_win, top_codes):
    """For each usable window, slice its own contiguous gap sequence,
    bit-reversal-permute it, recompute ratio classes on the NEW adjacency, and
    tabulate class counts (reusing the REAL top_codes, reading R4)."""
    class_counts = np.zeros((len(top_codes), n_win), dtype=np.int64)
    total_per_window = np.zeros(n_win, dtype=np.int64)
    max_m = 0
    for wi in usable_windows:
        lo = int(np.searchsorted(idx_full, wi, side="left"))
        hi = int(np.searchsorted(idx_full, wi, side="right"))
        if hi <= lo:
            continue
        window_gaps = gaps[lo: hi + 1]
        max_m = max(max_m, len(window_gaps))
        perm = bit_reversal_permutation(len(window_gaps))
        h = window_gaps[perm]
        code = reduced_classes(h[:-1], h[1:])
        total_per_window[wi] = len(code)
        for ci, cc in enumerate(top_codes):
            class_counts[ci, wi] = int(np.count_nonzero(code == cc))
    other_counts = total_per_window - class_counts.sum(axis=0)
    return total_per_window, class_counts, other_counts, max_m


# ------------------------------------------------------------------ CSV writers

def write_amplitudes_csv(path, class_labels, whole_counts, amp):
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        header = ["class", "whole_range_count"]
        for i, freq in enumerate(ALL_FREQS):
            tag = "zeta" if i < 5 else "ctrl"
            header.append(f"A_{tag}_{freq:.6f}")
        w.writerow(header)
        for ci, lab in enumerate(class_labels):
            row = [lab, int(whole_counts[ci])] + [f"{v:.10f}" for v in amp[ci]]
            w.writerow(row)


# ------------------------------------------------------------------ main

def run():
    global LOGF
    os.makedirs(OUT_DIR, exist_ok=True)
    log_path = os.path.join(OUT_DIR, "run.log")
    LOGF = open(log_path, "w")
    t_run_start = time.time()

    log("prime-seasons.py START")
    log("=== full module docstring (declaration readings R1-R8) ===")
    for line in __doc__.splitlines():
        LOGF.write(line + "\n")
    LOGF.write("=== end docstring ===\n\n")
    LOGF.flush()

    log(f"repo root        = {REPO_ROOT}")
    log(f"output dir       = {OUT_DIR}")
    log(f"python           = {sys.version.split()[0]}")
    log(f"numpy version    = {np.__version__}")
    log(f"N_PRIME = 2^28   = {N_PRIME}")
    log(f"N_LUCKY = 2^22   = {N_LUCKY}")
    log(f"WINDOW_WIDTH     = {WINDOW_WIDTH}")
    log(f"MIN_PAIRS_USABLE = {MIN_PAIRS_USABLE}")
    log(f"U_START=ln(1e4)  = {U_START:.6f}")
    log(f"U_END(primes)    = {math.log(N_PRIME):.6f}")
    log(f"U_END(luckies)   = {math.log(N_LUCKY):.6f}")

    # ---- assertion: every control >= 0.6 from every zero ordinate below 65
    worst = None
    for c in CONTROLS:
        for z in ZERO_LIST_BELOW_65:
            d = abs(c - z)
            if worst is None or d < worst[0]:
                worst = (d, c, z)
            assert d >= 0.6, f"control {c} within 0.6 of zero {z} (d={d})"
    log(f"ASSERTION PASSED: all {len(CONTROLS)} controls are >= 0.6 from every "
        f"one of the {len(ZERO_LIST_BELOW_65)} listed zero ordinates below 65 "
        f"(closest approach: control {worst[1]} to zero {worst[2]}, d={worst[0]:.6f}).")

    # ================================================================ PRIMES
    t0 = time.time()
    log("sieve_primes(2^28): start")
    primes = sieve_primes(N_PRIME)
    log(f"sieve_primes(2^28): done in {time.time()-t0:.2f}s -- {len(primes)} primes")

    t0 = time.time()
    gaps, gap1, gap2, mid = consecutive_gap_pairs(primes)
    code = reduced_classes(gap1, gap2)
    log(f"consecutive_gap_pairs + reduced_classes (primes): "
        f"{time.time()-t0:.2f}s -- {len(code)} triples")

    t0 = time.time()
    top_codes, top_counts, whole_total = whole_range_top10(code)
    top_labels = [class_label(cc) for cc in top_codes]
    other_whole = whole_total - int(top_counts.sum())
    log(f"whole_range_top10 (primes): {time.time()-t0:.2f}s -- "
        f"{whole_total} triples total (unrestricted whole-range, reading R3)")
    log("TOP 10 mirror classes (real primes, whole-range census):")
    for rank, (lab, cnt) in enumerate(zip(top_labels, top_counts), 1):
        log(f"  {rank:2d}. {lab:>8s}  count={int(cnt)}  frac={cnt/whole_total:.6f}")
    log(f"  OTHER  count={other_whole}  frac={other_whole/whole_total:.6f}")

    u_end_primes = math.log(N_PRIME)
    t0 = time.time()
    n_win, idx_full, total_pw, class_pw, other_pw = per_window_class_counts(
        mid, code, u_end_primes, top_codes)
    log(f"per_window_class_counts (primes): {time.time()-t0:.2f}s -- "
        f"{n_win} grid windows")

    centers = window_centers(n_win)
    usable_mask = total_pw >= MIN_PAIRS_USABLE
    usable_windows = np.flatnonzero(usable_mask)
    if len(usable_windows):
        log(f"usable windows (primes, >= {MIN_PAIRS_USABLE} pairs): "
            f"{len(usable_windows)} of {n_win} grid windows "
            f"(u in [{centers[usable_windows[0]]:.4f}, "
            f"{centers[usable_windows[-1]]:.4f}]); "
            f"max pairs in one window = {int(total_pw.max())}")
    else:
        log("usable windows (primes): 0 -- NO WINDOW MET THE THRESHOLD")

    # ---- census.csv (real, ALL grid windows)
    census_path = os.path.join(OUT_DIR, "census.csv")
    with open(census_path, "w", newline="") as f:
        wtr = csv.writer(f)
        wtr.writerow(["window_index", "u_center", "total_pairs", "usable"]
                     + top_labels + ["OTHER"])
        for wi in range(n_win):
            row = [wi, f"{centers[wi]:.6f}", int(total_pw[wi]), int(usable_mask[wi])]
            row += [int(class_pw[ci, wi]) for ci in range(len(top_codes))]
            row.append(int(other_pw[wi]))
            wtr.writerow(row)
    log(f"wrote {census_path}")

    # ---- spectral read (real)
    t0 = time.time()
    u_centers_usable = centers[usable_windows]
    fr_real = np.zeros((11, len(usable_windows)), dtype=np.float64)
    for ci in range(10):
        fr_real[ci] = class_pw[ci, usable_windows] / total_pw[usable_windows]
    fr_real[10] = other_pw[usable_windows] / total_pw[usable_windows]
    amp_real = spectral_amplitudes(u_centers_usable, fr_real)
    labels_real = top_labels + ["OTHER"]
    whole_counts_real = list(top_counts) + [other_whole]
    write_amplitudes_csv(os.path.join(OUT_DIR, "amplitudes_real.csv"),
                         labels_real, whole_counts_real, amp_real)
    log(f"spectral read (real): {time.time()-t0:.2f}s")
    log(f"wrote {os.path.join(OUT_DIR, 'amplitudes_real.csv')}")

    # ================================================================ F1 surrogate
    t0 = time.time()
    total_pw_f1, class_pw_f1, other_pw_f1, max_m = surrogate_window_counts(
        gaps, idx_full, usable_windows, n_win, top_codes)
    mismatch = np.flatnonzero(total_pw_f1[usable_windows] != total_pw[usable_windows])
    if len(mismatch):
        log(f"WARNING: F1 total-pairs mismatch in {len(mismatch)} windows "
            f"(should be impossible for a multiset-preserving permutation)")
    else:
        log("F1 consistency check passed: total-pairs-per-window identical to "
            "real in every usable window (gap multiset exactly preserved).")
    log(f"F1 largest per-window gap sequence length = {max_m}")
    fr_f1 = np.zeros((11, len(usable_windows)), dtype=np.float64)
    for ci in range(10):
        fr_f1[ci] = class_pw_f1[ci, usable_windows] / total_pw_f1[usable_windows]
    fr_f1[10] = other_pw_f1[usable_windows] / total_pw_f1[usable_windows]
    amp_f1 = spectral_amplitudes(u_centers_usable, fr_f1)
    write_amplitudes_csv(os.path.join(OUT_DIR, "amplitudes_surrogate.csv"),
                         labels_real, whole_counts_real, amp_f1)
    log(f"F1 (order surrogate): {time.time()-t0:.2f}s")
    log(f"wrote {os.path.join(OUT_DIR, 'amplitudes_surrogate.csv')}")

    # ================================================================ CHEBYSHEV (real primes)
    t0 = time.time()
    u_p = np.log(primes.astype(np.float64))
    idx_p = window_index(u_p)
    valid_p = (idx_p >= 0) & (idx_p < n_win)
    r = primes % 4
    is3 = valid_p & (r == 3)
    is1 = valid_p & (r == 1)
    count3_pw = np.bincount(idx_p[is3], minlength=n_win)
    count1_pw = np.bincount(idx_p[is1], minlength=n_win)
    lead_pw = count3_pw.astype(np.int64) - count1_pw.astype(np.int64)
    cumulative = np.cumsum(lead_pw)
    log(f"chebyshev tabulation: {time.time()-t0:.2f}s -- "
        f"final cumulative lead = {int(cumulative[-1])}")

    cheb_path = os.path.join(OUT_DIR, "chebyshev.csv")
    with open(cheb_path, "w", newline="") as f:
        wtr = csv.writer(f)
        wtr.writerow(["window_index", "u_center", "count_3mod4", "count_1mod4",
                     "window_lead", "cumulative_lead"])
        for wi in range(n_win):
            wtr.writerow([wi, f"{centers[wi]:.6f}", int(count3_pw[wi]),
                         int(count1_pw[wi]), int(lead_pw[wi]), int(cumulative[wi])])
    log(f"wrote {cheb_path}")

    signs = np.sign(cumulative)
    inversions = [wi for wi in range(1, n_win) if signs[wi] != signs[wi - 1]]
    inv_path = os.path.join(OUT_DIR, "inversions.txt")
    with open(inv_path, "w") as f:
        f.write("Chebyshev cumulative-lead (count 3mod4 - count 1mod4) sign "
                "inversions, over the FULL window grid (reading R6: all grid "
                f"windows, not restricted to the spectral-usable subset).\n")
        f.write(f"grid: window 0..{n_win-1}, u_center "
               f"{centers[0]:.4f}..{centers[-1]:.4f}\n")
        f.write(f"total inversions: {len(inversions)}\n\n")
        f.write(f"{'window_index':>13s} {'u_center':>10s} "
               f"{'prev_lead':>10s} {'new_lead':>10s} "
               f"{'prev_sign':>10s} {'new_sign':>9s}\n")
        for wi in inversions:
            f.write(f"{wi:13d} {centers[wi]:10.4f} "
                   f"{int(cumulative[wi-1]):10d} {int(cumulative[wi]):10d} "
                   f"{int(signs[wi-1]):10d} {int(signs[wi]):9d}\n")
    log(f"wrote {inv_path} -- {len(inversions)} inversions")
    if inversions:
        preview = ", ".join(
            f"w{wi}(u={centers[wi]:.3f})" for wi in inversions[:10])
        log(f"first inversions: {preview}")

    # ================================================================ LUCKIES (F2)
    t0 = time.time()
    log("lucky_sieve(2^22): start")
    luckies = lucky_sieve(N_LUCKY)
    log(f"lucky_sieve(2^22): done in {time.time()-t0:.2f}s -- {len(luckies)} luckies")

    t0 = time.time()
    l_gaps, l_gap1, l_gap2, l_mid = consecutive_gap_pairs(luckies)
    l_code = reduced_classes(l_gap1, l_gap2)
    l_top_codes, l_top_counts, l_whole_total = whole_range_top10(l_code)
    l_top_labels = [class_label(cc) for cc in l_top_codes]
    l_other_whole = l_whole_total - int(l_top_counts.sum())
    log(f"whole_range_top10 (luckies): {time.time()-t0:.2f}s -- "
        f"{l_whole_total} triples total (unrestricted whole-range, reading R3/R5)")
    log("TOP 10 mirror classes (luckies, own independent whole-range census):")
    for rank, (lab, cnt) in enumerate(zip(l_top_labels, l_top_counts), 1):
        log(f"  {rank:2d}. {lab:>8s}  count={int(cnt)}  frac={cnt/l_whole_total:.6f}")
    log(f"  OTHER  count={l_other_whole}  frac={l_other_whole/l_whole_total:.6f}")

    u_end_lucky = math.log(N_LUCKY)
    t0 = time.time()
    l_n_win, l_idx_full, l_total_pw, l_class_pw, l_other_pw = per_window_class_counts(
        l_mid, l_code, u_end_lucky, l_top_codes)
    l_centers = window_centers(l_n_win)
    l_usable_mask = l_total_pw >= MIN_PAIRS_USABLE
    l_usable_windows = np.flatnonzero(l_usable_mask)
    log(f"per_window_class_counts (luckies): {time.time()-t0:.2f}s -- "
        f"{l_n_win} grid windows")
    if len(l_usable_windows):
        log(f"usable windows (luckies, >= {MIN_PAIRS_USABLE} pairs): "
            f"{len(l_usable_windows)} of {l_n_win} grid windows "
            f"(u in [{l_centers[l_usable_windows[0]]:.4f}, "
            f"{l_centers[l_usable_windows[-1]]:.4f}])")
    else:
        log("usable windows (luckies): 0 -- NO WINDOW MET THE THRESHOLD")

    t0 = time.time()
    l_u_centers_usable = l_centers[l_usable_windows]
    fr_l = np.zeros((11, len(l_usable_windows)), dtype=np.float64)
    for ci in range(10):
        fr_l[ci] = l_class_pw[ci, l_usable_windows] / l_total_pw[l_usable_windows]
    fr_l[10] = l_other_pw[l_usable_windows] / l_total_pw[l_usable_windows]
    amp_l = spectral_amplitudes(l_u_centers_usable, fr_l)
    l_labels = l_top_labels + ["OTHER"]
    l_whole_counts = list(l_top_counts) + [l_other_whole]
    write_amplitudes_csv(os.path.join(OUT_DIR, "amplitudes_lucky.csv"),
                         l_labels, l_whole_counts, amp_l)
    log(f"F2 spectral read (luckies): {time.time()-t0:.2f}s")
    log(f"wrote {os.path.join(OUT_DIR, 'amplitudes_lucky.csv')}")

    total_time = time.time() - t_run_start
    log(f"TOTAL RUNTIME: {total_time:.2f}s")
    log("prime-seasons.py DONE")
    LOGF.close()


def main():
    global LOGF
    try:
        run()
    except Exception:
        tb = traceback.format_exc()
        sys.stderr.write(tb)
        if LOGF is not None and not LOGF.closed:
            LOGF.write("\n=== EXCEPTION ===\n")
            LOGF.write(tb)
            LOGF.close()
        sys.exit(1)


if __name__ == "__main__":
    main()
