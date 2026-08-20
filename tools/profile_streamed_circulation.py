#!/usr/bin/env python3
"""Derive Deed H4's profile faces from one Nsight Systems export.

The instrument is exterior apparatus: it measures the realization and testifies for nothing
semantic. What it is asked here is exactly the four questions H0 left open for the streamed
circulation, and every one of them is a measurement rather than a permission:

  1. how many octets of transfer are CONCURRENT with a kernel (H0 measured 0 ns of 415 ms);
  2. what fraction of the deed's span the card is busy (H0 measured 10.22 % of the kernel span,
     4.27 % of the wall);
  3. the driver-API census: cuGraphLaunch, cuStreamSynchronize, cuCtxSynchronize, cuMemAlloc,
     cuMemFree, and the host-to-device copies;
  4. the wall.

Usage:
    python3 tools/profile_streamed_circulation.py <export.sqlite> <output directory>

Writes `profile.tsv` (one reading per row, every one carrying its own unit) and
`overlap-timeline.tsv` (every transfer with the kernel time it overlapped). stdlib only.
"""

import sqlite3
import sys
from pathlib import Path

UNKNOWN = "unknown"


def union_length(intervals):
    """The measure of the union of half-open intervals — the card's busy time, counted once even
    where several kernels are in flight."""
    if not intervals:
        return 0
    ordered = sorted(intervals)
    total = 0
    start, end = ordered[0]
    for a, b in ordered[1:]:
        if a > end:
            total += end - start
            start, end = a, b
        else:
            end = max(end, b)
    total += end - start
    return total


def intersection_length(left, right):
    """The measure of the intersection of two interval unions: transfer time that is also kernel
    time. This is the overlap the plan asks for, and it is a measurement of the CARD, not a
    permission granted by a stream."""
    left = merge(left)
    right = merge(right)
    total = 0
    i = j = 0
    while i < len(left) and j < len(right):
        a0, a1 = left[i]
        b0, b1 = right[j]
        low = max(a0, b0)
        high = min(a1, b1)
        if high > low:
            total += high - low
        if a1 < b1:
            i += 1
        else:
            j += 1
    return total


def merge(intervals):
    if not intervals:
        return []
    ordered = sorted(intervals)
    merged = [list(ordered[0])]
    for a, b in ordered[1:]:
        if a > merged[-1][1]:
            merged.append([a, b])
        else:
            merged[-1][1] = max(merged[-1][1], b)
    return [tuple(pair) for pair in merged]


def table_exists(cur, name):
    cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name=?", (name,))
    return cur.fetchone() is not None


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    export = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(str(export))
    cur = connection.cursor()

    kernels = []
    if table_exists(cur, "CUPTI_ACTIVITY_KIND_KERNEL"):
        cur.execute("SELECT start, end FROM CUPTI_ACTIVITY_KIND_KERNEL")
        kernels = [(int(a), int(b)) for a, b in cur.fetchall()]

    transfers = []
    if table_exists(cur, "CUPTI_ACTIVITY_KIND_MEMCPY"):
        cur.execute("SELECT start, end, bytes, copyKind, streamId FROM CUPTI_ACTIVITY_KIND_MEMCPY")
        transfers = [(int(a), int(b), int(c), int(d), int(e)) for a, b, c, d, e in cur.fetchall()]

    memsets = []
    if table_exists(cur, "CUPTI_ACTIVITY_KIND_MEMSET"):
        cur.execute("SELECT start, end FROM CUPTI_ACTIVITY_KIND_MEMSET")
        memsets = [(int(a), int(b)) for a, b in cur.fetchall()]

    api = {}
    if table_exists(cur, "CUPTI_ACTIVITY_KIND_RUNTIME"):
        cur.execute(
            """SELECT s.value, COUNT(*), SUM(r.end - r.start)
                 FROM CUPTI_ACTIVITY_KIND_RUNTIME r
                 JOIN StringIds s ON s.id = r.nameId
                GROUP BY s.value"""
        )
        api = {name: (int(count), int(total or 0)) for name, count, total in cur.fetchall()}

    kernel_intervals = kernels
    transfer_intervals = [(a, b) for a, b, *_ in transfers]
    card_intervals = kernel_intervals + [(a, b) for a, b in memsets]

    kernel_busy = union_length(kernel_intervals)
    card_busy = union_length(card_intervals)
    transfer_busy = union_length(transfer_intervals)
    overlap = intersection_length(transfer_intervals, kernel_intervals)

    everything = card_intervals + transfer_intervals
    if everything:
        span_start = min(a for a, _ in everything)
        span_end = max(b for _, b in everything)
    else:
        span_start = span_end = 0
    span = span_end - span_start

    wall = UNKNOWN
    if table_exists(cur, "ANALYSIS_DETAILS"):
        cur.execute("SELECT duration FROM ANALYSIS_DETAILS")
        row = cur.fetchone()
        if row and row[0]:
            wall = int(row[0])

    htod = [t for t in transfers if t[3] == 1]
    dtoh = [t for t in transfers if t[3] == 2]

    rows = [
        ("kernels", len(kernel_intervals), "count"),
        ("memsets", len(memsets), "count"),
        ("transfers", len(transfers), "count"),
        ("transfers-host-to-device", len(htod), "count"),
        ("transfers-device-to-host", len(dtoh), "count"),
        ("octets-host-to-device", sum(t[2] for t in htod), "octets"),
        ("octets-device-to-host", sum(t[2] for t in dtoh), "octets"),
        ("kernel-span", span, "ns from the first card event to the last"),
        ("kernel-busy-union", kernel_busy, "ns, counted once where several are in flight"),
        ("card-busy-union", card_busy, "ns, kernels and memsets"),
        ("transfer-busy-union", transfer_busy, "ns"),
        ("transfer-kernel-overlap", overlap, "ns of transfer that is also kernel time (H0 measured 0)"),
        (
            "transfer-overlap-fraction-numerator",
            overlap,
            "ns; the denominator is transfer-busy-union — a ratio, carried as a pair",
        ),
        ("card-busy-fraction-numerator", card_busy, "ns; the denominator is kernel-span"),
        ("wall", wall, "ns as the profiler measured the session"),
    ]
    for name, (count, total) in sorted(api.items()):
        if name.startswith("cuGraphLaunch") or name.startswith("cuStreamSynchronize") or name.startswith("cuCtxSynchronize") \
           or name.startswith("cuMemAlloc") or name.startswith("cuMemFree") or name.startswith("cuMemcpy") \
           or name.startswith("cuMemHostAlloc") or name.startswith("cuGraphInstantiate") or name.startswith("cuStreamBeginCapture") \
           or name.startswith("cuStreamEndCapture") or name.startswith("cuLaunchKernel"):
            rows.append((f"api:{name}", count, f"calls, {total} ns total"))

    with (out / "profile.tsv").open("w") as handle:
        handle.write("reading\tvalue\tunit\n")
        for name, value, unit in rows:
            handle.write(f"{name}\t{value}\t{unit}\n")

    merged_kernels = merge(kernel_intervals)
    with (out / "overlap-timeline.tsv").open("w") as handle:
        handle.write("start_ns\tend_ns\toctets\tcopy_kind\tstream\toverlapped_ns\n")
        for a, b, octets, kind, stream in sorted(transfers):
            covered = intersection_length([(a, b)], merged_kernels)
            handle.write(f"{a}\t{b}\t{octets}\t{kind}\t{stream}\t{covered}\n")

    for name, value, unit in rows:
        print(f"{name}\t{value}\t{unit}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
