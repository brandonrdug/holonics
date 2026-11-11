#!/usr/bin/env python3
"""A lap's time budget from a FIELD_PROFILE read of the field's card driver (a host ruler on a run's own log).

Usage: python3 profile_budget.py prof_rt9_train.profile.txt [short_us]

Reads the FIELD_PROFILE entry lines (launches, ms, us a launch), FIELD_PROFILE_SPLIT (kernels, copies,
allocations, elapsed) and FIELD_CARD (reads, returns, pairs met, batches, peak store), and prints each part's
share of the elapsed time, the entries by kernel time, and the counts a batch. An entry is short when its mean
time a launch is under `short_us` (200 by default). The contact and affine families are named below.
"""
import re
import sys

CONTACT = ("field_exposure", "field_contact_", "field_pair", "field_echo_trips", "field_spread", "field_pace_skin_back")
AFFINE = ("field_affine_",)


def fields(line):
    return {k: v for k, v in (p.split("=", 1) for p in line.split()[1:] if "=" in p)}


def main():
    path = sys.argv[1]
    short_us = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    entries, split, card = [], {}, {}
    for line in open(path):
        if line.startswith("FIELD_PROFILE_SPLIT"):
            split = {k: int(v) for k, v in fields(line).items()}
        elif line.startswith("FIELD_PROFILE "):
            f = fields(line)
            entries.append((f["entry"], int(f["launches"]), int(f["ms"]), int(f["us_a_launch"])))
        elif line.startswith("FIELD_CARD "):
            card = {k: int(v) for k, v in fields(line).items()}
    elapsed, kernels = split["elapsed_ms"], split["kernels_ms"]
    launches = sum(e[1] for e in entries)
    short = [e for e in entries if e[3] < short_us]
    wide = [e for e in entries if e[3] >= short_us]
    short_ms, wide_ms = sum(e[2] for e in short), sum(e[2] for e in wide)
    summed = short_ms + wide_ms
    host = elapsed - kernels - split["copies_ms"] - split["allocations_ms"]
    print(f"elapsed_ms={elapsed} kernels_ms={kernels} entries_ms={summed} launches={launches} entries={len(entries)}")
    print(f"share_of_elapsed kernels={kernels / elapsed:.3f} wide={wide_ms / summed * kernels / elapsed:.3f} short={short_ms / summed * kernels / elapsed:.3f} "
          f"allocations={split['allocations_ms'] / elapsed:.3f} copies={split['copies_ms'] / elapsed:.3f} host={host / elapsed:.3f}")
    print(f"short_launches={sum(e[1] for e in short)} mean_us={1000 * short_ms / max(1, sum(e[1] for e in short)):.0f} share_of_kernel={short_ms / summed:.3f} least_us_a_launch={min(e[3] for e in entries)}")
    print(f"allocation_us={1000 * split['allocations_ms'] / split['allocations']:.1f} copy_us={1000 * split['copies_ms'] / split['copies']:.1f}")
    contact = sum(e[2] for e in entries if e[0].startswith(CONTACT))
    affine = sum(e[2] for e in entries if e[0].startswith(AFFINE))
    top = sorted(entries, key=lambda e: -e[2])
    print(f"share_of_kernel contact={contact / summed:.3f} affine={affine / summed:.3f} top_five={sum(e[2] for e in top[:5]) / summed:.3f}")
    if card:
        runs = card["reads"] + card["returns"]
        b = card["batches"]
        print(f"reads={card['reads']} returns={card['returns']} batches={b} batches_a_run={b / runs:.2f} pairs_met={card['pairs']} pairs_a_run={card['pairs'] / runs:.3e} peak_store={card['peak_store']}")
        print(f"a_batch launches={launches / b:.0f} allocations={split['allocations'] / b:.0f} copies={split['copies'] / b:.0f}")
    for name, n, ms, us in top[:16]:
        print(f"{name:34s} launches={n:7d} ms={ms:6d} us_a_launch={us:6d} share_of_kernel={ms / summed:.3f}")


main()
