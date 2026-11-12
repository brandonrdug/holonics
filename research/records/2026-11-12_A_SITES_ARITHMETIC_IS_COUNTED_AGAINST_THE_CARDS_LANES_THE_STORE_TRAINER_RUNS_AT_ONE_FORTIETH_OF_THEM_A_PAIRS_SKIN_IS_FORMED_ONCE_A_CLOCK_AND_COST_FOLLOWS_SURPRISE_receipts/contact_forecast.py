#!/usr/bin/env python3 -I
"""contact_forecast.py PROFILE --store DIR --keys K --pairs P --sites S --from F --to T: P52 item 3 (i) and (ii), a ruler on the host.

(i) Each entry of the contact family's octets, read from its source at `kernels/field.cu` (the build of P50 step 3) [agent-inferred, every row a
reading of the source, none measured]: by unit (a pair met, a computed row, an active crowd slot of a definite row, a site), by store, gathered (an
address that depends on the pair or the row: counted in 32-octet sectors, one an access at least) or in order (a warp's lanes on consecutive words:
counted in octets), for a still head and a paced head. The resident tables (the exponential's face, the decay rows, the class offsets, a receiver's
own rows reread by its lanes) are cached and not counted. (ii) Each entry's floor at the card's two yardsticks (P50 step 0: 1.4451e11 octets a second
gathered 32 at a time, 5.7247e11 in order) on the profiled read's pairs (its FIELD_PROFILE_PAIRS lines) and the census's rows and crowd slots of the
same sections (`store_stretch_census.py`), beside the entry's measured time (its FIELD_PROFILE line). Numbers only.
"""
import argparse
import glob
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
passage = glob.glob(os.path.join(here, "..", "2026-11-12_THE_PASSAGE_WIDENS_TO_FIVE_REGISTERS*_receipts"))
sys.path.insert(0, passage[0])
import store_stretch_census as census  # noqa: E402
from section_regions_census import NEAR, popcount  # noqa: E402

GATHER, ORDER = 1.4451e11, 5.7247e11
TICKS = 4

# The terms: (entry, unit, store, kind, octets, accesses, heads), unit one of pair, row, slot, site; kind G (gathered: `accesses` sectors at least
# `ceil(octets / 32)`) or O (in order: octets); heads "all", "still" or "paced". A value, key or probe row is a source's 16 words of 8 octets (128).
TERMS = [
    # field_exposure: one warp a (head, receiver), a lane a support entry (pair_base8 on the key row's 16 words of 32 bits).
    ("field_exposure", "pair", "support list (members, near keys)", "O", 4, 0, "all"),
    ("field_exposure", "pair", "source key row (qf32, 64 octets)", "G", 64, 2, "all"),
    ("field_exposure", "pair", "score e[i][j], written", "G", 8, 1, "all"),
    ("field_exposure", "pair", "lock sb[i][j], written (a return)", "G", 8, 1, "all"),
    ("field_exposure", "pair", "source class (cls, a still head's falloff)", "G", 4, 1, "still"),
    ("field_exposure", "pair", "skins, the clock's store (8 words)", "O", 32, 0, "paced"),
    ("field_exposure", "row", "receiver probe row (pq32)", "O", 64, 0, "all"),
    ("field_exposure", "slot", "crowd prefix sums sw at lo and hi+1 (2 x 16 x 16 octets)", "G", 512, 16, "all"),
    ("field_exposure", "slot", "crowd count sc at lo and hi+1", "G", 16, 2, "all"),
    ("field_exposure", "slot", "crowd edge skins (8 words)", "O", 32, 0, "paced"),
    # field_contact_l5/l6: the row's mass and numerators (lanes over the span's entries for a pair's value), then the shares stored.
    ("field_contact_l5", "pair", "support list, twice", "O", 8, 0, "all"),
    ("field_contact_l5", "pair", "score e[i][j], read twice", "G", 16, 2, "all"),
    ("field_contact_l5", "pair", "source value row (vf)", "G", 128, 4, "all"),
    ("field_contact_l5", "pair", "share e[i][j], written", "G", 8, 1, "all"),
    ("field_contact_l5", "pair", "skins, the clock's store", "O", 32, 0, "paced"),
    ("field_contact_l5", "row", "current y, written", "O", 128, 0, "all"),
    ("field_contact_l5", "slot", "crowd score (sw at lo, hi+1), twice", "G", 1024, 32, "all"),
    ("field_contact_l5", "slot", "crowd values (sv at lo, hi+1)", "G", 512, 16, "all"),
    ("field_contact_l5", "slot", "crowd share ce, written", "G", 8, 1, "all"),
    ("field_contact_l5", "slot", "crowd edge skins", "O", 32, 0, "paced"),
    # field_contact_rows: pass A (the pair's covector over the value row), pass B (dz, ds and the probe role over the word row), the crowds.
    ("field_contact_rows", "pair", "support list, twice", "O", 8, 0, "all"),
    ("field_contact_rows", "pair", "share e[i][j], twice", "G", 16, 2, "all"),
    ("field_contact_rows", "pair", "source value row (vf)", "G", 128, 4, "all"),
    ("field_contact_rows", "pair", "covector dp[i][j] (128 bits), written then read", "G", 32, 2, "all"),
    ("field_contact_rows", "pair", "lock sb[i][j]", "G", 8, 1, "all"),
    ("field_contact_rows", "pair", "ds[i][j], written", "G", 8, 1, "all"),
    ("field_contact_rows", "pair", "source word row (qf), the probe role", "G", 128, 4, "all"),
    ("field_contact_rows", "pair", "skins, the clock's store, twice", "O", 64, 0, "paced"),
    ("field_contact_rows", "row", "receiver covector row dyh", "O", 128, 0, "all"),
    ("field_contact_rows", "row", "dp and dq, written", "O", 256, 0, "all"),
    ("field_contact_rows", "slot", "crowd values sv (pass A)", "G", 512, 16, "all"),
    ("field_contact_rows", "slot", "crowd lock sw (pass B) and the probe role's sw", "G", 1024, 32, "all"),
    ("field_contact_rows", "slot", "crowd difference arrays cv, cw (128-bit atomics, 4 a lane)", "G", 1024, 32, "all"),
    ("field_contact_rows", "slot", "crowd share ce and dz cds", "G", 16, 2, "all"),
    ("field_contact_rows", "slot", "crowd edge skins, twice", "O", 64, 0, "paced"),
    # field_contact_columns: one warp a source j over its receivers i.
    ("field_contact_columns", "pair", "receiver list (pmem, olist, near)", "O", 4, 0, "all"),
    ("field_contact_columns", "pair", "ds[i][j] and e[i][j] (a column: a row's stride apart)", "G", 16, 2, "all"),
    ("field_contact_columns", "pair", "receiver probe row (pq)", "G", 128, 4, "all"),
    ("field_contact_columns", "pair", "receiver covector row (dyh)", "G", 128, 4, "all"),
    ("field_contact_columns", "pair", "the pair's support entry (pn, pcls, off, members by bisection, sc)", "G", 40, 2, "paced"),
    ("field_contact_columns", "pair", "skins, the clock's store (the receiver's row)", "G", 32, 1, "paced"),
    ("field_contact_columns", "row", "source word row, and dq, dv read and written", "O", 640, 0, "all"),
    # field_pace_skin_back: one warp a paced receiver, a lane a support entry, over its 8 modes.
    ("field_pace_skin_back", "pair", "support list", "O", 4, 0, "paced"),
    ("field_pace_skin_back", "pair", "source clock sigma", "G", 8, 1, "paced"),
    ("field_pace_skin_back", "pair", "skins, the clock's store", "O", 32, 0, "paced"),
    ("field_pace_skin_back", "pair", "source value row (16 words over the 8 modes)", "G", 128, 4, "paced"),
    ("field_pace_skin_back", "pair", "source word row", "G", 128, 4, "paced"),
    ("field_pace_skin_back", "pair", "e[i][j] and ds[i][j]", "G", 16, 2, "paced"),
    ("field_pace_skin_back", "pair", "the source's clock covector gsig (128-bit atomics, one a mode)", "G", 128, 8, "paced"),
    ("field_pace_skin_back", "slot", "crowd sv and sw at lo, hi+1 (8 modes)", "G", 1024, 32, "paced"),
    ("field_pace_skin_back", "slot", "crowd ce, cds, and the edge's gsig atomics (8)", "G", 144, 10, "paced"),
    ("field_pace_skin_back", "slot", "crowd edge skins", "O", 32, 0, "paced"),
    # field_skin_fill: one warp a (paced head, receiver), a lane a support entry; at each tick's forward and its return.
    ("field_skin_fill", "pair", "support list", "O", 4, 0, "paced"),
    ("field_skin_fill", "pair", "source clock sigma", "G", 8, 1, "paced"),
    ("field_skin_fill", "pair", "source site addresses (3 words a mode, 8 modes)", "G", 192, 8, "paced"),
    ("field_skin_fill", "pair", "skins, written to the store", "O", 32, 0, "paced"),
    # field_spread: a block a region, the difference arrays summed in order.
    ("field_spread", "site", "cv, cw read twice (16 entries of 128 bits each)", "O", 1024, 0, "all"),
    ("field_spread", "site", "dq, dv read and written (a definite site)", "O", 512, 0, "all"),
]
# How many times an entry runs over a unit in a section's ticks: the forward entries once a tick, the fill at the forward and at the return.
PASSES = {"field_skin_fill": 2}

# The compulsory traffic, a lower bound: each distinct word an entry touches in a launch brought from the card's memory once. A pair's entry in a
# region block (a word of 8 octets, `e`, `sb`, `ds`, or 16, `dp`) is a sector of its own (gathered: a row's support stands scattered in the block;
# a column's entries a row apart); the clock's skins a pair's 32 octets in order (a column's gathered); a site's rows (value, word, probe,
# covector: 128 octets; the prefix sums sw, sv: 256; the difference arrays cv, cw: 256, read and written in place) once a launch, in order.
# (entry, unit, distinct store, kind, octets, sectors, heads)
COMPULSORY = [
    ("field_exposure", "pair", "e and sb written", "G", 16, 2, "all"),
    ("field_exposure", "pair", "skins", "O", 32, 0, "paced"),
    ("field_exposure", "site", "key rows (qf32), probe rows (pq32), prefix sums sw, sc, classes", "O", 64 + 64 + 256 + 8 + 4, 0, "all"),
    ("field_contact_l5", "pair", "e read and written", "G", 16, 2, "all"),
    ("field_contact_l5", "pair", "skins", "O", 32, 0, "paced"),
    ("field_contact_l5", "site", "value rows, sw, sv, y", "O", 128 + 256 + 256 + 128, 0, "all"),
    ("field_contact_rows", "pair", "e, sb read, dp written and read, ds written", "G", 48, 4, "all"),
    ("field_contact_rows", "pair", "skins", "O", 32, 0, "paced"),
    ("field_contact_rows", "site", "value and word rows, dyh, sv, sw, cv and cw (read and written), dp and dq", "O", 128 * 3 + 256 * 2 + 512 * 2 + 256, 0, "all"),
    ("field_contact_columns", "pair", "ds and e (a row apart)", "G", 16, 2, "all"),
    ("field_contact_columns", "pair", "skins (the receiver's row)", "G", 32, 1, "paced"),
    ("field_contact_columns", "site", "probe, covector and word rows, dq and dv", "O", 128 * 3 + 256 * 2, 0, "all"),
    ("field_pace_skin_back", "pair", "e and ds", "G", 16, 2, "paced"),
    ("field_pace_skin_back", "pair", "skins", "O", 32, 0, "paced"),
    ("field_pace_skin_back", "site", "sigma, value and word rows, sv, sw, gsig", "O", 8 + 256 + 512 + 16, 0, "paced"),
    ("field_skin_fill", "pair", "skins written", "O", 32, 0, "paced"),
    ("field_skin_fill", "site", "sigma, site addresses", "O", 8 + 192, 0, "paced"),
    ("field_spread", "site", "cv and cw read twice, dq and dv read and written", "O", 1024 + 512, 0, "all"),
]


def geometry(a):
    """The census's rows, definite rows and active crowd slots of definite rows over the sections [from, to)."""
    out = {"rows": 0, "definite": 0, "slots": 0, "sections": 0}

    class Tally(census.Tally):
        def take(self, region):
            super().take(region)
            _, n, resolved, _ = region
            if self.section_live:
                out["rows"] += n
                out["definite"] += popcount(resolved)
                lv = 2
                while (1 << lv) < n:
                    near = max(1 << lv, NEAR)
                    left = resolved >> near  # definite rows at t >= near
                    right = resolved & ((1 << max(n - near, 0)) - 1)  # definite rows at t + near < n
                    out["slots"] += popcount(left) + popcount(right)
                    lv += 1

    state = {"n": 0}
    orig_init = Tally.__init__

    def init(self):
        orig_init(self)
        self.section_live = a.__dict__["from"] <= state["n"] < a.to
        state["n"] += 1

    Tally.__init__ = init
    census.Tally = Tally
    args = argparse.Namespace(store=a.store, role="prefix", keys=a.keys, pairs=a.pairs, sites=a.sites, sections=a.to, slice=None)
    out_stream = sys.stdout
    sys.stdout = open(os.devnull, "w")
    census.store(args)
    sys.stdout = out_stream
    out["sections"] = a.to - a.__dict__["from"]
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("profile")
    ap.add_argument("--store", required=True)
    ap.add_argument("--keys", required=True)
    for name in ("pairs", "sites", "from", "to"):
        ap.add_argument(f"--{name}", type=int, required=True)
    a = ap.parse_args()
    pairs, kinds, measured = {}, {}, {}
    for line in open(a.profile):
        if line.startswith("FIELD_PROFILE_PAIRS "):
            kv = dict(w.split("=", 1) for w in line.split()[1:])
            pairs[int(kv["head"])] = int(kv["pairs"])
            kinds[int(kv["head"])] = kv["kind"]
        elif line.startswith("FIELD_PROFILE entry="):
            kv = dict(w.split("=", 1) for w in line.split()[1:])
            measured[kv["entry"]] = int(kv["ms"])
    geo = geometry(a)
    heads = sorted(pairs)
    print(f"GEOMETRY sections={geo['sections']} rows_a_tick={geo['rows']} definite_rows_a_tick={geo['definite']} active_crowd_slots_a_tick={geo['slots']} ticks={TICKS} "
          f"pairs_by_head={[pairs[h] for h in heads]} kinds={[kinds[h] for h in heads]}")
    print("## (i) octets a unit, by entry and store (G: gathered, its sectors; O: in order)")
    for t in TERMS:
        print(f"TERM entry={t[0]} unit={t[1]} heads={t[6]} kind={t[3]} octets={t[4]} sectors={t[5] if t[3] == 'G' else '-'} store={t[2]!r}")
    entries = sorted({t[0] for t in TERMS}, key=lambda e: -measured.get(e, 0))
    print("## a pair's octets by entry and head kind (pair terms only; G as sectors x 32)")
    for e in entries:
        for kind in ("still", "paced"):
            g = sum(32 * t[5] for t in TERMS if t[0] == e and t[1] == "pair" and t[3] == "G" and t[6] in ("all", kind))
            o = sum(t[4] for t in TERMS if t[0] == e and t[1] == "pair" and t[3] == "O" and t[6] in ("all", kind))
            print(f"PAIR entry={e} head={kind} gathered_octets={g} in_order_octets={o}")
    print("## (ii) the floor at the yardsticks beside the measured time (ms over the read's sections)")
    total_floor = total_measured = 0.0
    for e in entries:
        g = o = 0.0
        passes = PASSES.get(e, 1)
        for t in TERMS:
            if t[0] != e:
                continue
            hs = [h for h in heads if t[6] == "all" or kinds[h] == t[6]]
            if e == "field_contact_l6" or not hs:
                continue
            if t[1] == "pair":
                units = sum(pairs[h] for h in hs)
            elif t[1] == "row":
                units = geo["rows"] * TICKS * len(hs)
            elif t[1] == "slot":
                units = geo["slots"] * TICKS * len(hs)
            else:
                units = geo["rows"] * TICKS * len(hs)
            units *= passes
            if t[3] == "G":
                g += units * 32 * t[5]
            else:
                o += units * t[4]
        floor_ms = 1000 * (g / GATHER + o / ORDER)
        ms = measured.get(e, 0) + (measured.get("field_contact_l6", 0) if e == "field_contact_l5" else 0)
        total_floor += floor_ms
        total_measured += ms
        print(f"FLOOR entry={e} gathered_GB={g / 1e9:.3f} in_order_GB={o / 1e9:.3f} floor_ms={floor_ms:.0f} measured_ms={ms} measured_over_floor={ms / max(floor_ms, 1e-9):.2f}")
    print(f"FLOOR family floor_ms={total_floor:.0f} measured_ms={total_measured:.0f} measured_over_floor={total_measured / total_floor:.2f} (the read's {geo['sections']} sections)")
    print("## (ii) the compulsory floor: each distinct word touched once a launch (a lower bound on the card's memory traffic)")
    tf = tm = 0.0
    for e in entries:
        g = o = 0.0
        passes = PASSES.get(e, 1)
        for t in COMPULSORY:
            if t[0] != e:
                continue
            hs = [h for h in heads if t[6] == "all" or kinds[h] == t[6]]
            units = (sum(pairs[h] for h in hs) if t[1] == "pair" else geo["rows"] * TICKS * len(hs)) * passes
            if t[3] == "G":
                g += units * 32 * t[5]
            else:
                o += units * t[4]
        floor_ms = 1000 * (g / GATHER + o / ORDER)
        ms = measured.get(e, 0) + (measured.get("field_contact_l6", 0) if e == "field_contact_l5" else 0)
        tf += floor_ms
        tm += ms
        print(f"COMPULSORY entry={e} gathered_GB={g / 1e9:.3f} in_order_GB={o / 1e9:.3f} floor_ms={floor_ms:.0f} measured_ms={ms} measured_over_floor={ms / max(floor_ms, 1e-9):.2f}")
    print(f"COMPULSORY family floor_ms={tf:.0f} measured_ms={tm:.0f} measured_over_floor={tm / tf:.2f}")


if __name__ == "__main__":
    main()
