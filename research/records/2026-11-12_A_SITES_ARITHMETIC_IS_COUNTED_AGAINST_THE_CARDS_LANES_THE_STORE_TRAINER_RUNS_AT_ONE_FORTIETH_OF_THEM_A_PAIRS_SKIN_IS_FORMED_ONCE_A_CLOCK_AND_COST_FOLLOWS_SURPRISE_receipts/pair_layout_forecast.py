#!/usr/bin/env python3 -I
"""pair_layout_forecast.py PROFILE --store DIR --keys K --pairs P --sites S --from F --to T: P53 item 2, a forecast from source at main (no build).

The pair store's words and walks read from `kernels/field.cu` (agent-inferred, none measured); the once-a-word floor of the contact family on the
hundred sections of the profiled read, today's (contact_forecast.py's COMPULSORY, 12,932 ms on step 3's read) beside three layouts:
(1) a pair's own words as one record in the order its receiver's support list is walked (in order, no sector a word); (2) the same with a tick's
entries of that order as one launch (the record and the source rows read once a launch); (3) the same at the words' occupied bits, owed: the bits
need a reading on the card, which this order does not build. The columns walk the transpose: (e) a second copy of the records in the sources'
order against reaching the receivers' records through an index. Rates: P50 step 0's yardsticks. Numbers only.
"""
import argparse
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import contact_forecast as cf  # noqa: E402

GATHER, ORDER, TICKS = cf.GATHER, cf.ORDER, cf.TICKS

# (a) A pair's words: (word, array, octets, index, heads), and the entries that read (R) or write (W) it.
WORDS = [
    ("score then share", "e", 8, "dense block [h][E]: receiver i, source j (region_eoff + i S + j)", "all"),
    ("lock at unit gain", "sb", 8, "dense block [h][E] (a return)", "all"),
    ("ds", "ds", 8, "dense block [E], one head at a time (a return)", "all"),
    ("covector dp", "dpb", 16, "dense block [E], one head at a time (a return)", "all"),
    ("skins (8 modes)", "skin", 32, "support stride [p][E2]: receiver i, entry k (region_soff + i K_r + k)", "paced"),
]
USES = {  # entry: [(array, R/W)]
    "field_exposure": [("e", "W"), ("sb", "W"), ("skin", "R")],
    "field_skin_fill": [("skin", "W")],
    "field_contact_l5": [("e", "R"), ("e", "W"), ("skin", "R")],
    "field_contact_rows": [("e", "R"), ("sb", "R"), ("dpb", "W"), ("dpb", "R"), ("ds", "W"), ("skin", "R")],
    "field_pace_skin_back": [("e", "R"), ("ds", "R"), ("skin", "R")],
    "field_contact_columns": [("e", "R"), ("ds", "R"), ("skin", "R")],
}
# (b) The walks: (entry, pass, launches a tick, the list, its order).
WALKS = [
    ("field_exposure", "forward", "1 (every head)", "receiver i's support", "near slots, then the probed classes' runs (or the region's definite list)"),
    ("field_skin_fill", "forward and return", "1 each (paced heads)", "receiver i's support", "the same"),
    ("field_contact_l5", "forward", "1 (every head)", "receiver i's support, twice", "the same"),
    ("field_contact_rows", "return", "1 a head", "receiver i's support, twice", "the same"),
    ("field_pace_skin_back", "return", "1 a paced head", "receiver i's support", "the same"),
    ("field_contact_columns", "return", "1 a head", "source j's receivers", "near slots, then the probers of j's class (their order an atomic's), then the open receivers"),
    ("field_spread", "return", "1 a head", "a region's sites", "in place order (no pair)"),
]
ORDERED = {"e": False, "sb": False, "ds": False, "dpb": False, "skin": True}  # the row walk meets the array in its own order


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
            pairs[int(kv["head"])], kinds[int(kv["head"])] = int(kv["pairs"]), kv["kind"]
        elif line.startswith("FIELD_PROFILE entry="):
            kv = dict(w.split("=", 1) for w in line.split()[1:])
            measured[kv["entry"]] = int(kv["ms"])
    geo = cf.geometry(a)
    heads = sorted(pairs)
    rows = geo["rows"]
    print(f"GEOMETRY sections={geo['sections']} rows_a_tick={rows} pairs_by_head={[pairs[h] for h in heads]} kinds={[kinds[h] for h in heads]}")
    print("## (a) a pair's words")
    for w in WORDS:
        meets = ", ".join(f"{e}:{'own order' if (ORDERED[w[1]] and e != 'field_contact_columns') else 'not its order'}" for e, us in USES.items() if any(x[0] == w[1] for x in us))
        print(f"WORD word={w[0]!r} array={w[1]} octets={w[2]} heads={w[4]} index={w[3]!r} walks={meets}")
    print("WORD bits_by_head_at_state_C=owed (the largest magnitude's and the 0.999 quantile's bits need a reading of the words on the card; not built under this order)")
    print("## (b) the walks")
    for w in WALKS:
        print(f"WALK entry={w[0]} pass={w[1]} launches_a_tick={w[2]!r} list={w[3]!r} order={w[4]!r}")
    print("WALK same_list_same_order=field_exposure,field_skin_fill,field_contact_l5,field_contact_rows,field_pace_skin_back (the receiver's support); field_contact_columns walks the transpose")
    print("## (c) the rows a pair reads through its source")
    per_site = {"value row vf": 128, "word row qf": 128, "probe row pq": 128, "key row qf32": 64, "probe row pq32": 64}
    for k, v in per_site.items():
        print(f"SOURCE row={k!r} octets={v} distinct_a_head_a_tick={rows} octets_a_head_a_tick={rows * v // geo['sections']}_a_section")
    for h in heads:
        print(f"SOURCE head={h} kind={kinds[h]} mean_receivers_a_source={pairs[h] / (rows * TICKS):.1f}")
    print("SOURCE card_L2_octets=67108864 shared_octets_a_multiprocessor=102400 (the driver's cuDeviceGetAttribute: L2_CACHE_SIZE, MAX_SHARED_MEMORY_PER_MULTIPROCESSOR)")
    print(f"SOURCE a_section_a_head_rows_read_through_sources={rows // geo['sections'] * 448} octets (vf, qf, pq, qf32; a region's of some 200 sites about 90 KB a head)")
    # (d) the floors.
    site_terms = {}
    for t in cf.COMPULSORY:
        if t[1] == "site":
            site_terms.setdefault(t[0], []).append(t)
    field = {w[1]: w[2] for w in WORDS}

    def units(heads_kind):
        return [h for h in heads if heads_kind == "all" or kinds[h] == heads_kind]

    def site_octets(e):
        o = 0
        for t in site_terms.get(e, []):
            o += rows * TICKS * len(units(t[6])) * t[4] * cf.PASSES.get(e, 1)
        return o

    def record_octets(e):
        o = 0
        for arr, _ in USES.get(e, []):
            kind = "paced" if arr == "skin" else "all"
            o += sum(pairs[h] for h in units(kind)) * field[arr] * cf.PASSES.get(e, 1)
        return o

    today = {}
    for e in sorted(USES) + ["field_spread"]:
        g = o = 0.0
        for t in cf.COMPULSORY:
            if t[0] != e:
                continue
            hs = units(t[6])
            u = (sum(pairs[h] for h in hs) if t[1] == "pair" else rows * TICKS * len(hs)) * cf.PASSES.get(e, 1)
            if t[3] == "G":
                g += u * 32 * t[5]
            else:
                o += u * t[4]
        today[e] = 1000 * (g / GATHER + o / ORDER)
    print("## (d) the family's once-a-word floor, ms over the read's sections, by entry")
    one = {}
    for e in sorted(USES) + ["field_spread"]:
        if e == "field_contact_columns":
            # (1) keeps the columns' walk: the receivers' records gathered, a sector a record field group (e and ds together, the skins apart).
            g = sum(pairs[h] for h in heads) * 32 + sum(pairs[h] for h in units("paced")) * 32
            one[e] = 1000 * (g / GATHER + site_octets(e) / ORDER)
        else:
            one[e] = 1000 * ((record_octets(e) + site_octets(e)) / ORDER)
        print(f"FLOOR layout=1 entry={e} today_ms={today[e]:.0f} record_in_order_ms={one[e]:.0f} measured_ms={measured.get(e, 0) + (measured.get('field_contact_l6', 0) if e == 'field_contact_l5' else 0)}")
    print(f"FLOOR layout=1 family today_ms={sum(today.values()):.0f} record_in_order_ms={sum(one.values()):.0f}")
    # (2) a tick's entries of the row order as one launch: forward (exposure, the forward fill, l5) and return (rows, skin back, the return fill).
    fwd_site = max(site_octets("field_exposure"), 0) + site_octets("field_contact_l5")
    ret_site = site_octets("field_contact_rows") + site_octets("field_pace_skin_back")
    paced_pairs = sum(pairs[h] for h in units("paced"))
    all_pairs = sum(pairs[h] for h in heads)
    fwd_record = all_pairs * (field["e"] + field["sb"]) + paced_pairs * field["skin"]  # written once
    ret_record = all_pairs * (field["e"] + field["sb"] + field["ds"]) + paced_pairs * field["skin"]  # e, sb, skins read once; ds written once; dp in registers
    fwd = 1000 * ((fwd_record + fwd_site + site_octets("field_skin_fill") / 2) / ORDER)
    ret = 1000 * ((ret_record + ret_site + site_octets("field_skin_fill") / 2) / ORDER)
    cols = one["field_contact_columns"]
    spread = one["field_spread"]
    print(f"FLOOR layout=2 forward_launch_ms={fwd:.0f} return_launch_ms={ret:.0f} columns_ms={cols:.0f} spread_ms={spread:.0f} family_ms={fwd + ret + cols + spread:.0f} (today 12,932 by the compulsory count)")
    print("FLOOR layout=3 owed: the records and the source rows at their occupied bits need the bits' reading (a)")
    # (e) the columns.
    copy_write_g = all_pairs * 32  # a second copy of (e, ds) in the sources' order, scattered as it is written by the rows' return
    copy_read_o = all_pairs * 16 + paced_pairs * 32
    index_read_g = all_pairs * 32 + paced_pairs * 32
    index_o = all_pairs * 4
    print(f"COLUMNS second_copy_octets_written_gathered={copy_write_g} read_in_order={copy_read_o} floor_ms={1000 * (copy_write_g / GATHER + copy_read_o / ORDER) + 1000 * site_octets('field_contact_columns') / ORDER:.0f}")
    print(f"COLUMNS through_an_index_octets_gathered={index_read_g} index_in_order={index_o} floor_ms={1000 * (index_read_g / GATHER + index_o / ORDER) + 1000 * site_octets('field_contact_columns') / ORDER:.0f}")


if __name__ == "__main__":
    main()
