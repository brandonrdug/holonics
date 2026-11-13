#!/usr/bin/env python3 -I
"""region_layout_forecast.py PROFILE --store DIR --keys K --pairs P --sites S --from F --to T: P54 item 3, layout 4 (a region resident for its
block), a forecast from source at main (no build) beside pair_layout_forecast.py's layouts 1 and 2. Every figure agent-inferred from source.

One block takes one region: it loads the region's source rows once into shared memory, every receiver walks its support with a pair's words as
one record in the walk's order, and the columns' transpose is taken in the same block from the same rows. A region's sites and pairs come from the
census of the read's sections (pairs: the dense block n^2 and the support stride's reservation n (NEAR_SLOTS + D), the met support per tick is not
in the census; the clocks change the support's classes, not a region's sites). Rates: P50 step 0's yardsticks. The driver's shared memory a
multiprocessor: 102,400 octets (cuDeviceGetAttribute MAX_SHARED_MEMORY_PER_MULTIPROCESSOR); a block's without opting in 49,152. Numbers only.
"""
import argparse
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import contact_forecast as cf  # noqa: E402
from section_regions_census import NEAR, popcount  # noqa: E402

SHARED_SM, ROWS_OWN = 102400, 20128
# A site's rows read through a source, a head (octets today; at item 2's proved widths: vf 16 words of 63 bits; qf, pq, qf32, pq32 16 words of 19
# bits, |w| <= 2^18 signed).
ROWS = {"vf": (128, 16 * 63 / 8), "qf": (128, 16 * 19 / 8), "pq": (128, 16 * 19 / 8), "qf32": (64, 16 * 19 / 8), "pq32": (64, 16 * 19 / 8)}
CHOICES = {"vf": ["vf"], "vf_qf": ["vf", "qf"], "all_five": list(ROWS)}


def quantiles(xs, qs=(0.5, 0.9, 0.99)):
    s = sorted(xs)
    return [s[min(len(s) - 1, int(q * len(s)))] for q in qs] + [s[-1]]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("profile")
    for name in ("store", "keys"):
        ap.add_argument(f"--{name}", required=True)
    for name in ("pairs", "sites", "from", "to"):
        ap.add_argument(f"--{name}", type=int, required=True)
    a = ap.parse_args()
    regions = []

    class Tally(cf.census.Tally):
        def take(self, region):
            super().take(region)
            if self.live:
                _, n, resolved, _ = region
                regions.append((n, popcount(resolved)))

    state = {"k": 0}
    init = Tally.__init__

    def tinit(self):
        init(self)
        self.live = a.__dict__["from"] <= state["k"] < a.to
        state["k"] += 1

    Tally.__init__ = tinit
    cf.census.Tally = Tally
    out = sys.stdout
    sys.stdout = open(os.devnull, "w")
    cf.census.store(argparse.Namespace(store=a.store, role="prefix", keys=a.keys, pairs=a.pairs, sites=a.sites, sections=a.to, slice=None))
    sys.stdout = out
    sites = [n for n, _ in regions]
    dense = [n * n for n, _ in regions]
    stride = [n * (2 * (NEAR - 1) + d) for n, d in regions]
    print(f"REGIONS count={len(regions)} sections={a.to - a.__dict__['from']} (every clock: a region's sites are its own at each of the 4 ticks)")
    print(f"(a) SITES_A_REGION q50,q90,q99,max={quantiles(sites)}")
    print(f"(a) DENSE_PAIRS_A_REGION q50,q90,q99,max={quantiles(dense)}  SUPPORT_STRIDE_ENTRIES_A_REGION q50,q90,q99,max={quantiles(stride)}")
    print("(a) MET_PAIRS_A_REGION_BY_CLOCK owed (the census holds no tick's classes; the profiled read's met pairs a tick are 4,566,615,773 over 4 ticks and 4 heads)")
    total_pairs = sum(stride)
    for name, rows in CHOICES.items():
        for width, idx in (("today", 0), ("proved", 1)):
            per_site = sum(ROWS[r][idx] for r in rows)
            octs = [n * per_site for n in sites]
            fit = [o + ROWS_OWN <= SHARED_SM for o in octs]
            share_r = sum(fit) / len(fit)
            share_p = sum(s for s, f in zip(stride, fit) if f) / total_pairs
            print(f"(b) ROWS choice={name} width={width} octets_a_site_a_head={per_site:.0f} region_rows_octets q50,q90,q99,max={[round(x) for x in quantiles(octs)]} "
                  f"fit_with_the_entrys_own_{ROWS_OWN}_in_{SHARED_SM} regions={share_r:.3f} support_entries={share_p:.3f}")
    print(f"(b) SHARED driver MAX_SHARED_MEMORY_PER_MULTIPROCESSOR={SHARED_SM} MAX_SHARED_MEMORY_PER_BLOCK=49152 field_contact_rows_own={ROWS_OWN} field_yard_rows_own=10912")
    # (d) the floors, ms over the read's sections: the pair records as layout 2's; the source rows once a region a fused launch (in order), and the
    # crowds' arrays and the difference arrays held in the block (none through the card's memory) under layout 4.
    pairs, kinds = {}, {}
    for line in open(a.profile):
        if line.startswith("FIELD_PROFILE_PAIRS "):
            kv = dict(w.split("=", 1) for w in line.split()[1:])
            pairs[int(kv["head"])], kinds[int(kv["head"])] = int(kv["pairs"]), kv["kind"]
    allp = sum(pairs.values())
    paced = sum(p for h, p in pairs.items() if kinds[h] == "paced")
    ticks_rows_heads = sum(sites) * cf.TICKS * len(pairs)
    paced_rows = sum(sites) * cf.TICKS * sum(1 for h in pairs if kinds[h] == "paced")
    fwd_rows = ticks_rows_heads * (64 + 64 + 128)  # key rows, probe rows, value rows once a region (the forward)
    ret_rows = ticks_rows_heads * (128 * 4)  # value, word, probe and covector rows once a region (the return, the columns' transpose included)
    out_rows = ticks_rows_heads * (128 + 128 * 3)  # y forward; dp, dq, dv written
    fwd_rec = allp * 16 + paced * 32  # e and sb written, skins written
    ret_rec = allp * (16 + 8 + 8) + paced * 32  # e and sb read, ds written and read by the columns, skins read
    clock = paced_rows * (8 + 192)  # sigma and the site addresses, the fill's
    floor = 1000 * (fwd_rows + ret_rows + out_rows + fwd_rec + ret_rec + clock) / cf.ORDER
    print(f"(d) FLOOR layout=4 forward_rows_GB={fwd_rows / 1e9:.1f} return_rows_GB={ret_rows / 1e9:.1f} outputs_GB={out_rows / 1e9:.1f} records_GB={(fwd_rec + ret_rec) / 1e9:.1f} clock_GB={clock / 1e9:.1f} family_ms={floor:.0f}")
    print("(d) FLOOR beside: layout 1 3,733 ms, layout 2 2,754 ms, today 12,932 ms (p53_pair_layout_forecast.txt), the read's 100 sections")
    # (c) The regions whose rows do not fit: their rows left in the card's memory as a per-region copy in the support's order (a source's row once a
    # pair that meets it), written once a tick and read once; the met pairs of those regions taken at their share of the support stride.
    for name, rows in CHOICES.items():
        for width, idx in (("today", 0), ("proved", 1)):
            per_site = sum(ROWS[r][idx] for r in rows)
            miss = sum(st for (n, _), st in zip(regions, stride) if n * per_site + ROWS_OWN > SHARED_SM) / total_pairs
            met = miss * allp
            copy = met * per_site
            print(f"(c) NOT_FITTING choice={name} width={width} support_share={miss:.3f} met_pairs={met:.0f} copy_octets={copy:.0f} floor_ms={1000 * 2 * copy / cf.ORDER:.0f} (written and read once, in order)")
    print("(e) LAUNCHES today 509 a section, the family's 80 (exposure 4, l5/l6 4, rows 16, columns 16, skin back 8, spread 16, skin fill 8, sums 4, classes 4): 0.157")
    print("(e) LAUNCHES layout 4: the forward one a tick (4) and the return one a tick (4), with sums and classes in the forward's block: 8 a section, 0.016 of 509")
    print("(f) DEPENDENCY forward: the contact's carrier (its limbs) is chosen by the host from the batch's widest row (tick.bits[1], an atomicMax over every region) between the exposure and the contact: one launch needs the carrier chosen per region on the card (any carrier at least the row's keeps the bits)")
    print("(f) DEPENDENCY return: the temperature's covector (gcov, an atomic into the material over every region) stays a global atomic; the skin's return gsig and the difference arrays cv, cw, the crowds' prefix rows sw, sv, sc and the probers' lists stay inside the region")
    print("(f) DEPENDENCY across ticks: a tick's blank clock reads the faces of every head after the site maps, outside the family, so a tick keeps the maps' launches between its forward and the next tick's")


if __name__ == "__main__":
    main()
