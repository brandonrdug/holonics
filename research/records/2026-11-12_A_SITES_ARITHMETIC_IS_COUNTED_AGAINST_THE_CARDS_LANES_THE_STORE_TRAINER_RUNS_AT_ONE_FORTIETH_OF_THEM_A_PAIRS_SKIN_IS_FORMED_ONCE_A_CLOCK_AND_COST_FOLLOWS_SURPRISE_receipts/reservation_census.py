#!/usr/bin/env python3
"""A ruler (P51, the engine's step 1): the batch reservation of each section of the store's pass, with the clock's skins at the row's support stride.

The pass's sections are cut by the passage record's own port of the trainer's cut (`store_stretch_census.py`, whose section lines the trainer's are
held to). A region of S sites, D of them definite, reserves

    pair S^2 + site S + region                    (read_octets for a return: the coefficients `field_pass reserve` prints from the declaration)
  + entry S (near_slots + D) + crowd_site S       (skin_octets: the clock's skins, K = NEAR_SLOTS + D entries a row, and the crowd edges)

and a section is one batch where its regions' sum stays within the cut (four fifths of the batch budget less the exponential's face, as the run's
FIELD_SKIN line prints it). Prints, over the sections [FROM, TO) of the pass: one line a section (its regions, sites, squared, open, the support
entries E2, the reservation without and with the skins) and the count that would pass the cut, beside the dense address's for comparison.
Numbers only: no path, no text, no key.

  python3 -I reservation_census.py --store DIR --role prefix --keys K --pairs P --sites S --from F --to T \
      --pair 280 --site 77246 --region 26064 --entry 64 --crowd-site 1280 --near-slots 10 --cut CUT [--lines]
"""
import argparse
import glob
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
passage = glob.glob(os.path.join(here, "..", "2026-11-12_THE_PASSAGE_WIDENS_TO_FIVE_REGISTERS*_receipts"))
if len(passage) != 1:
    sys.exit("the passage record's receipts are owed beside this one")
sys.path.insert(0, passage[0])
import store_stretch_census as census  # noqa: E402
from section_regions_census import popcount  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    for name in ("store", "keys"):
        ap.add_argument(f"--{name}", required=True)
    ap.add_argument("--role", default="prefix")
    for name in ("pairs", "sites", "from", "to", "pair", "site", "region", "entry", "crowd-site", "near-slots", "cut"):
        ap.add_argument(f"--{name}", type=int, required=True)
    ap.add_argument("--lines", action="store_true")
    a = ap.parse_args()
    rows = []

    class Tally(census.Tally):
        def __init__(self):
            super().__init__()
            self.entries = 0

        def take(self, region):
            super().take(region)
            _, n, resolved, _ = region
            self.entries += n * (a.near_slots + popcount(resolved))

        def text(self):
            base = a.pair * self.squared + a.site * self.sites + a.region * self.regions
            skins = a.entry * self.entries + a.crowd_site * self.sites
            dense = a.entry * self.squared + a.crowd_site * self.sites
            rows.append((self.regions, self.sites, self.squared, self.open, self.entries, base, base + skins, base + dense))
            return super().text() + f" entries={self.entries} reserve_base={base} reserve_support={base + skins} reserve_dense={base + dense}"

    census.Tally = Tally
    args = argparse.Namespace(store=a.store, role=a.role, keys=a.keys, pairs=a.pairs, sites=a.sites, sections=a.to, slice=None)
    out = sys.stdout
    sys.stdout = open(os.devnull, "w") if not a.lines else out
    census.store(args)
    sys.stdout = out
    span = rows[a.__dict__["from"]:a.to]
    over_support = sum(1 for r in span if r[6] > a.cut)
    over_dense = sum(1 for r in span if r[7] > a.cut)
    print(f"RESERVATION sections={len(span)} from={a.__dict__['from']} to={a.to} cut={a.cut} "
          f"max_base={max(r[5] for r in span)} max_support={max(r[6] for r in span)} max_dense={max(r[7] for r in span)} "
          f"over_cut_support={over_support} over_cut_dense={over_dense} "
          f"entries_sum={sum(r[4] for r in span)} squared_sum={sum(r[2] for r in span)} "
          f"entries_share_ppm={1_000_000 * sum(r[4] for r in span) // max(sum(r[2] for r in span), 1)}")


if __name__ == "__main__":
    main()
