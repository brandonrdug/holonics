#!/usr/bin/env python3
"""A ruler, and the reference port of a cut: a document store read by keyed stretches, one keyed state a stretch.

The cut (the record of November 12 on the opening's room, section 4; agent-inferred, not built when this was written).
`seed` is the key file's last eight bytes read big-endian, as `train-field` reads it; `mix` is its mixer.

  A piece's places. A piece of a slice's index (`tools/corpus_passage.py`: document, title_octets, text_octets, opens,
  closes) is read as its title's bytes, one line feed where it opens with a title, and its text's bytes: L places.

  A stretch, the d-th of the pass (d counts from 1 over every slice). Two draws on octaves:
    context q = (4 << oq) + mix(seed, d | 3 << 60) % (4 << oq),  oq = mix(seed, d | 1 << 60) % OCTAVES
    run     a = (4 << oa) + mix(seed, d | 5 << 60) % (4 << oa),  oa = mix(seed, d | 1 << 62) % OCTAVES
  so each is uniform over the octaves [4, 8) to [256, 512) and uniform within its octave. With `rest` places left in
  the piece from its cursor: where rest - (q + a) is at least 4 (the least context) the stretch is the next q + a
  places and the piece goes on; else it takes the rest (context min(q, rest - 1), the run the others), the piece is
  done, and where the piece closes its document NEAR void places follow the run (the near tail). A stretch cut by its
  draw, or by a piece that does not close, ends at its last place with no void.

  Its one state, from head = mix(seed, d): bit 17 set, the writer's state; clear, a mask state.
    mask: `shape`'s law on the stretch's sites n: u = ((head >> 1) & 0xFFFF) + 1, tau = max(u*u >> 16, 1), over the
      whole stretch where head & 1 and past the context otherwise; a site t open where
      mix(seed, d ^ (t + 1) << 32) & 0xFFFF < tau, one keyed site where none; weighed domain isqrt(4 m K).
    writer: `writer_region`'s law: the context known, the run's places in octave order of their distance from the
      context (key = mix(seed, d | 7 << 61), keyed within an octave), the first k resolved, k by octaves of reads
      (o = key % (bits(a - 1) + 1); k = 0 at o = 0, else in [2^(o-1), min(2^o - 1, a - 1)] by mix(seed, d | 15 << 60));
      a true end's voids given; every open place compared on its class at weight one.

  The slices' interleave. The next stretch comes from the slice, among those with a piece left, whose places taken
  stand least against its quota (taken_s * quota_t < taken_t * quota_s; the earlier slice at a tie), the quota the
  role's store octets.

  A section. Stretches in order while the regions' sum of sites squared stays within PAIRS and their sum of sites
  within SITES; the stretch that would pass either opens the next section.

What it prints. `--draw N`: N stretches of a piece with no end, the cut's means and its price at the code line's own
fitted rates. `--bound OCTETS`: the two bounds a reservation gives at a declaration's octets a pair and a site.
`--store DIR --role prefix --keys K --sections M`: the first M sections of the pass over a store, one line a section
(regions, sites, domain, sites squared, open rows' pairs, by kind), which the trainer's own lines are held to.
Numbers only: no path, no text, no key.

  python3 -I store_stretch_census.py --draw 100000
  python3 -I store_stretch_census.py --store DIR --role prefix --keys KEYS --sections 64 --pairs P --sites S
"""
import argparse
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from section_regions_census import NEAR, bits_of, first_k, mix, pairs_of, popcount  # noqa: E402

M64 = (1 << 64) - 1
OCTAVES = 7
LEAST = 4
SLICES = ("code", "web", "science", "books", "wikidata")
INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"
# The code line's fitted rates (te7's own 1,535 sections, CENSUS_FIT): ms a computed site, ms a pair over a read.
SITE_MS, PAIR_MS, HEAD_TICKS = 0.00874612, 3.7474e-06, 16


def lengths_of(seed, d):
    oq = mix(seed, d | (1 << 60)) % OCTAVES
    q = (LEAST << oq) + mix(seed, d | (3 << 60)) % (LEAST << oq)
    oa = mix(seed, d | (1 << 62)) % OCTAVES
    a = (LEAST << oa) + mix(seed, d | (5 << 60)) % (LEAST << oa)
    return q, a


def cut_of(seed, d, rest, closes):
    """The stretch at a cursor with `rest` places left: (context, run, whether a true end follows, whether the piece is done)."""
    q, a = lengths_of(seed, d)
    if rest - (q + a) >= LEAST:
        return q, a, False, False
    q = min(q, rest - 1)
    return q, rest - q, closes, True


def state_of(seed, d, q, a, ends):
    """The stretch's one keyed state as the ruler keeps a region: (kind, sites, resolved bitset, the sites its line counts)."""
    n = q + a + (NEAR if ends else 0)
    head = mix(seed, d)
    if (head >> 17) & 1:
        key = mix(seed, d | (7 << 61))
        most = a - 1
        o = key % (most.bit_length() + 1)
        k = 0
        if o:
            low = 1 << (o - 1)
            high = min((1 << o) - 1, most)
            k = low + mix(seed, d | (15 << 60)) % (high - low + 1)
        full, extras, _ = first_k(key, q, a, k)
        resolved = bits_of(q, full, extras) | (((1 << n) - 1) & ~((1 << (q + a)) - 1))
        return "writer", n, resolved, a - k
    u = ((head >> 1) & 0xFFFF) + 1
    tau = max((u * u) >> 16, 1)
    whole = head & 1 == 1
    frm = 0 if whole else q
    opened = 0
    for t in range(frm, n):
        if (mix(seed, d ^ ((t + 1) << 32)) & 0xFFFF) < tau:
            opened |= 1 << t
    if opened == 0:
        opened = 1 << (frm + mix(seed, (d + 1) & M64) % (n - frm))
    m = n - frm
    return ("mask_whole" if whole else "mask_run"), n, ((1 << n) - 1) & ~opened, math.isqrt(4 * m * popcount(opened))


class Tally:
    FIELDS = ("regions", "sites", "domain", "squared", "open", "pairs_open", "pairs_near")

    def __init__(self):
        for f in self.FIELDS:
            setattr(self, f, 0)

    def take(self, region):
        _, n, resolved, counted = region
        open_pairs, near, _, definite = pairs_of(n, resolved)
        self.regions += 1
        self.sites += n
        self.domain += counted
        self.squared += n * n
        self.open += n - definite
        self.pairs_open += open_pairs
        self.pairs_near += near

    def text(self):
        return " ".join(f"{f}={getattr(self, f)}" for f in self.FIELDS)


def moments():
    """The draw's law of a stretch with no end, n = q + a: the sums of n and of n squared over the law's common
    denominator, so the cut's mean pairs of sites a site is a ratio of two integers."""
    lows = [LEAST << o for o in range(OCTAVES)]
    den = math.lcm(*lows) * OCTAVES
    s1 = sum((den // (OCTAVES * low)) * v for low in lows for v in range(low, 2 * low))
    s2 = sum((den // (OCTAVES * low)) * v * v for low in lows for v in range(low, 2 * low))
    # E[n] = 2 s1/den,  E[n^2] = 2 s2/den + 2 (s1/den)^2
    return 2 * s1 * den, 2 * s2 * den + 2 * s1 * s1, den * den


def bounds(octets, pair_octets, site_octets):
    """The section's two bounds a reservation of `octets` gives: SITES the most with SITES * (site_octets + pair_octets * rho)
    within it, rho the cut's mean pairs of sites a site, and PAIRS = floor(rho * SITES)."""
    n1, n2, _ = moments()
    sites = octets * n1 // (site_octets * n1 + pair_octets * n2)
    return sites * n2 // n1, sites


def draw(count, seed, pairs_bound, sites_bound):
    kinds, lap, sections, in_pairs, in_sites = {}, Tally(), 0, 0, 0
    for d in range(1, count + 1):
        q, a, ends, _ = cut_of(seed, d, 1 << 40, False)
        region = state_of(seed, d, q, a, ends)
        kinds.setdefault(region[0], Tally()).take(region)
        lap.take(region)
        n = region[1]
        if in_sites and (in_pairs + n * n > pairs_bound or in_sites + n > sites_bound):
            sections, in_pairs, in_sites = sections + 1, 0, 0
        in_pairs, in_sites = in_pairs + n * n, in_sites + n
    n1, n2, den = moments()
    print(f"STRETCH_LAW octaves={OCTAVES} least={LEAST} mean_sites_millis={1000 * n1 // den} mean_squared={n2 // den} pairs_a_site_millis={1000 * n2 // n1}")
    for kind in sorted(kinds):
        print(f"STRETCH_KIND kind={kind} {kinds[kind].text()}")
    least = lap.pairs_open + lap.pairs_near
    site_us = 1000 * SITE_MS
    pair_us = 1000 * PAIR_MS * HEAD_TICKS * least / lap.sites
    print(f"STRETCH_DRAW stretches={count} {lap.text()} mean_sites_millis={1000 * lap.sites // lap.regions} mean_squared={lap.squared // lap.regions} "
          f"open_ppm={1_000_000 * lap.open // lap.sites} pairs_least_a_site_millis={1000 * least // lap.sites}")
    print(f"STRETCH_PRICE at_the_code_lines_rates site_us={site_us:.3f} pairs_us={pair_us:.3f} sum_us={site_us + pair_us:.3f} "
          f"bytes_a_second={int(1e6 / (site_us + pair_us))}")
    print(f"STRETCH_SECTIONS pairs_bound={pairs_bound} sites_bound={sites_bound} sections={sections} regions_a_section_millis={1000 * lap.regions // max(sections, 1)} "
          f"sites_a_section={lap.sites // max(sections, 1)}")


def pieces_of(store, role, name, count):
    stem = "HELD" if role == "held" else "DOCS"
    with open(os.path.join(store, f"{stem}_{name}.tsv")) as f:
        if f.readline() != INDEX_HEAD:
            sys.exit("an index that does not open with its head")
        out = []
        for line in f:
            if len(out) == count:
                break
            _, title, text, opens, closes = (int(x) for x in line.split("\t"))
            out.append((title + (1 if opens and title else 0) + text, bool(closes)))
    if len(out) != count:
        sys.exit("an index shorter than its role's pieces")
    return out


def store(args):
    with open(args.keys, "rb") as f:
        seed = int.from_bytes(f.read()[-8:], "big")
    roles = {}
    with open(os.path.join(args.store, "STORE.tsv")) as f:
        f.readline()
        for line in f:
            role, name, _, _, _, count, _, octets, _ = line.rstrip("\n").split("\t")
            roles[(role, name)] = (int(count), int(octets))
    names = [n for n in SLICES if (args.role, n) in roles]
    pieces = {n: pieces_of(args.store, args.role, n, roles[(args.role, n)][0]) for n in names}
    quota = {n: roles[(args.role, n)][1] for n in names}
    at = {n: [0, 0] for n in names}  # the piece and the cursor in it
    taken = dict.fromkeys(names, 0)
    d, section, tally, by_slice, in_pairs, in_sites = 0, 0, Tally(), dict.fromkeys(names, 0), 0, 0

    def close(through):
        print(f"STORE_SECTION n={section} {tally.text()} " + " ".join(f"{n}={by_slice[n]}" for n in names) + f" stretches={through}")

    while section < args.sections:
        live = [n for n in names if at[n][0] < len(pieces[n])]
        if not live:
            # The pass's last section, where the store ends inside it.
            if tally.regions:
                close(d)
                section += 1
            break
        name = live[0]
        for other in live[1:]:
            if taken[other] * quota[name] < taken[name] * quota[other]:
                name = other
        places, closes = pieces[name][at[name][0]]
        d += 1
        q, a, ends, done = cut_of(seed, d, places - at[name][1], closes)
        region = state_of(seed, d, q, a, ends)
        n = region[1]
        if in_sites and (in_pairs + n * n > args.pairs or in_sites + n > args.sites):
            close(d - 1)
            section, tally, by_slice, in_pairs, in_sites = section + 1, Tally(), dict.fromkeys(names, 0), 0, 0
            if section == args.sections:
                d -= 1
                break
        tally.take(region)
        by_slice[name] += 1
        in_pairs, in_sites = in_pairs + n * n, in_sites + n
        taken[name] += q + a
        at[name] = [at[name][0] + 1, 0] if done else [at[name][0], at[name][1] + q + a]
    print(f"STORE_PASS role={args.role} sections={section} stretches_read={d} " + " ".join(f"{n}_pieces={at[n][0]}" for n in names))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--draw", type=int)
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=1)
    ap.add_argument("--bound", type=int, help="a reservation in octets: prints the two bounds it gives")
    ap.add_argument("--pair-octets", type=int, default=280)
    ap.add_argument("--site-octets", type=int, default=71486)
    ap.add_argument("--pairs", type=int)
    ap.add_argument("--sites", type=int)
    ap.add_argument("--store")
    ap.add_argument("--role", default="prefix")
    ap.add_argument("--keys")
    ap.add_argument("--sections", type=int, default=64)
    args = ap.parse_args()
    if args.bound is not None:
        pairs, sites = bounds(args.bound, args.pair_octets, args.site_octets)
        print(f"STRETCH_BOUND octets={args.bound} pair_octets={args.pair_octets} site_octets={args.site_octets} pairs={pairs} sites={sites}")
        args.pairs = pairs if args.pairs is None else args.pairs
        args.sites = sites if args.sites is None else args.sites
    if args.pairs is None or args.sites is None:
        sys.exit("the section's bounds: --pairs and --sites, or --bound")
    if args.draw:
        draw(args.draw, args.seed, args.pairs, args.sites)
    if args.store:
        store(args)


if __name__ == "__main__":
    main()
