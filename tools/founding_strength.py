#!/usr/bin/env python3 -I
"""founding_strength.py DECLARATION: what each founding of a line bought, per entry it founded, by region (U4 of the Einstein record).

The Einstein record's section 5.6 and its order U4: a founding buys held code at the price of the free data it adds, and its strength
is the first over the second, read by region. This ruler lists every founding its declaration names, with the nats it bought on the
held passage and the entries it founded, and ranks the foundings that were read alike. Reason for reading by region and never one
total: bits read as progress is a recorded failure, and a whole-field mean hides where the field learns (CLAUDE.md, a reading names
its region).

The declaration is tab-separated, one read a row, '#' starting a comment:

  founding  laps  read  region  entries  arm  control  places

- laps: the laps trained since the founding (`2+3` for a mean of the end states of the founding's second and third laps).
- read: `end` (a lap's end state, one draw of the deposit's standing spread), `mean` (the lap's mean of states) or `mean2` (a mean of
  two lap ends, which leaves half a spread in). Rows are ranked only against rows of the same laps, read and region.
- region: `all` (the whole held passage) or `q1` to `q4` (a quarter of open sites, quarter 1 the fewest open).
- entries: the entries the founding added, signed terms `+SOURCE` or `-SOURCE` joined by ` ; `.
- arm, control: the held code, nats a place, of the founded line's state and of its control's, each a SOURCE.
- places: the region's places, a SOURCE.

A SOURCE is `path::anchor::key` or `path::anchor::key::N`, `path` from the repository's root. The line read is the first that matches
the regular expression `anchor`, or, when `key` is `NAME` or `PREFIX.NAME`, the first line from that one on that holds `NAME=` (and
`PREFIX`); the figure is the token after `NAME=`, its `N`th slash-separated part when `N` is given. `key` may instead be `tok:N` (the
anchor line's whitespace token N, from 0) or `col:N` (cell N of a Markdown table row, from 1). Every figure is read from a committed
receipt or record; the declaration holds none.

Printed for each row: bought = control - arm (nats a place), nats = bought x places (nats on that region of the held passage), and
strength = nats / entries (nats a founded entry). A lap's quarters are checked to partition its places, and their nats are summed
beside the whole; a founding read only whole says so. Integers and rationals only (`fractions`).

A ruler (CLAUDE.md, a ruler is an instrument): it reads text, opens no state, trains nothing, and is never machinery. Its controls
are tools/test_founding_strength.py (gate 1).
"""
import re
import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGIONS = ("all", "q1", "q2", "q3", "q4")
READS = ("end", "mean", "mean2")


def decimal(x, digits):
    """x at `digits` decimals, rounded half away from zero."""
    scale = 10 ** digits
    n = abs(x) * scale
    q = int(n)
    if n - q >= Fraction(1, 2):
        q += 1
    sign = "-" if x < 0 and q else ""
    whole, frac = divmod(q, scale)
    return f"{sign}{whole}.{frac:0{digits}d}" if digits else f"{sign}{whole}"


def figure(source):
    """The figure a SOURCE names and the line it was read from."""
    parts = source.split("::")
    if len(parts) not in (3, 4):
        sys.exit(f"a source is path::anchor::key[::N]: {source}")
    path, anchor, key = parts[:3]
    lines = (ROOT / path).read_text().splitlines()
    pattern = re.compile(anchor)
    start = next((i for i, line in enumerate(lines) if pattern.search(line)), None)
    if start is None:
        sys.exit(f"no line matches {anchor!r} in {path}")
    at = start
    if key.startswith("tok:"):
        value = lines[at].split()[int(key[4:])]
    elif key.startswith("col:"):
        value = [c.strip() for c in lines[at].strip().strip("|").split("|")][int(key[4:]) - 1]
    else:
        prefix, _, name = key.rpartition(".")
        mark = name + "="
        at = next((i for i in range(start, len(lines)) if mark in lines[i] and prefix in lines[i]), None)
        if at is None:
            sys.exit(f"no {key}= at or after {anchor!r} in {path}")
        value = lines[at].split(mark, 1)[1].split()[0]
    if len(parts) == 4:
        value = value.split("/")[int(parts[3]) - 1]
    try:
        return Fraction(value.replace(",", "")), f"{path.rsplit('/', 1)[-1]}:{at + 1}"
    except ValueError:
        sys.exit(f"{value!r} at {path}:{at + 1} is not a figure ({source})")


def entries_of(terms):
    total, where = 0, []
    for term in terms.split(" ; "):
        sign, source = term[0], term[1:]
        if sign not in "+-":
            sys.exit(f"an entries term starts + or -: {term}")
        value, at = figure(source)
        if value.denominator != 1:
            sys.exit(f"a count that is not whole: {value} at {at}")
        total += int(value) if sign == "+" else -int(value)
        where.append(f"{sign}{int(value)}@{at}")
    return total, where


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    rows = []
    for number, raw in enumerate(Path(sys.argv[1]).read_text().splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        cells = raw.split("\t")
        if len(cells) != 8:
            sys.exit(f"line {number}: eight tab-separated cells, read {len(cells)}")
        founding, laps, read, region, entries, arm, control, places = cells
        if read not in READS or region not in REGIONS:
            sys.exit(f"line {number}: read in {READS}, region in {REGIONS}")
        count, count_at = entries_of(entries)
        if count <= 0:
            sys.exit(f"line {number}: a founding adds entries ({count})")
        a, a_at = figure(arm)
        c, c_at = figure(control)
        p, p_at = figure(places)
        if p.denominator != 1 or p <= 0:
            sys.exit(f"line {number}: places {p}")
        bought = c - a
        nats = bought * p
        rows.append(dict(founding=founding, laps=laps, read=read, region=region, entries=count, places=int(p), arm=a, control=c,
                         bought=bought, nats=nats, strength=nats / count,
                         at=f"entries {' '.join(count_at)}; arm {a_at}; control {c_at}; places {p_at}"))

    print("# founding_strength.py: nats bought a place (control less arm), nats on the region, nats a founded entry")
    for r in rows:
        print(f"FOUNDING_STRENGTH founding={r['founding']} laps={r['laps']} read={r['read']} region={r['region']} "
              f"places={r['places']} entries={r['entries']} arm={decimal(r['arm'], 6)} control={decimal(r['control'], 6)} "
              f"bought={decimal(r['bought'], 6)} nats={decimal(r['nats'], 2)} strength={decimal(r['strength'], 6)}")
        print(f"  from {r['at']}")

    groups = defaultdict(dict)
    for r in rows:
        key = (r["founding"], r["laps"], r["read"])
        if r["region"] in groups[key]:
            sys.exit(f"two rows for {key} {r['region']}")
        groups[key][r["region"]] = r
    print("# the partition: a lap's quarters against its whole")
    for (founding, laps, read), regions in groups.items():
        quarters = [regions.get(q) for q in REGIONS[1:]]
        whole = regions.get("all")
        if not any(quarters):
            print(f"FOUNDING_PARTITION founding={founding} laps={laps} read={read} quarters=unread (read whole only)")
            continue
        if not all(quarters):
            sys.exit(f"{founding} {laps} {read}: some quarters read, not all four")
        places = sum(q["places"] for q in quarters)
        nats = sum(q["nats"] for q in quarters)
        line = (f"FOUNDING_PARTITION founding={founding} laps={laps} read={read} quarter_places={places} "
                f"quarter_nats={'/'.join(decimal(q['nats'], 2) for q in quarters)} sum={decimal(nats, 2)} "
                f"strength_by_quarter={'/'.join(decimal(q['strength'], 6) for q in quarters)}")
        if whole:
            if places != whole["places"]:
                sys.exit(f"{founding} {laps} {read}: the quarters hold {places} places, the whole {whole['places']}")
            line += f" whole={decimal(whole['nats'], 2)} whole_less_sum={decimal(whole['nats'] - nats, 2)}"
        print(line)

    print("# ranks: foundings read alike (same laps, read and region), strongest first")
    alike = defaultdict(list)
    for r in rows:
        alike[(r["laps"], r["read"], r["region"])].append(r)
    for (laps, read, region), group in alike.items():
        if len({r["founding"] for r in group}) < 2:
            continue
        group.sort(key=lambda r: r["strength"], reverse=True)
        ranked = " > ".join(f"{r['founding']} {decimal(r['strength'], 6)}" for r in group)
        print(f"FOUNDING_RANK laps={laps} read={read} region={region} {ranked}")


if __name__ == "__main__":
    main()
