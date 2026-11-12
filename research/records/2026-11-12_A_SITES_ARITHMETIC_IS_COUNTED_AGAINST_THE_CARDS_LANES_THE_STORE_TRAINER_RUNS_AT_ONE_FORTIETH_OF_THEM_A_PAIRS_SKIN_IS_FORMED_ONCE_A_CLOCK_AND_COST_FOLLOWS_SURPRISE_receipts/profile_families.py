#!/usr/bin/env python3
"""A ruler on the host: a profiled read's kernel time by family of entry, beside the count's products.

Usage: python3 profile_families.py PROFILE COUNT

PROFILE is a train-store log with FIELD_PROFILE entry lines and its FIELD_CARD line; COUNT is engine_count.py's
output for the same trainer (its table's rows by family). An entry belongs to the first family whose pattern it
matches. Prints, a family: its milliseconds a section, its share of the kernels' time, the count's products a
section [agent-inferred], the products a second that makes, and the card's lane-steps a product at the published
ceiling of 10,240 lanes at 2.55 GHz [from training].
"""
import re
import sys

FAMILIES = [
    ("contact", r"field_(contact_|exposure|pace_skin_back|spread|sums|classes)"),
    ("moments and clocks", r"field_(moment_|pace_|paces|pframes|skin_addresses)"),
    ("site maps", r"field_(affine|outer|transposed)"),
    ("blank clocks", r"field_blank_"),
    ("faces", r"field_(face|tied_|encoding|exponential|open)"),
    ("carry circles", r"field_pair"),
    ("site kernels, small", r"field_"),
]
COUNT_OF = {
    "contact": ["contact, forward", "contact, return", "crowds"],
    "moments and clocks": ["moments"],
    "site maps": ["site maps, forward", "site maps, return"],
    "blank clocks": ["blank clocks"],
    "faces": ["face and its return"],
    "carry circles": [],
    "site kernels, small": ["site kernels, small"],
}


def main():
    profile, count = sys.argv[1], sys.argv[2]
    lane_steps = 10240 * 2.55e9
    ms = {name: 0.0 for name, _ in FAMILIES}
    launches = {name: 0 for name, _ in FAMILIES}
    returns = None
    for line in open(profile):
        if line.startswith("FIELD_CARD"):
            returns = int(re.search(r"returns=(\d+)", line).group(1))
        m = re.match(r"FIELD_PROFILE entry=(\w+) launches=(\d+) ms=(\d+)", line)
        if m:
            for name, pattern in FAMILIES:
                if re.match(pattern, m.group(1)):
                    ms[name] += int(m.group(3))
                    launches[name] += int(m.group(2))
                    break
    products = {}
    for line in open(count):
        cells = [c.strip() for c in line.split("|")]
        if len(cells) == 6 and cells[0] != "family":
            products[cells[0]] = float(cells[4])
    total = sum(ms.values())
    print(f"PROFILE_FAMILIES sections={returns} kernels_ms_a_section={total / returns:.1f}")
    print("family | ms a section | share of kernels | launches a section | counted products a section | products a second | lane-steps a product")
    for name, _ in FAMILIES:
        p = sum(products.get(k, 0.0) for k in COUNT_OF[name])
        a_section = ms[name] / returns
        rate = p / (a_section / 1e3) if p else 0.0
        steps = lane_steps / rate if rate else 0.0
        print(f"{name} | {a_section:.1f} | {ms[name] / total:.3f} | {launches[name] / returns:.0f} | {p:.4g} | {rate:.4g} | {steps:.0f}")


if __name__ == "__main__":
    main()
