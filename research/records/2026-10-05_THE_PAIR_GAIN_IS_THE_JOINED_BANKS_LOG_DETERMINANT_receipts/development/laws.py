#!/usr/bin/env python3
"""Read `executed pair-members` listings and decide each station along the target's trajectory under
several joint readings of the bank's members (a development diagnostic, never a law).

Each member's growth is read at its 1/16 cell's lower end, exactly (Fraction). Laws, for the
candidate's pair storage p_m and its column alone a_m on the bank's members m:
  least    min_m p_m / a_m                        (lane C's law)
  joint    max_m p_m / max_m a_m                  (the joint growths' ratio)
  energy   sum_m p_m^2 / sum_m a_m^2              (a ratio of the joint quadratic forms, unit seed per member)
  product  prod_m p_m / a_m                       (the direct sum's log det)
A station is decided right when the target's value strictly exceeds every other class's.
usage: laws.py <listing>...
"""
import re
import sys
from fractions import Fraction

CELL = re.compile(r'"\[(\d+)/16, \d+/16\)"')


def members(text):
    return [Fraction(int(k), 16) for k in CELL.findall(text)]


def laws(p, a):
    out = {}
    out["least"] = min(x / y for x, y in zip(p, a))
    out["joint"] = max(p) / max(a)
    out["energy"] = sum(x * x for x in p) / sum(y * y for y in a)
    prod = Fraction(1)
    for x, y in zip(p, a):
        prod *= x / y
    out["product"] = prod
    return out


def main(paths):
    names = ["least", "joint", "energy", "product"]
    for path in paths:
        right = {n: 0 for n in names}
        stations = 0
        target = None
        station = None
        rows = {}

        def close():
            nonlocal stations
            if station is None or not rows:
                return
            stations += 1
            want = target[station]
            for n in names:
                values = {c: v[n] for c, v in rows.items()}
                if want in values and all(values[want] > v for c, v in values.items() if c != want):
                    right[n] += 1

        for line in open(path, encoding="utf-8"):
            head = re.match(r"request tail .* \| target \[([^\]]*)\]", line)
            if head:
                close()
                target = [int(x) for x in head.group(1).split(", ")]
                station, rows = None, {}
                continue
            st = re.match(r"\s+station (\d+):", line)
            if st:
                close()
                station, rows = int(st.group(1)), {}
                continue
            cl = re.match(r"\s+class (\d+): pair \[(.*)\] alone \[(.*)\] ", line)
            if cl:
                p, a = members(cl.group(2)), members(cl.group(3))
                if any(y == 0 for y in a):
                    continue
                rows[int(cl.group(1))] = laws(p, a)
        close()
        print(f"{path}: stations {stations}; decided right along the target's trajectory: "
              + ", ".join(f"{n} {right[n]}" for n in names))


if __name__ == "__main__":
    main(sys.argv[1:])
