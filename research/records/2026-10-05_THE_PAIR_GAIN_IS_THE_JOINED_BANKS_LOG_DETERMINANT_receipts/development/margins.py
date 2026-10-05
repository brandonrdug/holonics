#!/usr/bin/env python3
"""For each law of laws.py: the stations decided wrong and what won (the antecedent's copy or
another class; delta 2, read from the request's last two cells), and the narrowest ratio of the
target's value over the runner-up's among the stations decided right. Development diagnostic."""
import re, sys
from fractions import Fraction
from laws import members, laws
names = ["least", "joint", "energy", "product"]
for path in sys.argv[1:]:
    wrong = {n: {"copy": 0, "other": 0} for n in names}
    narrow = {n: None for n in names}
    tail = target = station = None
    rows = {}
    def close():
        if station is None or not rows:
            return
        passage = tail + target
        antecedent = passage[2 + station - 2]
        want = target[station]
        for n in names:
            vals = {c: v[n] for c, v in rows.items()}
            best = max(vals, key=lambda c: vals[c])
            if best != want or any(vals[c] == vals[want] for c in vals if c != want):
                wrong[n]["copy" if best == antecedent else "other"] += 1
            else:
                runner = max(v for c, v in vals.items() if c != want)
                r = vals[want] / runner
                narrow[n] = r if narrow[n] is None else min(narrow[n], r)
    for line in open(path, encoding="utf-8"):
        h = re.match(r"request tail \[([^\]]*)\] \| target \[([^\]]*)\]", line)
        if h:
            close(); tail = [int(x) for x in h.group(1).split(", ")]; target = [int(x) for x in h.group(2).split(", ")]; station, rows = None, {}; continue
        s = re.match(r"\s+station (\d+):", line)
        if s:
            close(); station, rows = int(s.group(1)), {}; continue
        c = re.match(r"\s+class (\d+): pair \[(.*)\] alone \[(.*)\] ", line)
        if c:
            p, a = members(c.group(2)), members(c.group(3))
            if all(y > 0 for y in a):
                rows[int(c.group(1))] = laws(p, a)
    close()
    print(path)
    for n in names:
        q = narrow[n]
        print(f"  {n}: wrong {wrong[n]}, narrowest target/runner-up among right " + (f"{q.numerator // q.denominator} rem {q.numerator % q.denominator}/{q.denominator}" if q is not None else "none"))
