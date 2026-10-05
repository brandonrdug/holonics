#!/usr/bin/env python3
"""Tally a released-sections listing of `executed evaluate` (the regressions record).

Per state: requests, nonconstant and constant apart; released and held; whole sections; stations
right of the released classes; adjacent stations equal; and the stations that follow the located pair
of a released section (`x_t = f(x_(t - delta))` along the request then the released section, with
`f` the identity, the regressions' located map). Exact counts only.

usage: tally.py <sections.txt> <delta>
"""
import re
import sys


def main(path: str, delta: int) -> None:
    states = {}
    order = []
    state = None
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        header = re.match(r"== (\S+) on ", line)
        if header:
            state = header.group(1)
            order.append(state)
            states[state] = []
            continue
        if state is None or not line.strip():
            continue
        request, rest = line.split(" | target ", 1)
        target = [int(x) for x in re.match(r"\[([^\]]*)\]", rest).group(1).split(", ")]
        kind = re.search(r"\| (released|held) \[([^\]]*)\]", rest)
        released = kind.group(1) == "released"
        classes = [int(x) for x in kind.group(2).split(", ")]
        constant = rest.endswith("| constant request")
        states[state].append((request, target, released, classes, constant))
    for state in order:
        rows = states[state]
        tally = {}
        for part in ("nonconstant", "constant"):
            chosen = [r for r in rows if r[4] == (part == "constant")]
            whole = sum(1 for r in chosen if r[2] and r[3] == r[1])
            released = sum(1 for r in chosen if r[2])
            right = sum(sum(a == b for a, b in zip(r[3], r[1])) for r in chosen)
            follows = 0
            for request, _, was_released, classes, _ in chosen:
                if not was_released:
                    continue
                passage = [int(c) for c in request] + classes
                n = len(request)
                follows += sum(passage[n + j] == passage[n + j - delta] for j in range(len(classes)))
            adjacent = sum(sum(c[j] == c[j + 1] for j in range(len(c) - 1)) for _, _, _, c, _ in chosen)
            tally[part] = (len(chosen), released, whole, right, 8 * len(chosen), follows, adjacent)
        print(f"{state}:")
        for part, (n, released, whole, right, stations, follows, adjacent) in tally.items():
            print(
                f"  {part}: {n} requests, released {released}, whole {whole}, stations right {right} of "
                f"{stations}, released stations following x_t = x_(t-{delta}) {follows}, adjacent equal {adjacent}"
            )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]))
