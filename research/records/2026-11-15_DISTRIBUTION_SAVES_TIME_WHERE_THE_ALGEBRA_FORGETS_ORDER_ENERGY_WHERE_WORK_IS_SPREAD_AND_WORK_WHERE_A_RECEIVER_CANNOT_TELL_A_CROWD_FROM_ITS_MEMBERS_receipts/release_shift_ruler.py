"""Ruler (host, Python integers): the release as one add and one arithmetic shift.

The release `rel(x, b)` is the nearest quotient of `x` by `2^b`, half away from zero; its card form had two branches,
`(x + h) >> b` for `x >= 0` and `-((-x + h) >> b)` below, with `h = 2^(b - 1)`. The build of 07:09 UTC on November 16
writes it `(x + h - [x < 0]) >> b`. For `x < 0`, `-floor((-x + h) / 2^b) = ceil((x - h) / 2^b) = floor((x + h - 1) / 2^b)`
since `2^b - h = h`. This asserts the two forms equal for every `b` from 1 to 127 on edges and draws inside the
128-bit word (where neither form's add leaves it), and that `b = 0` has no `h`: the guard `rel(x, 0) = x` must stay.
"""
import random

random.seed(20261116)
LO, HI = -(1 << 127), (1 << 127) - 1


def rel_two_branches(x, b):
    h = 1 << (b - 1)
    return (x + h) >> b if x >= 0 else -((-x + h) >> b)


def rel_one_shift(x, b):
    h = 1 << (b - 1)
    return (x + h - (1 if x < 0 else 0)) >> b


reads = 0
for b in range(1, 128):
    h = 1 << (b - 1)
    edges = [0, 1, -1, h, -h, h - 1, -h + 1, h + 1, -h - 1, (1 << b) - 1, -(1 << b) + 1, 3 * h, -3 * h, LO + 1, HI - h]
    draws = [random.randint(LO + 1, HI - h) for _ in range(400)]
    for x in edges + draws:
        if not (LO < x <= HI - h):
            continue
        assert rel_two_branches(x, b) == rel_one_shift(x, b), (x, b)
        reads += 1
print(f"the two forms agree on {reads} reads, b from 1 to 127, |x| inside the word less h")
try:
    rel_one_shift(5, 0)
    raise AssertionError("b = 0 should have no h")
except ValueError:
    print("b = 0: h = 2^(-1) is no integer (a negative shift); rel(x, 0) = x stays a guard")
