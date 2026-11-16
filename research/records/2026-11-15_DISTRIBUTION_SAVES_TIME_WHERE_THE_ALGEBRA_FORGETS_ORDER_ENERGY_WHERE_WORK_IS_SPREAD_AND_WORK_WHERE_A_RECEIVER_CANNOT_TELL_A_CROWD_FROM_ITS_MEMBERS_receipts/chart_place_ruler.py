"""Ruler (host, Python integers): the square root's first place read from the bit length.

The build of 04:18 UTC on November 16 reads the first place of the chart's bit-by-bit square root
as 2^((len - 1) & ~1) in place of stepping 2^126 down two bits at a time while it stands above n.
This ruler asserts that the two places and the roots agree for every n >= 1 it reads, prints what
n = 0 does under each, and counts the digit steps after which the remainder and res + bit stand
below 2^64 (where the loop could continue on one limb, the same integer).
"""
import math
import random

random.seed(20261116)


def place_stepped(n):
    bit, idle = 1 << 126, 0
    while bit > n:
        bit >>= 2
        idle += 1
    return bit, idle


def place_from_length(n):
    length = n.bit_length()
    assert length >= 1, "n = 0 has no bit length: the place needs a guard"
    return 1 << ((length - 1) & ~1)


def digits(n, bit):
    res, step, narrow_from = 0, 0, None
    while bit:
        if narrow_from is None and max(n, res + bit) < (1 << 64):
            narrow_from = step
        if n >= res + bit:
            n -= res + bit
            res = (res >> 1) + bit
        else:
            res >>= 1
        bit >>= 2
        step += 1
    return res, step, narrow_from


edges = [(1 << j) + d for j in range(128) for d in (-1, 0, 1) if 1 <= (1 << j) + d < (1 << 128)]
draws = [random.getrandbits(random.randint(1, 128)) | 1 for _ in range(100000)]
for n in edges + draws:
    stepped, _ = place_stepped(n)
    read = place_from_length(n)
    assert stepped == read, n
    assert digits(n, read)[0] == math.isqrt(n), n
print(f"places and roots agree on {len(edges) + len(draws)} inputs n >= 1 (edges 2^j - 1, 2^j, 2^j + 1)")

bit0, idle0 = place_stepped(0)
assert (bit0, idle0, digits(0, bit0)[0]) == (0, 64, 0)
print("n = 0, stepped: the place falls to 0 after 64 idle steps and the root is 0")
print(f"n = 0, from the length: len - 1 = -1, masked {(-1) & ~1}; as u32 {((0 - 1) & 0xFFFFFFFF) & ~1}")

_, idle87 = place_stepped(1 << 86)
assert idle87 == 20
print(f"a power of 87 bits: {idle87} idle steps of the stepped place")
for length in (70, 80, 87, 96, 110):
    reads = [digits(n, place_from_length(n)) for n in
             (random.getrandbits(length) | (1 << (length - 1)) for _ in range(2000))]
    steps = {s for _, s, _ in reads}
    narrow = [f for _, _, f in reads]
    assert len(steps) == 1 and None not in narrow
    print(f"len {length}: {steps.pop()} digit steps, one limb from step {min(narrow)} to {max(narrow)}")
