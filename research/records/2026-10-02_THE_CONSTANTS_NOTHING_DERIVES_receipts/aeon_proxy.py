"""The joint clock's aeon on repository text, a proxy for the cut's text (record §3.3).

The clock as stated in the 2026-09-25 record §1: rings of periods 5, 7, 11, 13 in carry order;
rings 0-2 step on a byte b = 0 mod d_g, ring 3 only by carry; the aeon closes at ring 3's
carry-out. This is a simulation of that stated law, not the code's owner. Exact integers only.
Run from the repository root at 5dab4c71 (the record itself is not yet in the glob there): python3 <this file>.
"""
import glob

PERIODS = (5, 7, 11, 13)

for pattern in ("docs/**/*.md", "research/records/*.md", "crates/holonics/src/**/*.rs"):
    files = sorted(glob.glob(pattern, recursive=True))
    data = b"".join(open(f, "rb").read() for f in files)
    locks = [sum(1 for b in data if b % d == 0) for d in PERIODS[:3]]
    # The long-run carry-out rate (c0 + 5 c1 + 35 c2) / (n * 5005): mean aeon n*5005/(c0+5c1+35c2).
    num = len(data) * 5 * 7 * 11 * 13
    den = locks[0] + 5 * locks[1] + 35 * locks[2]
    q, r = divmod(num, den)
    phase, lengths, last = [0, 0, 0, 0], [], 0
    for i, b in enumerate(data):
        own = [b % 5 == 0, b % 7 == 0, b % 11 == 0, False]
        carry = False
        for g, d in enumerate(PERIODS):
            steps = int(own[g]) + int(carry)
            carry = False
            for _ in range(steps):
                phase[g] += 1
                if phase[g] == d:
                    phase[g] = 0
                    carry = True
        if carry:
            lengths.append(i + 1 - last)
            last = i + 1
    s = sorted(lengths)
    mq, mr = divmod(sum(lengths), len(lengths))
    print(f"{pattern}: {len(files)} files, {len(data)} bytes; lock counts {locks}; "
          f"mean aeon by rate {q} rem {r} over {den}; {len(lengths)} aeons, measured mean "
          f"{mq} rem {mr} over {len(lengths)}; least {s[0]}, median {s[len(s) // 2]}, largest {s[-1]}")
