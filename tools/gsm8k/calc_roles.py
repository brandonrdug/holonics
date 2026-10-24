"""Mark the calculation results of a prepared GSM8K text by whether their expression was met in
training: one region byte per byte of DEV, for the tower's held-out read.

A calculation is `<<expression=result>>`. Its result's content digits are region 0 when the same
expression is calculated somewhere in TRAIN, 1 when it is not; the scale of an integer result (its
trailing zeros; a result 0 is content) is region 2; every other byte, the echo after `>>` included,
is region 3. An exterior partition of the text: nothing of it enters the machine.

usage: python3 -I calc_roles.py TRAIN DEV OUT_ROLES
"""
import re
import sys

CALCULATION = re.compile(rb"<<([^=<>]*)=([^<>]*)>>")


def main():
    train, dev, out = sys.argv[1:4]
    seen = {m.group(1) for m in CALCULATION.finditer(open(train, "rb").read())}
    text = open(dev, "rb").read()
    regions = bytearray([3] * len(text))
    counts = {"seen": 0, "unseen": 0}
    for m in CALCULATION.finditer(text):
        result, start = m.group(2), m.start(2)
        side = 0 if m.group(1) in seen else 1
        counts["seen" if side == 0 else "unseen"] += 1
        integer = re.fullmatch(rb"-?\d+", result) is not None
        content = len(result.rstrip(b"0")) if integer and result.strip(b"-0") else len(result)
        for k, b in enumerate(result):
            if chr(b).isdigit():
                regions[start + k] = side if k < content else 2
    with open(out, "xb") as f:
        f.write(bytes(regions))
    print(f"CALC_ROLES calculations_seen={counts['seen']} unseen={counts['unseen']} "
          + " ".join(f"region{r}={regions.count(r)}" for r in range(4)))


if __name__ == "__main__":
    main()
