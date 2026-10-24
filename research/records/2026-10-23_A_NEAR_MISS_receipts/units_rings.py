"""The correction of §2: a written sum's units read on the two rings of ℤ/10 = ℤ/2 × ℤ/5.

Reads the towers' digit-prompt writings with the design thread's own parser
(`tools/answer_digits.py`, `text_of` and the whole-equation rule), so the equations counted are
exactly those of its `ANSWER_DIGITS.txt`, and counts for the sums: units right, parity right and
residue mod 5 right, beside each ring's chance count. Exact integer counts; an exterior reading.

usage: python3 -I units_rings.py ANSWER_DIGITS_PY WRITE [WRITE ...]
(the writings: the `*WRITE*.txt` receipts of the tower record at commit f6a54bc37)
"""
import hashlib
import importlib.util
import json
import re
import sys

EQ = re.compile(r"^(\d+)([+\-*])(\d+)=(\d+)$")


def main():
    spec = importlib.util.spec_from_file_location("answer_digits", sys.argv[1])
    ad = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ad)
    paths = sorted(sys.argv[2:])
    sums, digest = [], hashlib.sha256()
    for path in paths:
        digest.update(open(path, "rb").read())
        for line in ("74-72=" + ad.text_of(path)).split("\n"):
            m = EQ.match(line)
            if m and m.group(2) == "+":
                a, _, b, c = m.groups()
                sums.append((a, b, c, str(int(a) + int(b))))
    n = len(sums)
    out = {
        "writes": len(paths),
        "writes_sha256": digest.hexdigest(),
        "sums": n,
        "units_right": sum(c[-1] == t[-1] for _, _, c, t in sums),
        "parity_right": sum(int(c[-1]) % 2 == int(t[-1]) % 2 for _, _, c, t in sums),
        "mod5_right": sum(int(c[-1]) % 5 == int(t[-1]) % 5 for _, _, c, t in sums),
        "chance": {"units": f"{n}/10", "parity": f"{n}/2", "mod5": f"{n}/5"},
    }
    assert out["units_right"] <= min(out["parity_right"], out["mod5_right"])
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
