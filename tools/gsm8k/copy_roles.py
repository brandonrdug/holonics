"""The copy partition of the held-out passage: which answer digits the problem's own question writes.

An exterior reading: it reads the passage bytes `tower_passage.py` writes (`DEV.bytes`) and writes a
roles file for the trainer to report the held-out code by. Nothing here enters the machine, selects a
release or reads the answer key (`README.md`).

    python3 -I tools/gsm8k/copy_roles.py DEV_BYTES OUT_ROLES

DEV_BYTES is a run of problems rendered `question END answer END`, END the byte 0x1E, so splitting at
END gives pieces that alternate question, answer. It is refused when the count of END bytes is odd or
the passage does not end with END. OUT_ROLES is created and never overwritten; it holds one byte for
each passage byte:

- 0: every question byte and the END after it;
- 1: every answer byte that is not an ASCII decimal digit, and the END after the answer;
- 2: every digit of an answer numeral whose text equals a numeral the same problem's question writes;
- 3: every digit of an answer numeral the question does not write.

A numeral is a match of the bytes regex `\\d+(?:\\.\\d+)?` (its '.' byte is role 1; only digit bytes take
2 or 3), compared as its bytes: `12` in an answer is copied when the question writes `12` and not when
it writes `125` or `12.5`. The numerals of other problems are not the question's.

The trainer prints the roles 0-3 under the names Q/P/N/M of `tower_passage.py`, so a receipt that uses
this file reads N as "answer digits the question writes" and M as "answer digits it does not". One
line is printed: the roles file's length, its SHA-256 and the count of bytes in each role.
"""

import hashlib
import re
import sys

END = 0x1E
NUMERAL = re.compile(rb"\d+(?:\.\d+)?")


def roles_of(passage):
    """One role byte for each passage byte, as the module docstring lists them."""
    if not passage.endswith(bytes([END])):
        raise SystemExit("the passage does not end with END (0x1E)")
    pieces = passage.split(bytes([END]))[:-1]
    if len(pieces) % 2:
        raise SystemExit(f"the passage holds {len(pieces)} END bytes, an odd count: questions and answers do not pair")
    roles = bytearray()
    for question, answer in zip(pieces[0::2], pieces[1::2]):
        roles += bytes(len(question) + 1)
        written = set(NUMERAL.findall(question))
        answer_roles = bytearray([1] * (len(answer) + 1))
        for m in NUMERAL.finditer(answer):
            role = 2 if m.group() in written else 3
            for k in range(m.start(), m.end()):
                if 48 <= answer[k] <= 57:
                    answer_roles[k] = role
        roles += answer_roles
    assert len(roles) == len(passage)
    return bytes(roles)


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    with open(sys.argv[1], "rb") as f:
        roles = roles_of(f.read())
    try:
        with open(sys.argv[2], "xb") as f:
            f.write(roles)
    except FileExistsError:
        raise SystemExit(f"{sys.argv[2]} exists; it is never overwritten")
    counts = " ".join(f"role{k}={roles.count(k)}" for k in range(4))
    print(f"COPY_ROLES length={len(roles)} sha256={hashlib.sha256(roles).hexdigest()} {counts}")


if __name__ == "__main__":
    main()
