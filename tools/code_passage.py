#!/usr/bin/env python3
"""The code passage's boundary codec (Brandon, November 5: python-codes-25k in place of GSM8K).

Usage: code_passage.py ROWS.jsonl OUT_DIR

Reads the dataset's rows (`instruction`, `input`, `output`) and writes two passages of records for the field trainer's
`problems_of`: `TRAIN.txt` and `HELD128.txt`, each problem `question US answer RS` (US 0x1F, RS 0x1E), the question the
instruction (and, where the row has one, a newline and its input), the answer the output, every byte as the row holds it.
The held problems are the 128 first in a keyed order (SHA-256 of `held128 | question US answer`) among the rows whose
instruction and whose output each stand in no other row, so no held question or answer is met in training; every other
row is a training problem. Refuses a row that holds either separator. Prints the counts and each passage's SHA-256.
Dataset roles are exterior codec information, not native identities.
"""
import hashlib
import json
import os
import sys
from collections import Counter

RS, US = b"\x1e", b"\x1f"


def main():
    rows = [json.loads(line) for line in open(sys.argv[1], encoding="utf-8")]
    out = sys.argv[2]
    problems = []
    for r in rows:
        q = r["instruction"] + ("\n" + r["input"] if r.get("input") else "")
        q, a = q.encode("utf-8"), r["output"].encode("utf-8")
        if RS in q + a or US in q + a:
            sys.exit("a row holds a separator")
        problems.append((q, a, r["instruction"], r["output"]))
    ins = Counter(p[2] for p in problems)
    outs = Counter(p[3] for p in problems)
    unique = [i for i, p in enumerate(problems) if ins[p[2]] == 1 and outs[p[3]] == 1]
    keyed = sorted(unique, key=lambda i: hashlib.sha256(b"held128|" + problems[i][0] + US + problems[i][1]).digest())
    held = set(keyed[:128])
    os.makedirs(out, exist_ok=True)
    for name, chosen in (("TRAIN.txt", [p for i, p in enumerate(problems) if i not in held]), ("HELD128.txt", [problems[i] for i in keyed[:128]])):
        data = b"".join(q + US + a + RS for q, a, _, _ in chosen)
        with open(os.path.join(out, name), "wb") as f:
            f.write(data)
        print(f"{name}: {len(chosen)} problems, {len(data)} bytes, sha256 {hashlib.sha256(data).hexdigest()}")
    print(f"rows {len(rows)}, unique in both {len(unique)}, held {len(held)}")


if __name__ == "__main__":
    main()
