#!/usr/bin/env -S python3 -I
"""seen_passage.py TRAIN DEV KEYS OUT_DIR: two passages cut from the training passage beside the held one, so that one held read
can be taken on problems the field trained on and on problems it withheld (G111).

The lap (`train-field`) withholds as many training problems as the held passage holds: the first in the keyed order
`(mix(seed, 2^61 | i), i)` of the training passage's problems, the seed the key file's last eight bytes read big-endian
(field_train.rs, `sections_of` and `mix`). It trains every other problem once a lap. This ruler writes, under OUT_DIR, which it
creates and refuses if it stands:

- WITHHELD.txt: the withheld problems, in their index order, each record as the training passage holds it;
- SEEN.txt: as many trained problems, one matched to each held problem in the held passage's order: the unused trained problem
  nearest it by the answer's bytes, then by the question's, then the lower index; none withheld and none chosen twice.

Both passages hold rows of the training passage, so they stay private, beside the passages they are cut from, and are never committed.

A record is `question US answer RS` (US 0x1F, RS 0x1E), read as `problems_of` reads it: a record without US, or with an empty question
or answer, is not a problem. Printed: each passage's problems, bytes and SHA-256; the lap's own counts (trained, withheld), to stand
beside the lap's FIELD_DECLARATION line; the quartiles of the answers' and the questions' bytes in DEV, SEEN and WITHHELD; how many
withheld problems share their question or their answer, byte for byte, with a trained problem, and how many held problems do.

Reason: the circle line's held read stood on one passage, and its quarter 4 (the most open quarter) turned back from te4 to te6 while
quarters 1 to 3 fell. Whether that turn is a trade of the field's capacity between its regions, or its far law fitting the answers it
trains on, is read by the same held read on problems it trained on (SEEN) and on training problems it never trained on (WITHHELD),
beside the held passage. Matching SEEN to the held passage by lengths keeps the open quarters' places alike, since a quarter's code
grows with the distance from its letters to the written ones. A ruler on the host: it reads passages and writes passages, never a
state, and no reading of the field is made here.
"""
import hashlib
import os
import sys

RS, US = 0x1E, 0x1F
MASK = (1 << 64) - 1
GAMMA = 0x9E3779B97F4A7C15
WITHHELD_DRAW = 1 << 61


def mix(seed, counter):
    """field_train.rs `mix`: the integer mixer of a seed and a counter (the splitmix64 step at `seed + counter * gamma`)."""
    z = (seed + counter * GAMMA) & MASK
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
    return z ^ (z >> 31)


def problems_of(text):
    """The problems of a passage of records, as field_train.rs `problems_of` reads one: (question, answer) byte strings."""
    out = []
    for record in text.split(bytes([RS])):
        cut = record.find(bytes([US]))
        if cut < 0:
            continue
        q, a = record[:cut], record[cut + 1:]
        if q and a:
            out.append((q, a))
    return out


def seed_of(keys):
    """The key file's last word, big-endian, as the lap reads its seed."""
    if len(keys) < 8:
        raise SystemExit("a key file of fewer than eight bytes")
    return int.from_bytes(keys[-8:], "big")


def withheld_of(count, withheld, seed):
    """The withheld problems' indices (sorted) and the trained ones', as `sections_of` splits a passage of `count` problems."""
    keyed = sorted(range(count), key=lambda i: (mix(seed, WITHHELD_DRAW | i), i))
    held = sorted(keyed[: min(withheld, count)])
    return held, sorted(keyed[min(withheld, count):])


def matched(dev, problems, trained):
    """For each held problem in order, the unused trained problem nearest by answer bytes, then question bytes, then index."""
    if len(trained) < len(dev):
        raise SystemExit(f"{len(trained)} trained problems to match {len(dev)} held ones")
    unused = set(trained)
    chosen = []
    for q, a in dev:
        best = min(unused, key=lambda i: (abs(len(problems[i][1]) - len(a)), abs(len(problems[i][0]) - len(q)), i))
        unused.remove(best)
        chosen.append(best)
    return chosen


def quartiles(values):
    """The values at a quarter, a half and three quarters of their sorted order (the lap's own quartile cut)."""
    v = sorted(values)
    return "/".join(str(v[(k * len(v)) // 4]) for k in (1, 2, 3)) if v else "-"


def passage(problems):
    """A passage of records, each `question US answer RS`."""
    return b"".join(q + bytes([US]) + a + bytes([RS]) for q, a in problems)


def main(argv):
    if len(argv) != 5:
        raise SystemExit("seen_passage.py TRAIN DEV KEYS OUT_DIR")
    train, dev = (problems_of(open(p, "rb").read()) for p in argv[1:3])
    seed = seed_of(open(argv[3], "rb").read())
    out = argv[4]
    os.makedirs(out)
    withheld, trained = withheld_of(len(train), len(dev), seed)
    seen = matched(dev, train, trained)
    print(f"SEEN_PASSAGE train_problems={len(train)} trained={len(trained)} withheld={len(withheld)} dev={len(dev)}")
    sets = (("WITHHELD", [train[i] for i in withheld]), ("SEEN", [train[i] for i in seen]))
    for name, chosen in sets:
        data = passage(chosen)
        path = os.path.join(out, f"{name}.txt")
        with open(path, "xb") as f:
            f.write(data)
        print(f"SEEN_PASSAGE_FILE {name}.txt problems={len(chosen)} bytes={len(data)} sha256={hashlib.sha256(data).hexdigest()}")
    for name, chosen in (("DEV", dev),) + sets:
        print(f"SEEN_PASSAGE_LENGTHS {name} answer_bytes_quartiles={quartiles([len(a) for _, a in chosen])} question_bytes_quartiles={quartiles([len(q) for q, _ in chosen])} answer_bytes={sum(len(a) for _, a in chosen)}")
    questions = {train[i][0] for i in trained}
    answers = {train[i][1] for i in trained}
    shared = lambda chosen: (sum(q in questions for q, _ in chosen), sum(a in answers for _, a in chosen))
    for name, chosen in (("WITHHELD", sets[0][1]), ("DEV", dev)):
        sq, sa = shared(chosen)
        print(f"SEEN_PASSAGE_SHARED {name} question_in_trained={sq} answer_in_trained={sa} of={len(chosen)}")


if __name__ == "__main__":
    main(sys.argv)
