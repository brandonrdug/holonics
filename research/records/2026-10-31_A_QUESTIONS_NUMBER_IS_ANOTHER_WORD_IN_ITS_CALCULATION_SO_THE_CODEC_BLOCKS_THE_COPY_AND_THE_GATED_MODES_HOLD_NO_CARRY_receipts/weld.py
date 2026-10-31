"""How often a question's numeral is the same unit word in its first calculation (record §3).

    python3 -I weld.py UNITS TRAIN_JSONL COUNT

UNITS is a founded-units file (`founded-units-v1 N`, one merge a line); TRAIN_JSONL is GSM8K's
public training split; COUNT the first problems read. Each problem is rendered as the tower's
passage renders it (`question END answer END`, END = 0x1E) and parsed by the founding's merges
in order (`hnn::units::Units::parse`). For every operand of the answer's first `<<…>>` that the
question writes as a numeral, the units covering its digits in the question and in the
calculation are compared as words. An exterior count: nothing here enters the machine.
"""
import json, re, sys

lines = open(sys.argv[1]).read().split("\n")
merges = [tuple(map(int, l.split())) for l in lines[1:1 + int(lines[0].split()[1])]]
pieces = [bytes([i]) for i in range(256)]
for a, b in merges:
    pieces.append(pieces[a] + pieces[b])


def parse(bs):
    seq = list(bs)
    present = set(seq)
    for i, (a, b) in enumerate(merges):
        if a not in present or b not in present:
            continue
        out, j, hit = [], 0, False
        while j < len(seq):
            if j + 1 < len(seq) and seq[j] == a and seq[j + 1] == b:
                out.append(256 + i); j += 2; hit = True
            else:
                out.append(seq[j]); j += 1
        if hit:
            seq = out
            present.add(256 + i)
    return seq


def word(spans, s, e):
    return tuple(pieces[u] for (a, b, u) in spans if a < e and b > s)


num = re.compile(rb"\d+(?:\.\d+)?")
digit_only = lambda w: all(all(48 <= c <= 57 or c == 46 for c in p) for p in w)
rows = [json.loads(l) for l in open(sys.argv[2], encoding="utf-8")][: int(sys.argv[3])]
found = same = pure = with_calc = all_from_q = 0
for r in rows:
    q, a = r["question"].encode(), r["answer"].encode()
    spans, at = [], 0
    for u in parse(q + b"\x1e" + a + b"\x1e"):
        spans.append((at, at + len(pieces[u]), u)); at += len(pieces[u])
    m = re.search(rb"<<([^=>]*)=([^>]*)>>", a)
    if not m:
        continue
    with_calc += 1
    qnums = {}
    for n in num.finditer(q):
        qnums.setdefault(n.group(), (n.start(), n.end()))
    ops = list(num.finditer(m.group(1)))
    all_from_q += bool(ops) and all(o.group() in qnums for o in ops)
    base = len(q) + 1 + m.start(1)
    for o in ops:
        if o.group() not in qnums:
            continue
        found += 1
        wq, wc = word(spans, *qnums[o.group()]), word(spans, base + o.start(), base + o.end())
        same += wq == wc
        pure += digit_only(wq)
print(f"WELD problems={len(rows)} with_calculation={with_calc} first_calc_all_from_question_numerals={all_from_q} "
      f"operands_the_question_writes={found} same_word={same} question_word_digits_only={pure}")
