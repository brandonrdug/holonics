"""An exterior baseline's releases for the written-rule reads (`written_rules.py`).

A character n-gram with interpolated Witten-Bell smoothing, trained on the training text, writes
what `read-unit-tower-written` writes, in the same files: for each held-out problem a free release
from the framed question (a blank line, the question, its line end), and at each calculation of the
held-out answer a release after its `=`. It is a baseline read beside the machine and never enters
it; its floats are the baseline's own. Record:
research/records/2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS.md

    python3 -I tools/gsm8k/ngram_release.py TRAIN HELD ORDER BYTES AGREE MARK_AGREE MARK_CAP OUT

The free release draws `BYTES` bytes at `AGREE` agreeing draws (the distribution raised to that
power), and each calculation's release draws at `MARK_AGREE` until it holds `>>` or a line end, or
`MARK_CAP` bytes. Problem `i` draws from `random.Random(i)`.
"""

import os
import random
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from written_rules import calculations_of, problems_of  # noqa: E402


class NGram:
    def __init__(self, text, order):
        self.order = order
        self.count = defaultdict(int)
        self.total = defaultdict(int)
        self.kinds = defaultdict(int)
        self.next = defaultdict(list)
        for k in range(order + 1):
            for i in range(k, len(text)):
                key = text[i - k : i + 1]
                if self.count[key] == 0:
                    self.kinds[key[:-1]] += 1
                    self.next[key[:-1]].append(key[-1])
                self.count[key] += 1
                self.total[key[:-1]] += 1

    def face(self, history):
        """The interpolated distribution over the 256 bytes after `history`."""
        p = [1.0 / 256] * 256
        h = history[-self.order :] if self.order else b""
        for k in range(len(h) + 1):
            ctx = h[len(h) - k :] if k else b""
            total = self.total.get(ctx, 0)
            if total == 0:
                break
            t = self.kinds[ctx]
            q = [t * x for x in p]
            for c in self.next[ctx]:
                q[c] += self.count[ctx + bytes([c])]
            p = [x / (total + t) for x in q]
        return p

    def sample(self, history, rng):
        """One draw from the interpolated distribution, without forming it: the longest context
        the training text holds keeps its counts with weight `total / (total + kinds)` and hands the
        rest to the context one shorter, down to the uniform byte."""
        h = history[-self.order :] if self.order else b""
        used = []
        for k in range(len(h) + 1):
            ctx = h[len(h) - k :] if k else b""
            if self.total.get(ctx, 0) == 0:
                break
            used.append(ctx)
        for ctx in reversed(used):
            total, t = self.total[ctx], self.kinds[ctx]
            r = rng.random() * (total + t)
            if r < total:
                for c in self.next[ctx]:
                    r -= self.count[ctx + bytes([c])]
                    if r < 0:
                        return c
                return self.next[ctx][-1]
        return rng.randrange(256)


def draw(p, agree, rng):
    w = [x**agree for x in p]
    s = sum(w)
    r = rng.random() * s
    for c, x in enumerate(w):
        r -= x
        if r < 0:
            return c
    return max(range(256), key=lambda c: w[c])


def field(bs):
    return "".join("\\x7c" if b == 0x7C else chr(b).encode("unicode_escape").decode() if 32 <= b < 127 or b in (9, 10, 13) else f"\\x{b:02x}" for b in bs)


def main():
    if len(sys.argv) != 9:
        raise SystemExit(__doc__)
    train, held = (open(p, "rb").read() for p in sys.argv[1:3])
    order, count, agree, mark_agree, mark_cap = map(int, sys.argv[3:8])
    out = sys.argv[8]
    os.mkdir(out)
    model = NGram(train, order)
    free_rows, mark_rows = [], []
    for i, (q, a) in enumerate(problems_of(held)):
        rng = random.Random(i)
        framed = b"\n\n" + q + b"\n"
        text = bytearray(framed)
        for _ in range(count):
            text.append(model.sample(bytes(text), rng) if agree == 1 else draw(model.face(bytes(text)), agree, rng))
        free_rows.append(f"{i}\t{field(bytes(text[len(framed):]))}\n")
        through = 0
        for j, expression in enumerate(calculations_of(a)):
            at = a.index(b"<<" + expression + b"=", through)
            through = at + len(expression) + 3
            prompt = bytearray(framed + a[:through])
            release = bytearray()
            while len(release) < mark_cap and b">>" not in release and b"\n" not in release:
                c = draw(model.face(bytes(prompt)), mark_agree, rng)
                release.append(c)
                prompt.append(c)
            mark_rows.append(f"{i}\t{j}\t{field(expression)}\t{field(bytes(release))}\n")
    with open(f"{out}/FREE.tsv", "x") as f:
        f.writelines(free_rows)
    with open(f"{out}/MARKS.tsv", "x") as f:
        f.writelines(mark_rows)
    print(f"NGRAM_WRITTEN order={order} problems={len(free_rows)} calculations={len(mark_rows)}")


if __name__ == "__main__":
    main()
