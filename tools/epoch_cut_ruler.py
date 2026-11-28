#!/usr/bin/env -S python3 -I
"""epoch_cut_ruler.py ROWS CUT: a ruler (the lead, November 27; the formal thread's G-Z47 of 18:51 UTC). Whether her epochs cut a word
met again at the same offsets as its earlier meeting.

CUT is a `read-strand-cut … past` output (`cut.tsv`, the known stream's anchors). A word is a run of letters of ROWS's rows; its cut is the
offsets from its first place of the anchors that stand on its places or on the place after it. For each word met again in its row, the
later meeting's cut is set beside the earlier's, by the word's length (eight and more as one) and whether it was met within 30 places; beside
it, chance: two meetings of words of the same length drawn at random. Beside them, where the anchors fall (the formal thread's G-Z65 of
01:29 UTC, November 28: same-cut is partly built in by a cut's construction, so it is read beside its density and its ends' places): the
share of places after a space that carry an anchor, and the anchors parted by the place they stand on (a word's first letter, a letter
inside a word, the place after a word's last letter, any other place). Outside the machine; counts.
"""
import random
import sys
from collections import defaultdict


def letter(b):
    return 65 <= b <= 90 or 97 <= b <= 122


def main():
    rows_f, cut_d = sys.argv[1], sys.argv[2]
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n', '\n').encode() for t in f[1:3]))
    pairs, chance = defaultdict(lambda: [0, 0]), defaultdict(lambda: [0, 0])
    rng = random.Random(27)
    anchors_n = places_n = 0
    after_space, where = [0, 0], defaultdict(int)
    for line in open(f'{cut_d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        r, n = int(f[0]), int(f[1])
        anchors = {int(a) for a in f[2].split(',') if a}
        anchors_n, places_n = anchors_n + len(anchors), places_n + n
        t = texts[r][:n]
        for p in range(1, n):
            if t[p - 1] == 32:
                after_space[0] += p in anchors
                after_space[1] += 1
        for a in anchors:
            if a >= n or a == 0:
                continue
            if letter(t[a]):
                where['first_letter' if not letter(t[a - 1]) else 'inside_word'] += 1
            else:
                where['after_word' if letter(t[a - 1]) else 'other'] += 1
        words, i = [], 0
        while i < n:
            if letter(t[i]):
                j = i
                while j < n and letter(t[j]):
                    j += 1
                words.append((i, j, bytes(t[i:j])))
                i = j
            else:
                i += 1
        last, by_len = {}, defaultdict(list)
        for s, e, w in words:
            cut = tuple(a - s for a in range(s, e + 1) if a in anchors)
            length = min(len(w), 8)
            if w in last:
                same = cut == last[w][1]
                for key in (('length', length, 'within_30' if s - last[w][0] <= 30 else 'over_30'), ('all',), ('three_or_more',) if len(w) >= 3 else None):
                    if key:
                        pairs[key][0] += same
                        pairs[key][1] += 1
            by_len[length].append(cut)
            last[w] = (s, cut)
        for length, cuts in by_len.items():
            for _ in range(min(200, len(cuts))):
                chance[length][0] += rng.choice(cuts) == rng.choice(cuts)
                chance[length][1] += 1
    print(f"EPOCH_CUT places={places_n} anchors={anchors_n} places_an_epoch={places_n / anchors_n:.2f}")
    print(f"EPOCH_CUT after_space places={after_space[1]} anchored={after_space[0] / max(after_space[1], 1):.3f}")
    placed = sum(where.values())
    for key in ('first_letter', 'inside_word', 'after_word', 'other'):
        print(f"EPOCH_CUT anchors_at {key} count={where[key]} share={where[key] / max(placed, 1):.3f}")
    for key in sorted(pairs, key=str):
        a, b = pairs[key]
        print(f"EPOCH_CUT {' '.join(map(str, key))} pairs={b} same={a / b:.3f}")
    for length in sorted(chance):
        a, b = chance[length]
        print(f"EPOCH_CUT_CHANCE length {length} same={a / b:.3f}")


if __name__ == '__main__':
    main()
