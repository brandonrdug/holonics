#!/usr/bin/env -S python3 -I
"""join_count_ruler.py DUMP ROWS [planted|words]: a ruler (the lead, November 27; the formal thread's ceiling for the join, 04:01 UTC, G-Z12). How much
of a place a count of the passage could tell from what the join carries.

`read-strand-cut ... past face` (DUMP) writes the known stream's anchors and the epoch each open place reads (`cut.tsv`). The join tells
an open place its epoch before (the row the level hands on) and where the place stands in its own epoch (its phase). So this counts, on
the even rows, each place's byte against two conditions: the spelling of the epoch it reads with its distance from its own epoch's site,
backed off to the last four, two and one bytes of that spelling with the distance, then the distance alone, by interpolated absolute
discounting (each order's count less 0.75, the mass taken handed to the order below in proportion to its distinct bytes); and its byte
alone over the alphabet seen, with one added to every count. How many of the orders the count uses is chosen on the even rows alone
(counted on their first half, coded on their second). (Witten–Bell's interpolation, its first form, trusted a spelling seen
once and coded the places given the spelling above their codes alone.) On the odd rows each place's code given the join's condition over its code alone is the share a
count leaves unsaid, `n_count = R/Z`, read by the place's part (a word's first letter, a letter inside a word, any other byte) beside the
join's own share (`tools/level_face_ruler.py`'s `LEVEL_FACE_JOIN_PART`). With `planted` (rule 11, the formal thread's proof of the
ruler's null, November 27): on every third row each place's byte is set to the last byte of the epoch it reads, a join a count must find,
and the planted rows' parts are read apart (`JOIN_COUNT_PLANTED`). With `words` (the formal thread's G-Z29, November 27 14:59 UTC) the
units are the writers' words in place of her epochs: a place's unit is the run of non-space bytes it stands in with the spaces after it,
the join's condition the spelling of the unit before and the place's distance into its own (`JOIN_COUNT_WORDS`). Outside the machine; counts and ratios, floats at the exterior.
"""
import math
import sys
from collections import defaultdict

# The discount of interpolated absolute discounting (Ney, Essen and Kneser): a ruler's constant, the standard value for sparse counts.
DISCOUNT = 0.75


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    planted = len(sys.argv) > 3 and sys.argv[3] == 'planted'
    words = len(sys.argv) > 3 and sys.argv[3] == 'words'
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    kind = lambda t, i: "word_first" if letter(t[i]) and (i == 0 or t[i - 1] in (32, 10)) else ("letter_inside" if letter(t[i]) else "other")
    samples = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        r, n = int(f[0]), int(f[1])
        anchors = [int(a) for a in f[2].split(',') if a]
        source = [None if s == '-' else int(s) for s in f[3].split(',')] if len(f) > 3 and f[3] else []
        text = texts[r][:n]
        if words:
            # the writers' units: a run of non-space bytes with the spaces after it
            anchors = [t for t in range(n) if t == 0 or (text[t] not in (32, 10) and text[t - 1] in (32, 10))]
            source = [None] + [None] * (n - 1)
            for p in range(1, n):
                u = max(k for k, a in enumerate(anchors) if a <= p - 1)
                source[p] = u - 1 if u >= 1 else None
        epoch_of = [0] * n
        for j, a in enumerate(anchors):
            for t in range(a, anchors[j + 1] if j + 1 < len(anchors) else n):
                epoch_of[t] = j
        for p, j in enumerate(source):
            if j is None or p == 0:
                continue
            e = epoch_of[p - 1]
            read = text[anchors[j]:anchors[j + 1] if j + 1 < len(anchors) else n]
            dist = min(p - anchors[e], 15)
            byte = (read[-1] if read else 32) if planted and r % 3 == 0 else text[p]
            samples.append((r % 2 == 0, byte, [(read, dist), (read[-4:], dist), (read[-2:], dist), (read[-1:], dist), ((), dist)], kind(text, p), (r, n + p)))
    orders = 5

    def fit(rows):
        counts = [defaultdict(lambda: defaultdict(int)) for _ in range(orders)]
        uni = defaultdict(int)
        for b, conds in rows:
            uni[b] += 1
            for k, c in enumerate(conds):
                counts[k][c][b] += 1
        return counts, uni

    def coder(model, depth):
        counts, uni = model
        alphabet, total = len(uni) + 1, sum(uni.values())
        p_alone = lambda b: (uni.get(b, 0) + 1) / (total + alphabet)

        def p_given(b, conds):
            p = p_alone(b)
            for k in range(orders - 1, orders - 1 - depth, -1):
                tab = counts[k].get(conds[k])
                if not tab:
                    continue
                c = sum(tab.values())
                p = (max(tab.get(b, 0) - DISCOUNT, 0.0) + DISCOUNT * len(tab) * p) / c
            return p
        return p_given, p_alone

    # How many orders the count uses (the distance alone, then the spelling's last one, two and four bytes, then the whole spelling):
    # the depth whose code is least on the second half of the even rows, counted on the first half.
    even = [(b, conds) for ev, b, conds, _, _ in samples if ev]
    half = len(even) // 2
    model = fit(even[:half])
    held = [sum(-math.log(coder(model, depth)[0](b, conds)) for b, conds in even[half:]) for depth in range(orders + 1)]
    depth = min(range(orders + 1), key=lambda k: held[k])
    p_given, p_alone = coder(fit(even), depth)
    print(f"JOIN_COUNT_DEPTH orders={depth} held_codes_a_place=" + ' '.join(f"{h / max(len(even) - half, 1):.3f}" for h in held))

    # the join's own codes at the same places, where the dump holds them (`face.tsv`: the level face's code and the rest's, 2^(-20) bits)
    face = {}
    try:
        for line in open(f'{d}/face.tsv'):
            f = line.rstrip('\n').split('\t')
            if len(f) > 3:
                face[(int(f[0]), int(f[1]))] = (int(f[2]) * math.log(2) / (1 << 20), int(f[3]) * math.log(2) / (1 << 20))
    except FileNotFoundError:
        pass
    by = defaultdict(lambda: [0.0, 0.0, 0, 0.0, 0.0])
    for even, b, conds, part, site in samples:
        if even or (planted and site[0] % 3 != 0):
            continue
        g = by[part]
        g[0] += -math.log(p_given(b, conds))
        g[1] += -math.log(p_alone(b))
        g[2] += 1
        if site in face:
            g[3] += face[site][0]
            g[4] += face[site][1]
    label = d.rstrip('/').split('/')[-1]
    for part in ("word_first", "letter_inside", "other"):
        R, Z, k, FR, FZ = by[part]
        join = f" join_codes={FR / max(k, 1):.3f}/{FZ / max(k, 1):.3f} join_unsaid_share={FR / FZ:.3f}" if FZ > 0 else ""
        print(f"JOIN_COUNT{'_PLANTED' if planted else ('_WORDS' if words else '')} {label} part={part} places={k} code_given={R / max(k, 1):.3f} code_alone={Z / max(k, 1):.3f} unsaid_share={R / max(Z, 1e-12):.3f}{join}")


if __name__ == '__main__':
    main()
