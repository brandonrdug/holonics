#!/usr/bin/env -S python3 -I
"""level_face_ruler.py DUMP ROWS ALPHABET: a ruler (the lead, November 26, the formal thread's record of nested cycles §9 item 3). Where a
second level would cut her passage, read from her level's own face.

`read-strand-cut ... past face` writes, for passages read by two streams, the known stream's anchors and the epoch each open place reads
(`cut.tsv`), and each open place's code at the level's own face (`face.tsv`: the prolonged row alone through the opening's reader, on
`2^(-20)` bits). This reads, over the rows of `ROWS` (the passage's text):
  - the first level: its epochs, and the share whose anchor is a word's first letter (a letter after a space or a line feed);
  - the unit's news under the level, `C1_j`: the summed face code, in nats, of the open places that read epoch `j`;
  - a second level cut by the same law as the first, on `C1`: an epoch is a site where no larger `C1` stands among the epochs within a
    section of news on either side, the section the first level's own (the flat face's code over the alphabet, ln ALPHABET nats);
  - the second level's units: their count, their lengths in places and in first-level epochs, and the share whose first place is a
    word's first letter, beside the same cut on `C1` shuffled within each row (the ruler's null: a law that finds no word in `C1`
    leaves the shuffled share), beside the unit's news a place that reads it (`per_place`), and on a planted news that peaks at every epoch a word begins (the ruler's proof: it must find them).
Outside the machine; counts and ratios only, floats at the exterior.
"""
import math
import random
import sys
from collections import defaultdict

LN2_20 = math.log(2) / (1 << 20)


def landmarks(news, section):
    """Indices where no larger news stands among the units within a section of news on either side (the law of a level's sites)."""
    out = []
    for j, v in enumerate(news):
        ok, acc, k = True, 0.0, j - 1
        while k >= 0 and acc < section:
            if news[k] > v:
                ok = False
                break
            acc += news[k]
            k -= 1
        acc, k = 0.0, j + 1
        while ok and k < len(news) and acc < section:
            if news[k] > v:
                ok = False
                break
            acc += news[k]
            k += 1
        if ok:
            out.append(j)
    return out


def main():
    d, rows_f, alphabet = sys.argv[1], sys.argv[2], int(sys.argv[3])
    section = math.log(alphabet)
    texts = []
    for line in open(rows_f, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        texts.append((f[1] + f[2]).replace("\\n", "\n").encode())
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    starts = lambda t, i: i < len(t) and letter(t[i]) and (i == 0 or t[i - 1] in (32, 10))
    cuts = {}
    for line in open(f"{d}/cut.tsv"):
        f = line.rstrip("\n").split("\t")
        anchors = [int(a) for a in f[2].split(",") if a]
        source = [None if s == "-" else int(s) for s in f[3].split(",")] if len(f) > 3 and f[3] else []
        cuts[int(f[0])] = (int(f[1]), anchors, source)
    face = defaultdict(dict)
    for line in open(f"{d}/face.tsv"):
        r, site, code = line.rstrip("\n").split("\t")
        face[int(r)][int(site)] = int(code) * LN2_20
    rng = random.Random(26)
    first_n = first_ws = 0
    c1_all, second = [], {"law": [0, 0, [], []], "shuffled": [0, 0, [], []], "planted": [0, 0, [], []], "per_place": [0, 0, [], []]}
    for r, (n, anchors, source) in sorted(cuts.items()):
        t = texts[r][:n]
        first_n += len(anchors)
        first_ws += sum(1 for a in anchors if starts(t, a))
        c1 = [0.0] * len(anchors)
        reads = [0] * len(anchors)
        for p, j in enumerate(source):
            if j is not None and (n + p) in face[r]:
                c1[j] += face[r][n + p]
                reads[j] += 1
        # Beside the law: the unit's news a place that reads it, so a long epoch read by many places weighs no more for its length.
        per_place = [c / k if k else 0.0 for c, k in zip(c1, reads)]
        c1_all += c1
        # The planted law: news that peaks at each epoch whose anchor is a word's first letter, so the cut must find the words.
        planted = [(6.0 if starts(t, a) else 1.0) for a in anchors]
        for name, news in (("law", c1), ("shuffled", rng.sample(c1, len(c1))), ("planted", planted), ("per_place", per_place)):
            sites = landmarks(news, section)
            g = second[name]
            g[0] += len(sites)
            g[1] += sum(1 for j in sites if starts(t, anchors[j]))
            for a, b in zip(sites, sites[1:] + [len(anchors)]):
                g[2].append((anchors[b] if b < len(anchors) else n) - anchors[a])
                g[3].append(b - a)
    med = lambda v: sorted(v)[len(v) // 2] if v else 0
    print(f"LEVEL_FACE rows={len(cuts)} first_epochs={first_n} first_word_start_share={first_ws / max(first_n, 1):.3f} "
          f"c1_nats_median={med(c1_all):.2f} c1_nats_mean={sum(c1_all) / max(len(c1_all), 1):.2f} section_nats={section:.3f}")
    for name, (count, ws, places, epochs) in second.items():
        print(f"LEVEL_FACE_SECOND {name} units={count} word_start_share={ws / max(count, 1):.3f} places_median={med(places)} "
              f"places_mean={sum(places) / max(len(places), 1):.1f} first_epochs_median={med(epochs)}")


if __name__ == "__main__":
    main()
