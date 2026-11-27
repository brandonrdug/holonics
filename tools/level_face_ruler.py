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
  - [the formal thread's law, November 26 23:50 UTC] the second level cut on the share the join left unsaid, `n_u = R_u / Z_u`: `R_u`
    the level face's code of unit `u`'s places (each read from unit `u − 1`'s row carried across the join), `Z_u` the same places'
    codes through the same reader from the row at rest (`face.tsv`'s fourth column); its clock `S2 = Σ n`, its section one unit (a
    unit the join told nothing has `n = 1`, so no number is handed in); a site is a unit whose `n` stands above every unit within one
    unit of `S2` on either side, and a unit the past misleads (`n > 1`) is always a site (`join`), beside the same cut on `n` shuffled
    within each row (`join_shuffled`) and on a planted share over one at each unit a word begins (`join_planted`), and the join's share
    a place by the place's kind and a unit's by its anchor's (`LEVEL_FACE_JOIN_PART`); each with its share of phrase starts (a word's first letter after `.,;:!?` or a line feed, or at
    the row's start) beside the words'.
A unit `u` is the first level's epoch `u`: an open place at place `p` stands in the epoch of the place before it and reads the epoch
before that (`cut.tsv`'s fourth field, the open places' epochs read), so the places that read epoch `j` are unit `j + 1`'s, and a
unit's news stands at unit `j + 1`'s anchor (until November 26 23:55 UTC this ruler set it at epoch `j`'s, one unit early).
Outside the machine; counts and ratios only, floats at the exterior.
"""
import math
import random
import sys
from collections import defaultdict

LN2_20 = math.log(2) / (1 << 20)


def landmarks(news, section, clock=None, misled=None):
    """Indices where no larger news stands among the units within a section of the clock on either side (the law of a level's sites).
    `clock` is each unit's stride on the clock (its news where none is given); a unit whose news stands over `misled` is always a site."""
    clock = news if clock is None else clock
    out = []
    for j, v in enumerate(news):
        if misled is not None and v > misled:
            out.append(j)
            continue
        ok, acc, k = True, 0.0, j - 1
        while k >= 0 and acc < section:
            if news[k] > v:
                ok = False
                break
            acc += clock[k]
            k -= 1
        acc, k = 0.0, j + 1
        while ok and k < len(news) and acc < section:
            if news[k] > v:
                ok = False
                break
            acc += clock[k]
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

    def phrase(t, i):
        if not starts(t, i):
            return False
        k = i - 1
        while k >= 0 and t[k] == 32:
            k -= 1
        return k < 0 or t[k] in b".,;:!?\n"

    cuts = {}
    for line in open(f"{d}/cut.tsv"):
        f = line.rstrip("\n").split("\t")
        anchors = [int(a) for a in f[2].split(",") if a]
        source = [None if s == "-" else int(s) for s in f[3].split(",")] if len(f) > 3 and f[3] else []
        cuts[int(f[0])] = (int(f[1]), anchors, source)
    face, rest = defaultdict(dict), defaultdict(dict)
    for line in open(f"{d}/face.tsv"):
        f = line.rstrip("\n").split("\t")
        face[int(f[0])][int(f[1])] = int(f[2]) * LN2_20
        if len(f) > 3:
            rest[int(f[0])][int(f[1])] = int(f[3]) * LN2_20
    rng = random.Random(26)
    first_n = first_ws = 0
    names = ("law", "shuffled", "planted", "per_place", "join", "join_shuffled", "join_planted")
    # The join's share a place, by the place's kind (a word's first letter, a letter inside a word, any other byte), and a unit's by
    # the kind of its anchor.
    place_share, unit_share = defaultdict(list), defaultdict(list)
    kind = lambda t, i: "word_first" if starts(t, i) else ("letter_inside" if i < len(t) and letter(t[i]) else "other")
    c1_all, n_all = [], []
    second = {k: [0, 0, 0, [], []] for k in names}
    for r, (n, anchors, source) in sorted(cuts.items()):
        t = texts[r][:n]
        first_n += len(anchors)
        first_ws += sum(1 for a in anchors if starts(t, a))
        units = len(anchors)
        c1, z1 = [0.0] * units, [0.0] * units
        reads = [0] * units
        for p, j in enumerate(source):
            if j is None or j + 1 >= units or (n + p) not in face[r]:
                continue
            c1[j + 1] += face[r][n + p]
            z1[j + 1] += rest[r].get(n + p, 0.0)
            reads[j + 1] += 1
            if rest[r].get(n + p, 0.0) > 0:
                place_share[kind(t, p)].append(face[r][n + p] / rest[r][n + p])
        # Unit 0 reads no epoch before it, and has no news under the level: it stands aside from every cut.
        c1, z1, reads, anchors_u = c1[1:], z1[1:], reads[1:], anchors[1:]
        if not anchors_u:
            continue
        per_place = [c / k if k else 0.0 for c, k in zip(c1, reads)]
        nu = [c / z if z > 0 else 1.0 for c, z in zip(c1, z1)]
        c1_all += c1
        n_all += [v for v, z in zip(nu, z1) if z > 0]
        planted = [(6.0 if starts(t, a) else 1.0) for a in anchors_u]
        shuffled_nu = rng.sample(nu, len(nu))
        # The join's planted law: a share over one at each unit a word begins and under it elsewhere, so its cut must find the words.
        planted_nu = [1.2 if starts(t, a) else 0.4 + 0.2 * rng.random() for a in anchors_u]
        for a, v, z in zip(anchors_u, nu, z1):
            if z > 0:
                unit_share["unit_" + kind(t, a)].append(v)
        for name, news, clock, misled, sec in (("law", c1, None, None, section), ("shuffled", rng.sample(c1, len(c1)), None, None, section),
                                               ("planted", planted, None, None, section), ("per_place", per_place, None, None, section),
                                               ("join", nu, nu, 1.0, 1.0), ("join_shuffled", shuffled_nu, shuffled_nu, 1.0, 1.0),
                                               ("join_planted", planted_nu, planted_nu, 1.0, 1.0)):
            sites = landmarks(news, sec, clock, misled)
            g = second[name]
            g[0] += len(sites)
            g[1] += sum(1 for j in sites if starts(t, anchors_u[j]))
            g[2] += sum(1 for j in sites if phrase(t, anchors_u[j]))
            for a, b in zip(sites, sites[1:] + [len(anchors_u)]):
                g[3].append((anchors_u[b] if b < len(anchors_u) else n) - anchors_u[a])
                g[4].append(b - a)
    med = lambda v: sorted(v)[len(v) // 2] if v else 0
    print(f"LEVEL_FACE rows={len(cuts)} first_epochs={first_n} first_word_start_share={first_ws / max(first_n, 1):.3f} "
          f"c1_nats_median={med(c1_all):.2f} c1_nats_mean={sum(c1_all) / max(len(c1_all), 1):.2f} section_nats={section:.3f}")
    if n_all:
        q = sorted(n_all)
        print(f"LEVEL_FACE_JOIN units={len(q)} n_median={med(q):.3f} n_p10={q[len(q) // 10]:.3f} n_p90={q[9 * len(q) // 10]:.3f} "
              f"misled_share={sum(1 for v in q if v > 1) / len(q):.3f}")
    for k, v in sorted(place_share.items()) + sorted(unit_share.items()):
        q = sorted(v)
        print(f"LEVEL_FACE_JOIN_PART {k} count={len(q)} share_median={med(q):.3f} share_mean={sum(q) / len(q):.3f} misled_share={sum(1 for x in q if x > 1) / len(q):.3f}")
    for name, (count, ws, ps, places, epochs) in second.items():
        print(f"LEVEL_FACE_SECOND {name} units={count} word_start_share={ws / max(count, 1):.3f} phrase_start_share={ps / max(count, 1):.3f} "
              f"places_median={med(places)} places_mean={sum(places) / max(len(places), 1):.1f} first_epochs_median={med(epochs)}")


if __name__ == "__main__":
    main()
