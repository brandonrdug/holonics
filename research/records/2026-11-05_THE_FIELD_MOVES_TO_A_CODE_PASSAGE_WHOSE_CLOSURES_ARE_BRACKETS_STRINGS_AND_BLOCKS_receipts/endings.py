#!/usr/bin/env python3
"""Where the writer ends against held (the unified-theory reading of November 5, 21:19, fixed before b1's read).

Usage: endings.py HELD.txt SAMPLE.tsv ROOM

For each written answer of w bytes beside its held answer of h bytes: the places written at or under held are min(w, h),
those past held max(w - h, 0); an answer ending at w <= h ends at or under held, one ending at h < w < ROOM ends past it, and
one reaching the room ends nowhere (censored). The hazard is ends over places written there; the ratio past over under is
the sharp read (a sense of length makes it several times one; memoryless writing makes it one or less). Beside it the
correlation of written with held bytes and their ratio. Aggregates only.
"""
import statistics
import sys


def records(path):
    out = []
    for r in open(path, "rb").read().split(b"\x1e"):
        if b"\x1f" in r:
            out.append(r.split(b"\x1f", 1)[1])
    return out


def main():
    held, room = records(sys.argv[1]), int(sys.argv[3])
    pairs = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            w = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace")
            pairs.append((len(w), len(held[int(k)])))
    under_places = sum(min(w, h) for w, h in pairs)
    past_places = sum(max(w - h, 0) for w, h in pairs)
    under = sum(w <= h for w, h in pairs)
    past = sum(h < w < room for w, h in pairs)
    censored = sum(w >= room for w, h in pairs)
    hu = under / under_places if under_places else float("nan")
    hp = past / past_places if past_places else float("nan")
    ratio = hp / hu if hu else float("nan")
    ws, hs = [w for w, _ in pairs], [h for _, h in pairs]
    corr = statistics.correlation(ws, hs) if len(pairs) > 2 else float("nan")
    print(f"ENDINGS answers {len(pairs)}: {under} end at or under held over {under_places} places (one in {under_places / max(under, 1):.0f}), {past} past it over {past_places} (one in {past_places / max(past, 1):.0f}), {censored} reach the room")
    print(f"HAZARD past/under {ratio:.2f}; written/held {sum(ws) / sum(hs):.3f}; correlation {corr:+.3f}")


if __name__ == "__main__":
    main()
