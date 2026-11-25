#!/usr/bin/env python3
"""[measurement; the formal thread, November 24] Cuts of the lead's tension reads of a ring's fade, from codes already read.

    fade_cuts.py ROWS.tsv RUN_DIR [RUN_DIR ...]

A ruler on the host, and no part of the machine: it reads tables and writes nothing.

ROWS is the lead's table of rows (`label<TAB>text<TAB>...`, a line feed written `\\n`): rows `period:{kept|loose}:{P1}:{i}` as
`known_cuts.py` beside this file reads them (a kept row is drawn letters in words of `L = P1 - 1` letters, each followed by a
space; its loose twin cuts the same letters into words of `L - 1`, `L` or `L + 1`), and rows `held:{register}:{i}`, stretches of
held text. Each RUN_DIR holds `read-reach`'s `codes.tsv` (`row`, `group`, `place`, then a code a setting on `2^(-20)` bits, every
place at its own frontier) and `settings.tsv`, a setting a line, the first of them `law`. A setting `fade:FROM:MILLI` reads the
rings of period `FROM` and longer at a fade `2^(MILLI/1000)` of the skin's, and `skin:places` counts the skin's distance in
places. A place is a byte of a row's text. Every figure but FADE_LAW's is a setting's code less the law's at the same places,
in nats.

Why the cuts. A kept row's separators getting cheaper under a slower fade say that a period is timed better only if its twin's
separators after the same count of letters do not get cheaper by as much: the twin shows no period, so what the two share is a
change in her code of a separator on rows of that word length, and their difference is the change in what the shown period
gives her. On held text the question is whether any kind of place gains, since a fade read from a site's state can only pay where
some kind of site does.

  FADE_HELD        a setting's code less the law's on the held rows: every place, then by the kind of the place coded (a space,
                   a line feed, an ASCII letter, a digit, any other byte), with each count of places.
  FADE_HELD_RUN    the same at a space and at a letter, by the count of bytes since the last separator (0 to 2, 3 to 5, 6 to 8,
                   9 or more).
  FADE_LAW         P1; the law's own codes over a row's places from 200, a row's mean averaged over rows: the kept
                   separators, the twin's after `L - 1`, `L` and `L + 1` letters, the letters of the kept rows and of the
                   twins, and `ln P1`, the code of a reader that holds the separators' rate and no place in the period. A
                   reader that counts the letters since the last separator codes the twin's three at `ln 3`, `ln 2` and 0.
  FADE_PAIRED      P1; over a row's places from 200, a row's mean change at its separators after `L` letters, averaged over
                   rows, kept and twin; the twin's less the kept's, the change in the period's gain, with its standard error
                   over rows; the twin's change at its separators after `L - 1` and `L + 1` letters; the change at the
                   letters of the kept rows and of the twins; and `opens`, a twin row's change after `L - 1` letters less
                   its change after `L + 1`, averaged over rows with its standard error over rows: how far the setting opens
                   the twin's code of a separator across the count of letters since the last one (a reader of that count
                   holds it open by `ln 3`).
  FADE_POOLED      the change in the period's gain averaged over the lengths with P1 at most 5 and over those from 7, each with
                   the standard error of that average from the lengths' own.
  FADE_STATIONARY  for settings `fade:F:-M` and `fade:F:M` in one RUN_DIR: the parabola through their two changes on the held
                   rows and the law's zero, its stationary point in thousandths of an octave of the fade, and its code there
                   less the law's.
"""
import collections
import math
import os
import sys


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def spread(xs):
    k = len(xs)
    if k < 2:
        return float("nan")
    mu = mean(xs)
    return (sum((x - mu) ** 2 for x in xs) / (k - 1) / k) ** 0.5


def kind_of(b):
    if b == 0x20:
        return "space"
    if b == 0x0A:
        return "feed"
    if (0x41 <= b <= 0x5A) or (0x61 <= b <= 0x7A):
        return "letter"
    if 0x30 <= b <= 0x39:
        return "digit"
    return "other"


def bucket(run):
    return "0-2" if run <= 2 else "3-5" if run <= 5 else "6-8" if run <= 8 else "9+"


def cut(rows, run_dir):
    with open(os.path.join(run_dir, "settings.tsv"), encoding="utf-8") as f:
        settings = [line.strip() for line in f if line.strip()]
    count = len(settings)
    codes = {}
    with open(os.path.join(run_dir, "codes.tsv"), encoding="utf-8") as f:
        for line in f:
            w = line.rstrip("\n").split("\t")
            codes[(int(w[0]), int(w[2]))] = [int(x) / 2**20 * math.log(2) for x in w[3:3 + count]]
    held = collections.defaultdict(lambda: [0.0] * count)      # kind or (kind, bucket) -> a setting's summed change
    held_n = collections.Counter()
    paired = collections.defaultdict(lambda: [[] for _ in range(count)])   # (kind of row, P1, letters before) -> a row's mean change
    law = collections.defaultdict(list)                                    # (kind of row, P1, letters before) -> a row's mean code
    opens = collections.defaultdict(lambda: [[] for _ in range(count)])    # P1 -> a twin row's change after L - 1 less after L + 1
    for r, (label, text) in enumerate(rows):
        parts = label.split(":")
        run = 0
        if parts[0] == "held":
            for p, b in enumerate(text):
                c = codes.get((r, p))
                kind = kind_of(b)
                if c is not None:
                    keys = ["all", kind] + ([(kind, bucket(run))] if kind in ("space", "letter") else [])
                    for key in keys:
                        held_n[key] += 1
                        for s in range(count):
                            held[key][s] += c[s] - c[0]
                run = 0 if kind in ("space", "feed") else run + 1
            continue
        p1 = int(parts[2])
        tail = collections.defaultdict(lambda: [[] for _ in range(count)])
        level = collections.defaultdict(list)
        for p, b in enumerate(text):
            c = codes.get((r, p))
            letter = b not in (0x20, 0x0A)
            if c is not None and p >= 200:
                at = "letter" if letter else run
                level[at].append(c[0])
                for s in range(count):
                    tail[at][s].append(c[s] - c[0])
            run = run + 1 if letter else 0
        if parts[1] == "loose" and p1 - 2 in tail and p1 in tail:
            for s in range(count):
                opens[p1][s].append(mean(tail[p1 - 2][s]) - mean(tail[p1][s]))
        for n, per in tail.items():
            law[(parts[1], p1, n)].append(mean(level[n]))
            for s in range(count):
                paired[(parts[1], p1, n)][s].append(mean(per[s]))
    periods = sorted({k[1] for k in paired})
    name = os.path.basename(os.path.normpath(run_dir))
    print(f"FADE run={name} settings={','.join(settings)} codes={len(codes)} held_places={held_n['all']}")
    for p1 in periods:
        length = p1 - 1
        twin = " ".join(f"{mean(law[('loose', p1, n)]):.3f}" for n in (length - 1, length, length + 1))
        print(f"FADE_LAW run={name} P1={p1} kept={mean(law[('kept', p1, length)]):.3f} twin={twin} letters={mean(law[('kept', p1, 'letter')]):.3f} {mean(law[('loose', p1, 'letter')]):.3f} ln_P1={math.log(p1):.3f}")
    for s in range(1, count):
        tag = f"run={name} setting={settings[s]}"
        cells = " ".join(f"{k}={held[k][s] / held_n[k]:+.4f}({held_n[k]})" for k in ("all", "space", "feed", "letter", "digit", "other") if held_n[k])
        print(f"FADE_HELD {tag} {cells}")
        cells = " ".join(f"{k}:{b}={held[(k, b)][s] / held_n[(k, b)]:+.4f}({held_n[(k, b)]})" for k in ("space", "letter") for b in ("0-2", "3-5", "6-8", "9+") if held_n[(k, b)])
        print(f"FADE_HELD_RUN {tag} {cells}")
        changes = {}
        for p1 in periods:
            length = p1 - 1
            kept, twin = paired[("kept", p1, length)][s], paired[("loose", p1, length)][s]
            changes[p1] = (mean(twin) - mean(kept), (spread(twin) ** 2 + spread(kept) ** 2) ** 0.5)
            around = " ".join(f"{mean(paired[('loose', p1, n)][s]):+.3f}" for n in (length - 1, length + 1))
            letters = f"{mean(paired[('kept', p1, 'letter')][s]):+.3f} {mean(paired[('loose', p1, 'letter')][s]):+.3f}"
            print(f"FADE_PAIRED {tag} P1={p1} kept={mean(kept):+.3f} twin={mean(twin):+.3f} change={changes[p1][0]:+.3f} se={changes[p1][1]:.3f} twin_around={around} letters={letters} opens={mean(opens[p1][s]):+.3f}({spread(opens[p1][s]):.3f})")
        cells = []
        for label, group in (("P1<=5", [p for p in periods if p <= 5]), ("P1>=7", [p for p in periods if p >= 7])):
            if group:
                cells.append(f"{label} change={mean([changes[p][0] for p in group]):+.3f} se={sum(changes[p][1] ** 2 for p in group) ** 0.5 / len(group):.3f}")
        print(f"FADE_POOLED {tag} " + " ".join(cells))
    at = {}
    for s in range(1, count):
        w = settings[s].split(":")
        if w[0] == "fade" and len(w) == 3 and held_n["all"]:
            at[(w[1], int(w[2]))] = held["all"][s] / held_n["all"]
    for (ring, milli), up in sorted(at.items()):
        if milli > 0 and (ring, -milli) in at and up + at[(ring, -milli)] != 0:
            down = at[(ring, -milli)]
            point = -milli * (up - down) / (2 * (up + down))
            print(f"FADE_STATIONARY run={name} from={ring} step={milli} down={down:+.4f} up={up:+.4f} at={point:+.0f} code={-(up - down) ** 2 / (8 * (up + down)):+.4f}")


def main(rows_path, run_dirs):
    rows = []
    with open(rows_path, encoding="utf-8") as f:
        for line in f:
            w = line.rstrip("\n").split("\t")
            rows.append((w[0], w[1].replace("\\n", "\n").encode("utf-8")))
    for run_dir in run_dirs:
        cut(rows, run_dir)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2:])
