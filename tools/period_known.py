#!/usr/bin/env -S python3 -I
"""Does her store keep a period it is shown? A ruler on the host, read on known text (the lead, November 24; the formal thread's
20:49Z note on the period panel: "the read that would tell is her face on the reference laid out as known text").

Usage: python3 tools/period_known.py make ROWS.tsv PLACES.tsv [SEED [ROWS_EACH [L,L,...]]]
       python3 tools/period_known.py read CODES_DIR PLACES.tsv

`make` writes rows for `athena ... read-reach` (`label<TAB>text<TAB>`) and the places to read. Each row is a stretch of drawn lowercase
words, a space after each. In a `kept` row every word has `L` letters, so a separator stands every `P1 = L + 1` places; in its
`loose` twin the same letters are cut into words of `L − 1`, `L` or `L + 1` letters drawn anew (the mean length the same), so a
separator stands at no period. The places read are the separators of the row's last third (each a place whose code is its
surprise, read by two streams with every place before it known), and the letters there. A store that keeps `P1` codes a kept row's
separators below its loose twin's; one that hears only the near field codes them alike once `P1` passes it.

`read` reads read-reach's `codes.tsv` at those places and prints, a line a `P1`, the mean code in nats of the separators and of the
letters in kept and in loose rows, and `kept − loose` at the separators (negative where the period is kept). It reads no state of
its own and refuses nothing; its rows are drawn by `random.Random(SEED)` alone and hold no text of anyone's.
"""
import collections
import math
import random
import sys

LENGTHS = (2, 3, 4, 6, 8, 9, 14, 15)  # P1 = 3, 4, 5, 7, 9, 10, 15, 16: on her rings' periods (3, 4, 9, 16) and off them
ROWS_EACH = 16
SPAN = 300
LETTERS = "abcdefghijklmnopqrstuvwxyz"


def make(rows_path, places_path, seed, rows_each=ROWS_EACH, lengths=LENGTHS):
    rng = random.Random(seed)
    rows, places = [], []
    for L in lengths:
        for i in range(rows_each):
            letters = [rng.choice(LETTERS) for _ in range(SPAN)]
            for kind in ("kept", "loose"):
                text, seps, at = [], [], 0
                cut = random.Random(seed * 1000 + L * 37 + i)
                while len(text) < SPAN:
                    n = L if kind == "kept" else max(1, L + cut.choice((-1, 0, 1)))
                    for _ in range(n):
                        text.append(letters[at % SPAN]); at += 1
                    seps.append(len(text)); text.append(" ")
                text = text[:SPAN]
                r = len(rows)
                rows.append((f"period:{kind}:{L + 1}:{i}", "".join(text)))
                tail = SPAN * 2 // 3
                for p in range(tail, SPAN):
                    places.append((r, kind, L + 1, p, "sep" if text[p] == " " else "letter"))
    with open(rows_path, "w") as f:
        for label, text in rows:
            f.write(f"{label}\t{text}\t\n")
    with open(places_path, "w") as f:
        for r, kind, p1, p, what in places:
            f.write(f"{r}\t{kind}\t{p1}\t{p}\t{what}\n")
    print(f"PERIOD_KNOWN_MADE rows={len(rows)} places={len(places)} seed={seed}")


def read(codes_dir, places_path):
    settings = [l.strip() for l in open(f"{codes_dir}/settings.tsv") if l.strip()]
    code = {}
    for line in open(f"{codes_dir}/codes.tsv"):
        f = line.rstrip("\n").split("\t")
        code[(int(f[0]), int(f[2]))] = [int(v) for v in f[3:]]
    for si, setting in enumerate(settings):
        by = collections.defaultdict(lambda: [0, 0.0])
        for line in open(places_path):
            r, kind, p1, p, what = line.rstrip("\n").split("\t")
            c = code.get((int(r), int(p)))
            if c is None:
                continue
            b = by[(int(p1), kind, what)]
            b[0] += 1
            b[1] += c[si] / 2 ** 20 * math.log(2)
        mean = lambda k: by[k][1] / by[k][0] if by[k][0] else float("nan")
        for p1 in sorted({k[0] for k in by}):
            ks, ls = mean((p1, "kept", "sep")), mean((p1, "loose", "sep"))
            kl, ll = mean((p1, "kept", "letter")), mean((p1, "loose", "letter"))
            print(f"PERIOD_KNOWN {setting} P1={p1:2d} sep kept {ks:.3f} loose {ls:.3f} kept-loose {ks - ls:+.3f} (n {by[(p1, 'kept', 'sep')][0]}, "
                  f"{by[(p1, 'loose', 'sep')][0]}) | letter kept {kl:.3f} loose {ll:.3f}")


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "make":
        make(sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 24, int(sys.argv[5]) if len(sys.argv) > 5 else ROWS_EACH, tuple(int(v) for v in sys.argv[6].split(",")) if len(sys.argv) > 6 else LENGTHS)
    elif len(sys.argv) == 4 and sys.argv[1] == "read":
        read(sys.argv[2], sys.argv[3])
    else:
        sys.exit(__doc__)
