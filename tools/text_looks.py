"""Read a tower's LOOKS.tsv (read-lines-again over any text) by the lock alone, the micro-control's
§7 reading, with nothing particular to a medium: for the lines whose whole line the training text
holds verbatim (met) and the lines it does not (unmet), the line count, the true rests' bytes `ΣT`
(each rest with its line end), `Σλ` and `ΣF*` at the first look and the last (`λ` the longest
order-consistent coupling of a look with the true rest, `F* = |H| + |T| − 2λ` its friction), and how
many lines' locks held or grew (`λ` up or equal and `F*` down or equal) from the first look to the
last and how many fell. `λ / ΣT` is the share of the true rests the looks hold in order. The head
and rest fields are read back to their bytes (`read_lines` writes them escaped). An exterior
reading, outside the machine.

usage: python3 -I text_looks.py TRAIN_TXT LOOKS_TSV
"""
import codecs
import sys
from collections import defaultdict

FIELDS = ("lines", "ΣT", "first λ", "last λ", "first F*", "last F*", "held or grew", "fell")


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    train = set(open(sys.argv[1], "rb").read().split(b"\n"))
    rows = defaultdict(lambda: defaultdict(int))
    for row in open(sys.argv[2], "rb"):
        cols = row.rstrip(b"\n").split(b"\t")
        head, rest = (codecs.escape_decode(c)[0] for c in cols[1:3])
        lam = [int(v) for v in cols[6].split(b"|")]
        fr = [int(v) for v in cols[7].split(b"|")]
        k = rows["met" if head + rest in train else "unmet"]
        k["lines"] += 1
        k["ΣT"] += len(rest) + 1
        k["first λ"] += lam[0]
        k["last λ"] += lam[-1]
        k["first F*"] += fr[0]
        k["last F*"] += fr[-1]
        k["held or grew"] += lam[-1] >= lam[0] and fr[-1] <= fr[0]
        k["fell"] += lam[-1] < lam[0] or fr[-1] > fr[0]
    print("part\t" + "\t".join(FIELDS))
    for part in ("met", "unmet"):
        print(part + "\t" + "\t".join(str(rows[part][f]) for f in FIELDS))


if __name__ == "__main__":
    main()
