#!/usr/bin/env -S python3 -I
"""A sampled wave as a slice of a store: the boundary chart that reads a sample as its rank among levels of equal mass.

One stream law reads every passage, so nothing here names what a wave is a recording of. The boundary states two things, the
alphabet's width and whose clock drew the samples, and keeps what the chart holds back.

  chart      r(x) = #{j : c_j <= x},  c_1 < ... < c_(K-1) located on the training samples:  c_j the least value v with
             K * #{x < v} >= j * N  (K levels of equal mass, as near as whole samples allow; integers throughout)
  symbol     one a sample, at the source's own clock: level r is written as the octet o_r, the octets ascending with the level
  remainder  x - low_r,  low_0 the least value a sample takes, low_r = c_r;  chart and remainder return the sample:
             x = low_r + remainder
  held       a group (one voice, one instrument: whose clock and whose hand) is held where the first eight hex digits of its
             name's SHA-256, read as a number, divide by HELD_ONE_IN; its documents never train, and the chart is located
             without them

Why one symbol a sample and K levels (the record of November 25, section 10): the octets are by default the thirteen that no
UTF-8 text holds (C0, C1, F5 to FF), so no level shares a class with a letter and a learner grows its alphabet by them as it did at
the store's crossing (`Codec::extended`, `Constitution::lettered`), with no chart of its own in the engine. A count ruler
(`levels_ruler.py` in that record's receipts) read what a level tells of the level n places back at 3, 9, 13 and 16 levels: thirteen
hold 0.95 to 0.96 of sixteen's, nine 0.85 to 0.88, three 0.41 to 0.44. The value-word design of November 12 (a word of rank digits
whose radix a ruler on a paired port fixes, atlas `compression.value-word-rank-registers`) differs: it sends several digits a value,
and this chart sends the first register alone and keeps the rest as its remainder, because a second digit a sample halves what a
region spans and no paired port stands to fix a radix by.

Usage:
  wave_passage.py write OUT LISTING NAME SECONDS HELD HELD_ONE_IN [--octets HEX,HEX,...] [--remainder]
  wave_passage.py check OUT NAME
  wave_passage.py join STORE OUT NEW NAME

`write` reads LISTING, rows `id TAB group TAB path` (a fourth field, a rate in samples a second, marks a path of raw 16-bit
little-endian samples; every other path is decoded by ffmpeg at its own clock and refused unless it holds one channel at the
clock of the first; sources are decoded a few at once and read in order). Documents are read in the order of their id's SHA-256. The training documents are those of the groups not
held, taken whole until SECONDS of them stand; the held documents are the first HELD of the held groups'. It writes the slice
NAME under OUT in `corpus_passage.py`'s form (`DOCS_NAME.bin`, `DOCS_NAME.tsv`, `IDS_NAME.txt` and the `HELD_` three; a document
is one piece that opens and closes, with no title, so a source's end is a true end), the chart `CHART_NAME.tsv` (level, octet,
low, high, count), the boundary's statement `BOUNDARY_NAME.tsv` (the clock, the width, the counts, the SHA-256 of the samples
each role covers) and, with `--remainder`, `REMAINDER_NAME.bin` and `HELD_REMAINDER_NAME.bin` (16 bits a sample, little-endian).
It prints the slice's `STORE.tsv` rows. A level no sample falls in is refused (an atom wider than a level takes a level of its
own in the value-word design, which this chart does not build).

`check` rebuilds each role's samples from the slice, the chart and the remainder and compares their SHA-256 with the boundary's.
`join` writes the store NEW: every file of STORE hard-linked but `STORE.tsv`, the slice's files hard-linked from OUT, and
`STORE.tsv` with the slice's rows after the store's own. Outside the machine: a boundary codec, and no sample is changed.
"""
import concurrent.futures
import hashlib
import os
import subprocess
import sys

import numpy as np

INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"
STORE_HEAD = "role\tslice\tshare\tline_floor\tdocuments\tpieces\ttext_octets\tstore_octets\tsha256\n"
CHART_HEAD = "level\toctet\tlow\thigh\tcount\n"
# The octets no UTF-8 text holds: C0 and C1 (overlong lead bytes) and F5 to FF (past the last code point).
FREE_OCTETS = (0xC0, 0xC1) + tuple(range(0xF5, 0x100))
LEAST, PAST = -32768, 32768  # a 16-bit sample's least value and the value past its greatest


def key(name):
    return hashlib.sha256(name.encode("utf-8")).hexdigest()


def held_group(group, one_in):
    return int(key(group)[:8], 16) % one_in == 0


def listing_of(path):
    """A listing's rows as (id, group, path, rate or None), in the order of the id's SHA-256."""
    rows = []
    for n, line in enumerate(open(path, encoding="utf-8").read().split("\n")):
        if not line:
            continue
        w = line.split("\t")
        if len(w) not in (3, 4):
            sys.exit(f"{path} row {n + 1}: not id, group, path and at most a rate")
        rows.append((w[0], w[1], w[2], int(w[3]) if len(w) == 4 else None))
    if len({r[0] for r in rows}) != len(rows):
        sys.exit(f"{path} holds an id twice")
    return sorted(rows, key=lambda r: key(r[0]))


def samples_of(row):
    """A source's samples (16 bits, one channel) and its clock in samples a second."""
    _, _, path, rate = row
    if rate is not None:
        return np.fromfile(path, dtype="<i2"), rate
    wav = subprocess.run(["ffmpeg", "-v", "error", "-i", path, "-map_metadata", "-1", "-bitexact", "-c:a", "pcm_s16le", "-f", "wav", "-"],
                         capture_output=True, check=True).stdout
    # The decoder's container: `RIFF` size `WAVE`, then chunks (four letters, a 32-bit length, the body); `fmt ` states the channels
    # and the clock, and `data` is the samples to the end (a piped container's lengths are not filled in).
    if wav[:4] != b"RIFF" or wav[8:12] != b"WAVE":
        sys.exit(f"{path}: the decoder returned no samples")
    at, channels, clock = 12, None, None
    while at + 8 <= len(wav):
        tag, length = wav[at:at + 4], int.from_bytes(wav[at + 4:at + 8], "little")
        if tag == b"fmt ":
            channels, clock = int.from_bytes(wav[at + 10:at + 12], "little"), int.from_bytes(wav[at + 12:at + 16], "little")
        if tag == b"data":
            if channels != 1:
                sys.exit(f"{path}: not one channel ({channels})")
            body = wav[at + 8:]
            return np.frombuffer(body, dtype="<i2", count=len(body) // 2), clock
        at += 8 + length + (length & 1)
    sys.exit(f"{path}: the decoder returned no samples")


def read_role(rows, clock, limit):
    """The role's documents in order: yields (id, samples), refusing a source at another clock; stops once `limit` samples stand
    (None: every row). Sources are decoded a few at once, on the host's threads, and read in the listing's order."""
    got = 0
    workers = os.cpu_count() or 1
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for k in range(0, len(rows), 4 * workers):
            batch = rows[k:k + 4 * workers]
            for row, (x, rate) in zip(batch, pool.map(samples_of, batch)):
                if limit is not None and got >= limit:
                    return
                if clock[0] is None:
                    clock[0] = rate
                if rate != clock[0]:
                    sys.exit(f"{row[2]}: drawn at {rate} samples a second where the first source was drawn at {clock[0]}")
                if len(x) == 0:
                    continue
                got += len(x)
                yield row[0], x


def cuts_of(hist, levels):
    """The chart's cuts from the samples' histogram over the 65,536 values: c_j the least value v with K * #{x < v} >= j * N."""
    total = int(hist.sum())
    below = np.concatenate(([0], np.cumsum(hist)[:-1])).astype(np.int64)  # below[i] = #{x < i + LEAST}
    cuts = [int(np.searchsorted(below * levels, j * total, side="left")) + LEAST for j in range(1, levels)]
    return cuts, total


def chart_rows(cuts, hist):
    lows = [LEAST] + cuts
    highs = cuts + [PAST]
    return [(lo, hi, int(hist[lo - LEAST:hi - LEAST].sum())) for lo, hi in zip(lows, highs)]


class Role:
    """A role's files while they are written."""

    def __init__(self, out, stem, name, remainder):
        ids_stem = "HELD_IDS" if stem == "HELD" else "IDS"
        rem_stem = "HELD_REMAINDER" if stem == "HELD" else "REMAINDER"
        self.bin = open(os.path.join(out, f"{stem}_{name}.bin"), "xb")
        self.tsv = open(os.path.join(out, f"{stem}_{name}.tsv"), "x")
        self.ids = open(os.path.join(out, f"{ids_stem}_{name}.txt"), "x")
        self.rem = open(os.path.join(out, f"{rem_stem}_{name}.bin"), "xb") if remainder else None
        self.tsv.write(INDEX_HEAD)
        self.sha, self.pcm = hashlib.sha256(), hashlib.sha256()
        self.documents = self.octets = 0

    def add(self, ident, x, cuts, octets):
        level = np.searchsorted(np.asarray(cuts, dtype=np.int64), x, side="right")
        body = np.asarray(octets, dtype=np.uint8)[level].tobytes()
        self.bin.write(body)
        self.sha.update(body)
        self.pcm.update(x.astype("<i2").tobytes())
        if self.rem:
            low = np.asarray([LEAST] + cuts, dtype=np.int64)[level]
            self.rem.write((x.astype(np.int64) - low).astype("<u2").tobytes())
        self.tsv.write(f"{self.documents}\t0\t{len(x)}\t1\t1\n")
        self.ids.write(ident.replace("\n", " ") + "\n")
        self.documents += 1
        self.octets += len(x)

    def close(self):
        for f in (self.bin, self.tsv, self.ids, self.rem):
            if f:
                f.close()

    def row(self, role, name):
        return f"{role}\t{name}\t0\t0\t{self.documents}\t{self.documents}\t{self.octets}\t{self.octets}\t{self.sha.hexdigest()}"


def write(out, listing, name, seconds, held, one_in, octets, remainder):
    rows = listing_of(listing)
    train_rows = [r for r in rows if not held_group(r[1], one_in)]
    held_rows = [r for r in rows if held_group(r[1], one_in)][:held]
    if len(held_rows) < held:
        sys.exit(f"the held groups hold {len(held_rows)} documents of the {held} asked")
    os.makedirs(out, exist_ok=True)
    if os.listdir(out):
        sys.exit(f"{out} holds files; a slice is written under a new or an empty directory")
    clock = [None]
    # The first reading: which documents train, and the histogram their chart is located on.
    hist = np.zeros(PAST - LEAST, dtype=np.int64)
    first = next(iter(read_role(train_rows[:1], clock, None)), None)
    if first is None:
        sys.exit("no training document")
    limit = seconds * clock[0]
    taken = []
    for ident, x in read_role(train_rows, clock, limit):
        hist += np.bincount(x.astype(np.int64) - LEAST, minlength=PAST - LEAST)
        taken.append(ident)
    cuts, total = cuts_of(hist, len(octets))
    if total < limit:
        sys.exit(f"the training groups hold {total} samples of the {limit} asked")
    chart = chart_rows(cuts, hist)
    if any(c == 0 for _, _, c in chart):
        sys.exit("a level no sample falls in: the distribution holds an atom wider than a level")
    with open(os.path.join(out, f"CHART_{name}.tsv"), "x") as f:
        f.write(CHART_HEAD)
        for r, (lo, hi, c) in enumerate(chart):
            f.write(f"{r}\t{octets[r]}\t{lo}\t{hi}\t{c}\n")
    # The second reading: the same documents through the chart, then the held ones.
    by_id = {r[0]: r for r in train_rows}
    roles = {}
    for stem, role_rows in (("DOCS", [by_id[i] for i in taken]), ("HELD", held_rows)):
        role = Role(out, stem, name, remainder)
        for ident, x in read_role(role_rows, clock, None):
            role.add(ident, x, cuts, octets)
        role.close()
        roles[stem] = role
    if roles["DOCS"].octets != total:
        sys.exit("the second reading of the training documents is not the first")
    mass = np.asarray([c for _, _, c in chart], dtype=np.float64) / total
    with open(os.path.join(out, f"BOUNDARY_{name}.tsv"), "x") as f:
        f.write(f"clock_hz\t{clock[0]}\nsample_bits\t16\nlevels\t{len(octets)}\noctets\t{','.join(format(o, '02X') for o in octets)}\n")
        f.write(f"held_one_group_in\t{one_in}\nlevel_entropy_micronats\t{int(round(float(-(mass * np.log(mass)).sum()) * 1e6))}\n")
        for stem, label in (("DOCS", "train"), ("HELD", "held")):
            r = roles[stem]
            f.write(f"{label}_documents\t{r.documents}\n{label}_samples\t{r.octets}\n{label}_samples_sha256\t{r.pcm.hexdigest()}\n")
        f.write(f"remainder\t{int(remainder)}\n")
    print(f"WAVE_CHART clock_hz={clock[0]} levels={len(octets)} cuts={' '.join(map(str, cuts))}")
    print(f"WAVE_MASS least={min(c for _, _, c in chart)} most={max(c for _, _, c in chart)} of={total}")
    print(STORE_HEAD, end="")
    for role, stem in (("train", "DOCS"), ("prefix", "DOCS"), ("held", "HELD")):
        print(roles[stem].row(role, name))


def boundary_of(out, name):
    return dict(line.split("\t") for line in open(os.path.join(out, f"BOUNDARY_{name}.tsv")).read().rstrip("\n").split("\n"))


def chart_of(out, name):
    lines = open(os.path.join(out, f"CHART_{name}.tsv")).read().rstrip("\n").split("\n")
    if lines[0] + "\n" != CHART_HEAD:
        sys.exit(f"CHART_{name}.tsv does not open with its head")
    return [tuple(int(v) for v in line.split("\t")) for line in lines[1:]]


def check(out, name):
    boundary, chart = boundary_of(out, name), chart_of(out, name)
    if boundary["remainder"] != "1":
        sys.exit("a slice written without its remainder: the samples are returned from its sources")
    low_of = np.full(256, PAST, dtype=np.int64)
    for _, octet, lo, _, _ in chart:
        low_of[octet] = lo
    for stem, rem_stem, label in (("DOCS", "REMAINDER", "train"), ("HELD", "HELD_REMAINDER", "held")):
        h, count = hashlib.sha256(), 0
        with open(os.path.join(out, f"{stem}_{name}.bin"), "rb") as b, open(os.path.join(out, f"{rem_stem}_{name}.bin"), "rb") as r:
            while True:
                body = np.frombuffer(b.read(1 << 22), dtype=np.uint8)
                rem = np.frombuffer(r.read(2 * len(body)), dtype="<u2")
                if len(body) == 0:
                    if r.read(1):
                        sys.exit(f"{rem_stem}_{name}.bin holds samples past the slice's")
                    break
                if len(rem) != len(body):
                    sys.exit(f"{rem_stem}_{name}.bin ends before the slice")
                low = low_of[body]
                if (low == PAST).any():
                    sys.exit(f"{stem}_{name}.bin holds an octet the chart does not")
                h.update((low + rem).astype("<i2").tobytes())
                count += len(body)
        same = h.hexdigest() == boundary[f"{label}_samples_sha256"] and count == int(boundary[f"{label}_samples"])
        print(f"WAVE_CHECK role={label} samples={count} returned={'equal' if same else 'DIFFERS'}")
        if not same:
            sys.exit(1)


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 24), b""):
            h.update(chunk)
    return h.hexdigest()


def join(store, out, new, name):
    rows = open(os.path.join(store, "STORE.tsv")).read()
    if not rows.startswith(STORE_HEAD):
        sys.exit("a STORE.tsv that does not open with its head")
    if any(line.split("\t")[1] == name for line in rows.rstrip("\n").split("\n")[1:]):
        sys.exit(f"the store already holds a slice {name}")
    files = {"DOCS": (f"DOCS_{name}.bin", f"DOCS_{name}.tsv", f"IDS_{name}.txt"), "HELD": (f"HELD_{name}.bin", f"HELD_{name}.tsv", f"HELD_IDS_{name}.txt")}
    extra = (f"CHART_{name}.tsv", f"BOUNDARY_{name}.tsv")
    counts = {}
    for stem, (data, index, _) in files.items():
        lines = open(os.path.join(out, index)).read()
        if not lines.startswith(INDEX_HEAD):
            sys.exit(f"{index} does not open with its head")
        counts[stem] = (lines.count("\n") - 1, os.path.getsize(os.path.join(out, data)), sha256_of(os.path.join(out, data)))
    os.makedirs(new)
    for f in sorted(os.listdir(store)):
        if f != "STORE.tsv" and os.path.isfile(os.path.join(store, f)):
            os.link(os.path.join(store, f), os.path.join(new, f))
    for f in (*files["DOCS"], *files["HELD"], *extra):
        os.link(os.path.join(out, f), os.path.join(new, f))
    with open(os.path.join(new, "STORE.tsv"), "x") as f:
        f.write(rows)
        for role, stem in (("train", "DOCS"), ("prefix", "DOCS"), ("held", "HELD")):
            n, octets, sha = counts[stem]
            row = f"{role}\t{name}\t0\t0\t{n}\t{n}\t{octets}\t{octets}\t{sha}"
            f.write(row + "\n")
            print("WAVE_JOIN " + row)


def main(argv):
    if len(argv) >= 7 and argv[0] == "write":
        rest = argv[7:]
        octets, remainder = FREE_OCTETS, False
        while rest:
            if rest[0] == "--remainder":
                remainder, rest = True, rest[1:]
            elif rest[0] == "--octets" and len(rest) > 1:
                octets, rest = tuple(int(h, 16) for h in rest[1].split(",")), rest[2:]
            else:
                sys.exit(__doc__)
        if len(octets) < 2 or list(octets) != sorted(set(octets)) or not all(0 <= o < 256 for o in octets):
            sys.exit("the octets are two or more distinct octets, ascending")
        write(argv[1], argv[2], argv[3], int(argv[4]), int(argv[5]), int(argv[6]), octets, remainder)
    elif len(argv) == 3 and argv[0] == "check":
        check(argv[1], argv[2])
    elif len(argv) == 5 and argv[0] == "join":
        join(argv[1], argv[2], argv[3], argv[4])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
