#!/usr/bin/env python3
"""Controls of tools/wave_passage.py on synthetic sources (raw 16-bit samples, so no decoder runs): the chart's levels hold equal
masses, the slice is in the store's form and the store's own reader reads it, chart and remainder return every sample, no held
group trains, a grown store holds the slice's rows after its own, and the refusals refuse."""
import hashlib
import os
import subprocess
import sys
import tempfile

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus_passage  # noqa: E402
import wave_passage  # noqa: E402

TOOL = os.path.join(HERE, "wave_passage.py")
RATE = 1000


def run(*args, ok=True):
    p = subprocess.run([sys.executable, "-I", TOOL, *args], capture_output=True, text=True)
    if ok and p.returncode != 0:
        raise SystemExit(f"wave_passage {' '.join(args)} failed: {p.stderr[-400:]}")
    return p


def sources(root, groups, per_group, length, seed=7):
    """Sources whose samples together are each of 13 * m distinct values once (a permutation), so every level's mass is known."""
    rng = np.random.default_rng(seed)
    n = groups * per_group * length
    values = (np.arange(n, dtype=np.int64) * 5) - (n * 5) // 2  # distinct, inside 16 bits for the sizes used here
    assert values.min() >= -32768 and values.max() < 32768
    rng.shuffle(values)
    rows, k = [], 0
    for g in range(groups):
        for d in range(per_group):
            path = os.path.join(root, f"g{g}_d{d}.s16le")
            values[k:k + length].astype("<i2").tofile(path)
            rows.append(f"doc-{g}-{d}\tgroup-{g}\t{path}\t{RATE}")
            k += length
    listing = os.path.join(root, "LISTING.tsv")
    with open(listing, "w") as f:
        f.write("\n".join(rows) + "\n")
    return listing


def main():
    failed = []

    def control(name, held):
        print(f"wave-passage control {name}: {'ok' if held else 'FAILED'}")
        if not held:
            failed.append(name)

    with tempfile.TemporaryDirectory() as root:
        listing = sources(root, groups=24, per_group=4, length=130)
        one_in = 4
        held_groups = {f"group-{g}" for g in range(24) if wave_passage.held_group(f"group-{g}", one_in)}
        control("the keyed draw holds some groups and trains others", 0 < len(held_groups) < 24)
        train_docs = (24 - len(held_groups)) * 4
        seconds = (train_docs * 130) // RATE  # whole seconds the training groups hold
        out = os.path.join(root, "slice")
        p = run("write", out, listing, "wave", str(seconds), "3", str(one_in), "--remainder")
        p_first = p.stdout.split("\n")[-4:]
        rows = [line.split("\t") for line in p.stdout.split("\n") if line.startswith(("train\t", "prefix\t", "held\t"))]
        control("three store rows of nine fields", len(rows) == 3 and all(len(r) == 9 for r in rows))

        chart = wave_passage.chart_of(out, "wave")
        octets = [c[1] for c in chart]
        control("thirteen levels on the octets no UTF-8 text holds", octets == list(wave_passage.FREE_OCTETS) and len(octets) == 13)
        undecodable = all(_refuses(bytes([o])) for o in octets)
        control("each of those octets alone is no UTF-8 text", undecodable)
        counts = [c[4] for c in chart]
        control("levels of equal mass on distinct values", max(counts) - min(counts) <= 1 and sum(counts) == int(rows[0][7]))
        control("the chart's bounds tile the sample's range", chart[0][2] == -32768 and chart[-1][3] == 32768 and all(a[3] == b[2] for a, b in zip(chart, chart[1:])))

        ids = open(os.path.join(out, "IDS_wave.txt")).read().split()
        held_ids = open(os.path.join(out, "HELD_IDS_wave.txt")).read().split()
        group_of = {line.split("\t")[0]: line.split("\t")[1] for line in open(listing).read().rstrip("\n").split("\n")}
        control("no held group trains", all(group_of[i] not in held_groups for i in ids) and all(group_of[i] in held_groups for i in held_ids) and len(held_ids) == 3)
        order = sorted(ids, key=lambda i: hashlib.sha256(i.encode()).hexdigest())
        control("documents stand in the order of their id's SHA-256", ids == order)

        # The store's own reader reads the slice, and each piece is its source through the chart.
        pieces = list(corpus_passage.pieces(out, "wave"))
        path_of = {line.split("\t")[0]: line.split("\t")[2] for line in open(listing).read().rstrip("\n").split("\n")}
        cuts = np.asarray([c[2] for c in chart[1:]])
        same = len(pieces) == len(ids)
        for (document, title, text, opens, closes), ident in zip(pieces, ids):
            x = np.fromfile(path_of[ident], dtype="<i2")
            want = np.asarray(octets, dtype=np.uint8)[np.searchsorted(cuts, x, side="right")].tobytes()
            same = same and title == b"" and opens and closes and text == want
        control("the store's reader reads each source through the chart", same)
        held_pieces = list(corpus_passage.pieces(out, "wave", stem="HELD"))
        control("the held cut reads through the training's chart", len(held_pieces) == 3 and all(set(t) <= set(octets) for _, _, t, _, _ in held_pieces))
        sha = hashlib.sha256(open(os.path.join(out, "DOCS_wave.bin"), "rb").read()).hexdigest()
        control("a row's SHA-256 is its file's", rows[0][8] == sha and rows[1][8] == sha and rows[0][7] == str(os.path.getsize(os.path.join(out, "DOCS_wave.bin"))))

        p = run("check", out, "wave")
        control("chart and remainder return every sample", p.stdout.count("returned=equal") == 2)
        # A remainder moved by one is caught.
        rem = os.path.join(out, "REMAINDER_wave.bin")
        body = bytearray(open(rem, "rb").read())
        body[0] ^= 1
        open(rem, "wb").write(body)
        control("a changed remainder is refused", run("check", out, "wave", ok=False).returncode != 0)

        # A grown store.
        store = os.path.join(root, "store")
        os.makedirs(store)
        base = wave_passage.STORE_HEAD + "train\tcode\t40\t0\t1\t1\t5\t5\tabc\n"
        open(os.path.join(store, "STORE.tsv"), "w").write(base)
        open(os.path.join(store, "DOCS_code.bin"), "wb").write(b"hello")
        new = os.path.join(root, "grown")
        run("join", store, out, new, "wave")
        grown = open(os.path.join(new, "STORE.tsv")).read()
        linked = os.path.samefile(os.path.join(store, "DOCS_code.bin"), os.path.join(new, "DOCS_code.bin")) and os.path.samefile(os.path.join(out, "DOCS_wave.bin"), os.path.join(new, "DOCS_wave.bin"))
        control("a grown store links both and holds the slice's rows after its own", linked and grown.startswith(base) and grown[len(base):].split("\n")[0].split("\t")[:2] == ["train", "wave"] and grown.count("\twave\t") == 3)
        control("a store that holds the slice refuses it again", run("join", new, out, os.path.join(root, "again"), "wave", ok=False).returncode != 0)

        # Refusals of the writer.
        flat = os.path.join(root, "flat.s16le")
        np.zeros(4000, dtype="<i2").tofile(flat)
        flat_listing = os.path.join(root, "FLAT.tsv")
        names = [g for g in (f"q{i}" for i in range(64)) if not wave_passage.held_group(g, 2)][:1] + [g for g in (f"q{i}" for i in range(64)) if wave_passage.held_group(g, 2)][:1]
        open(flat_listing, "w").write(f"a\t{names[0]}\t{flat}\t{RATE}\nb\t{names[1]}\t{flat}\t{RATE}\n")
        control("a level no sample falls in is refused", "atom" in run("write", os.path.join(root, "flat"), flat_listing, "wave", "1", "1", "2", ok=False).stderr)
        mixed = os.path.join(root, "MIXED.tsv")
        first = open(listing).read().rstrip("\n").split("\n")
        trains = [r for r in first if r.split("\t")[1] not in held_groups]
        open(mixed, "w").write("\n".join([trains[0]] + [r.rsplit("\t", 1)[0] + "\t2000" for r in trains[1:]] + [r for r in first if r.split("\t")[1] in held_groups]) + "\n")
        control("a source drawn at another clock is refused", "samples a second" in run("write", os.path.join(root, "mixed"), mixed, "wave", "1", "1", str(one_in), ok=False).stderr)
        control("more seconds than the training groups hold is refused", "of the" in run("write", os.path.join(root, "long"), listing, "wave", str(seconds + 5), "3", str(one_in), ok=False).stderr)
        control("a directory that holds files is refused", run("write", out, listing, "wave", str(seconds), "3", str(one_in), ok=False).returncode != 0)
        empty = os.path.join(root, "empty")
        os.makedirs(empty)
        again = run("write", empty, listing, "wave", str(seconds), "3", str(one_in))
        control("an empty directory takes the slice, and a second writing is the first", again.stdout.split("\n")[-4:] == p_first)
    if failed:
        sys.exit(f"wave-passage controls failed: {', '.join(failed)}")
    print("wave-passage controls: all held")


def _refuses(octets):
    try:
        octets.decode("utf-8")
    except UnicodeDecodeError:
        return True
    return False


if __name__ == "__main__":
    main()
