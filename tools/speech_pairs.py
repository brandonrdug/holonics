#!/usr/bin/env -S python3 -I
"""Speech beside its words: a slice whose every document is an utterance's loudness at a frame's clock, then its transcript.

One stream law reads every passage, so nothing here names what the frames or the letters are. The boundary states the frame's clock,
the chart and the pairing, and keeps nothing the passage does not hold.

  frame      the utterance's samples cut into frames of F samples (the last one shorter), each read as its energy
             e = sum of x^2 over the frame, and as the integer v = 16 b + m: b the octave of 1 + e (its bit length less one) and m
             the four bits under its top, so v rises with e and a step of v is a sixteenth of an octave of power or less
  chart      K levels of equal mass over the training frames' v, located as wave_passage.py locates its levels (c_j the least value
             with K #{v < c_j} >= j N), level r written as the octet o_r, the octets ascending with the level
  document   the frames' octets, a line's end, the transcript in lower case, a line's end: the sound and then its words in one passage
  bound      a document is taken only where its places stand within BOUND (the field's reach, so a region holds an utterance whole
             and its words beside it); the rest are counted and left
  held       a group (one speaker) is held where the first eight hex digits of its name's SHA-256, read as a number, divide by
             HELD_ONE_IN, as wave_passage.py holds a group; its documents never train, and the chart is located without them

Why the loudness at 100 frames a second (the lead, November 26, Brandon's message of November 25 17:10 UTC on speech timings coupling to
text, and of November 26 18:27 UTC on transcription): at the samples' own clock a word's sound spans thousands of places and her reach
holds 1,885, so no region holds an utterance beside its words; at a frame of 10 ms a median utterance of 14 s is 1,400 places and its
words some 200 more. The loudness carries an utterance's timing (its syllables' beat and its pauses), the part the formal thread read
standing in the wave past sixteen samples (the cut record's §12). It carries no spectrum, so the slice tests whether timing alone tells
her the words' count and rhythm; a spectrum would take more octets a frame than the field's free octets give.
The octets are by default the thirteen no UTF-8 text holds (C0, C1, F5 to FF), the wave slice's: a frame's level and a sample's level
share a class, told apart by the passage around them (`agent-inferred`: the free octets are thirteen, and a second chart's own
octets would cost two places a frame).

Usage:
  speech_pairs.py write OUT MANIFEST NAME DOCUMENTS HELD HELD_ONE_IN [--frame F] [--bound BOUND] [--passes R]

MANIFEST is a JSON-lines listing with `id`, `speaker_id`, `source_root`, `flac_path`, `sample_rate_hz` and `transcript` a line. It
writes the slice NAME under OUT in `corpus_passage.py`'s form (`DOCS_NAME.bin`, `DOCS_NAME.tsv`, `IDS_NAME.txt` and the `HELD_` three),
the chart `CHART_NAME.tsv` (level, octet, low, high, count over v) and the boundary's statement `BOUNDARY_NAME.tsv`, and prints the
slice's `STORE.tsv` rows; `wave_passage.py join` then joins it to a store. Outside the machine: a boundary codec.

With `--passes R` the training documents are written R times, each time in the order of SHA-256 of `ID:r`: a slice's share of a pass
is its octets (the cut's quotas), so R passes over the utterances give them R times the share (the lead, November 26: the 25,000
utterances alone are 0.23% of the wave store's octets, some 250 utterances a lap; sixteen passes stand at the wave slice's share). The
held documents are written once.
"""
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("wave_passage", os.path.join(HERE, "wave_passage.py"))
assert _spec is not None and _spec.loader is not None
wave_passage = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(wave_passage)

FRAME, BOUND = 160, 1880
V_PAST = 16 * 64  # v = 16 b + m for 1 + e < 2^64 stands under 16 * 63 + 16


def frames_of(x, frame):
    """Each frame's v = 16 b + m (b the octave of 1 + e, m the four bits under its top), e its samples' summed squares, in integers
    (a frame's last part stands as it is)."""
    x = x.astype(np.int64)
    n = (len(x) + frame - 1) // frame
    e = np.zeros(n, dtype=np.int64)
    np.add.at(e, np.arange(len(x)) // frame, x * x)
    one = e + 1
    octave = np.floor(np.log2(one.astype(np.float64))).astype(np.int64)
    # The float above only places the octave; it is corrected to the integer bit length, so v is read from integers alone.
    octave = np.where((one >> octave) == 0, octave - 1, octave)
    octave = np.where((one >> (octave + 1)) > 0, octave + 1, octave)
    shift = np.maximum(octave - 4, 0)
    sixteenths = np.where(octave >= 4, (one >> shift) - 16, (one << (4 - octave)) - 16)
    return 16 * octave + sixteenths


def rows_of(manifest):
    rows = []
    for line in open(manifest, encoding="utf-8"):
        d = json.loads(line)
        rows.append((d["id"], d["speaker_id"], os.path.join(d["source_root"], d["flac_path"]), d["sample_rate_hz"], d["transcript"]))
    if len({r[0] for r in rows}) != len(rows):
        sys.exit(f"{manifest} holds an id twice")
    return sorted(rows, key=lambda r: wave_passage.key(r[0]))


def decoded(row, frame):
    ident, _, path, rate, words = row
    x, clock = wave_passage.samples_of((ident, None, path, None))
    if clock != rate:
        sys.exit(f"{path}: drawn at {clock} where its listing says {rate}")
    return frames_of(x, frame), words.lower().encode("utf-8"), len(x)


def read(rows, frame, bound, limit):
    """The rows' (id, v, words, samples) in order whose places stand within the bound, up to `limit` of them; and the count left."""
    taken, left = [], 0
    workers = os.cpu_count() or 1
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for k in range(0, len(rows), 4 * workers):
            batch = rows[k:k + 4 * workers]
            for row, (v, words, n) in zip(batch, pool.map(lambda r: decoded(r, frame), batch)):
                if len(taken) >= limit:
                    return taken, left
                if len(v) + len(words) + 2 > bound or len(v) == 0 or not words:
                    left += 1
                    continue
                taken.append((row[0], v, words, n))
    return taken, left


def write(out, manifest, name, documents, held, one_in, frame, bound, octets, passes=1):
    rows = rows_of(manifest)
    train_rows = [r for r in rows if not wave_passage.held_group(r[1], one_in)]
    held_rows = [r for r in rows if wave_passage.held_group(r[1], one_in)]
    os.makedirs(out, exist_ok=True)
    if os.listdir(out):
        sys.exit(f"{out} holds files; a slice is written under a new or an empty directory")
    train, train_left = read(train_rows, frame, bound, documents)
    kept, held_left = read(held_rows, frame, bound, held)
    if len(train) < documents or len(kept) < held:
        sys.exit(f"within the bound the rows hold {len(train)} training and {len(kept)} held documents of {documents} and {held}")
    hist = np.zeros(V_PAST, dtype=np.int64)
    for _, v, _, _ in train:
        hist += np.bincount(v, minlength=V_PAST)
    total = int(hist.sum())
    below = np.concatenate(([0], np.cumsum(hist)[:-1])).astype(np.int64)
    levels = len(octets)
    cuts = [int(np.searchsorted(below * levels, j * total, side="left")) for j in range(1, levels)]
    lows, highs = [0] + cuts, cuts + [V_PAST]
    chart = [(lo, hi, int(hist[lo:hi].sum())) for lo, hi in zip(lows, highs)]
    if any(c == 0 for _, _, c in chart):
        sys.exit("a level no frame falls in")
    with open(os.path.join(out, f"CHART_{name}.tsv"), "x") as f:
        f.write(wave_passage.CHART_HEAD)
        for r, (lo, hi, c) in enumerate(chart):
            f.write(f"{r}\t{octets[r]}\t{lo}\t{hi}\t{c}\n")
    roles = {}
    passed = [doc for r in range(passes) for doc in sorted(train, key=lambda d: wave_passage.key(f"{d[0]}:{r}"))] if passes > 1 else train
    for stem, docs in (("DOCS", passed), ("HELD", kept)):
        ids_stem = "HELD_IDS" if stem == "HELD" else "IDS"
        sha, count, frames, letters = hashlib.sha256(), 0, 0, 0
        with open(os.path.join(out, f"{stem}_{name}.bin"), "xb") as b, open(os.path.join(out, f"{stem}_{name}.tsv"), "x") as t, open(os.path.join(out, f"{ids_stem}_{name}.txt"), "x") as ids:
            t.write(wave_passage.INDEX_HEAD)
            for k, (ident, v, words, _) in enumerate(docs):
                level = np.searchsorted(np.asarray(cuts, dtype=np.int64), v, side="right")
                body = np.asarray(octets, dtype=np.uint8)[level].tobytes() + b"\n" + words + b"\n"
                b.write(body)
                sha.update(body)
                t.write(f"{k}\t0\t{len(body)}\t1\t1\n")
                ids.write(ident + "\n")
                count += len(body)
                frames += len(v)
                letters += len(words)
        roles[stem] = (len(docs), count, sha.hexdigest(), frames, letters)
    mass = np.asarray([c for _, _, c in chart], dtype=np.float64) / total
    with open(os.path.join(out, f"BOUNDARY_{name}.tsv"), "x") as f:
        f.write(f"frame_samples\t{frame}\nclock_hz\t{train_rows[0][3] // frame if train_rows[0][3] % frame == 0 else 0}\nlevels\t{levels}\n")
        f.write(f"octets\t{','.join(format(o, '02X') for o in octets)}\nbound\t{bound}\nheld_one_group_in\t{one_in}\n")
        f.write(f"level_entropy_micronats\t{int(round(float(-(mass * np.log(mass)).sum()) * 1e6))}\npasses\t{passes}\n")
        for stem, label, left in (("DOCS", "train", train_left), ("HELD", "held", held_left)):
            n, count, sha, frames, letters = roles[stem]
            f.write(f"{label}_documents\t{n}\n{label}_octets\t{count}\n{label}_frames\t{frames}\n{label}_letters\t{letters}\n{label}_past_bound\t{left}\n{label}_sha256\t{sha}\n")
    print(f"PAIRS_CHART frame={frame} levels={levels} cuts={' '.join(map(str, cuts))}")
    for stem, label in (("DOCS", "train"), ("HELD", "held")):
        n, count, _, frames, letters = roles[stem]
        print(f"PAIRS_ROLE {label} documents={n} octets={count} frames={frames} letters={letters}")
    print(wave_passage.STORE_HEAD, end="")
    for role, stem in (("train", "DOCS"), ("prefix", "DOCS"), ("held", "HELD")):
        n, count, sha, _, _ = roles[stem]
        print(f"{role}\t{name}\t0\t0\t{n}\t{n}\t{count}\t{count}\t{sha}")


def main(argv):
    if len(argv) >= 7 and argv[0] == "write":
        rest, frame, bound, passes = argv[7:], FRAME, BOUND, 1
        while rest:
            if rest[0] == "--passes" and len(rest) > 1:
                passes, rest = int(rest[1]), rest[2:]
            elif rest[0] == "--frame" and len(rest) > 1:
                frame, rest = int(rest[1]), rest[2:]
            elif rest[0] == "--bound" and len(rest) > 1:
                bound, rest = int(rest[1]), rest[2:]
            else:
                sys.exit(f"unknown word {rest[0]}")
        write(argv[1], argv[2], argv[3], int(argv[4]), int(argv[5]), int(argv[6]), frame, bound, wave_passage.FREE_OCTETS, passes)
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
