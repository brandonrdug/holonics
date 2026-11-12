#!/usr/bin/env -S python3 -I
"""Controls of corpus_passage.py on drawn shards (parquet files written here with pyarrow; nothing is fetched). They run under
a python that holds pyarrow (on the PC, .local/venv-corpus), so they stand outside tools/gate.sh, whose python has none.

  order      the shards sort by (d, n, m) as integers, and the listing's other files are left out;
  slices     each slice's filter, and 'Open Government', other languages and other collections in none;
  grid       a document's windows: 256-byte answers from its first byte, each with the 256 bytes before it, the first with the
             title line (its first 255 bytes and a newline);
  drops      a separator on either side drops a window, and a science answer whose lines average under 25 bytes drops it in
             science alone;
  build      each slice takes whole documents while under its quota; no government, French or transcript text is kept; the
             records read back as seen_passage.problems_of reads them, each slice's windows in its documents' order; TRAIN.txt is
             PASSAGE.txt's prefix while its answer bytes stand under P; every record was written by the slice of least progress;
  held       the held windows come from the far end, never from a document whose text a training document holds, each its
             document's middle window (or the first kept after it); a held read that reaches a trained shard is refused;
  manifest   each shard's octets, SHA-256 and rows, its documents and answer bytes a slice, the identifiers in order, and the
             printed SHA-256 of every passage;
  bounds     the shard bound, the held bound and the early stop each stop the run (CORPUS_STOPPED); a passage file that ends
             inside a record is refused; a standing out directory is refused before anything is fetched.
"""
import hashlib
import itertools
import os
import shutil
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus_passage as cp  # noqa: E402
import seen_passage as sp  # noqa: E402

PASSED = []

KINDS = {  # open_type, collection, language
    "code": ("Open Source", "GitHub", "Python"),
    "web": ("Open Web", "Wikipedia", "English"),
    "science": ("Open Science", "OpenAlex", "English"),
    "books": ("Open Culture", "English-PD", "English"),
    "wikidata": ("Semantic data", "Wikidata", "German"),
}
LETTER = {"code": "c", "web": "w", "science": "s", "books": "b", "wikidata": "d"}
OF_LETTER = {ord(v): k for k, v in LETTER.items()}
NEAR = [f"common_corpus_1/subset_1_{m}.parquet" for m in range(1, 6)]
FAR = ["common_corpus_2/subset_1_1.parquet", "common_corpus_2/subset_2_1.parquet"]


def check(name, condition):
    if not condition:
        raise SystemExit(f"FAILED {name}")
    PASSED.append(name)


def stopped(f):
    """The message of the SystemExit that `f()` raises, or None."""
    try:
        f()
    except SystemExit as e:
        return str(e)
    return None


def row(identifier, open_type, collection, language, title, text):
    return {"identifier": identifier, "collection": collection, "open_type": open_type, "language": language, "title": title, "text": text}


def text_of(name, k, lines):
    """A drawn document of `lines` lines of 39 bytes, unique by k; wikidata's lines hold a two-byte letter."""
    mark = "é" if name == "wikidata" else LETTER[name]
    line = LETTER[name] * (31 - len(mark.encode())) + mark + f"{k:07d}" + "\n"
    return line * lines


def draw():
    """{path: rows}: five near shards and two far ones, each with two documents a slice (four of code), a government, a French, a
    transcript, an empty and a table document; the second near shard holds a web document with a separator, and the far end a web
    document whose text is the first web document's."""
    counter = dict.fromkeys(cp.NAMES, 0)
    shards = {}
    first_web = None
    for path in NEAR + FAR:
        rows = [row(f"{path}/gov", "Open Government", "Caselaw Access Project", "English", "GOVERNMENT", "GOVERNMENT\n" * 50)]
        if path == FAR[-1]:
            rows.append(row(f"{path}/dup", *KINDS["web"], "WEB again", first_web))
        for name in cp.NAMES:
            for _ in range(4 if name == "code" else 2):
                k = counter[name]
                counter[name] += 1
                text = text_of(name, k, 8 + (k * 5) % 13)
                rows.append(row(f"{path}/{name}/{k}", *KINDS[name], f"{name.upper()} title {k}", text))
                if name == "web" and first_web is None:
                    first_web = text
        if path == NEAR[1]:
            line = text_of("web", 999, 1)
            rows.append(row(f"{path}/web/sep", *KINDS["web"], "WEB separated", line * 3 + "\x1e" + line * 20))
        rows.append(row(f"{path}/french", "Open Web", "Wikipedia", "French", "FRENCH", "FRENCH\n" * 60))
        rows.append(row(f"{path}/youtube", "Open Web", "YouTube-Commons", "English", "YOUTUBE", "YOUTUBE\n" * 60))
        rows.append(row(f"{path}/empty", *KINDS["code"], "EMPTY", ""))
        rows.append(row(f"{path}/tables", *KINDS["science"], "TABLES", ("s" * 9 + "\n") * 60))
        shards[path] = rows
    return shards


def write_shards(root, shards):
    import pyarrow as pa
    import pyarrow.parquet as pq

    for path, rows in shards.items():
        full = os.path.join(root, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        pq.write_table(pa.table({c: [r[c] for r in rows] for c in cp.COLUMNS}), full)


def fetcher(root, cache, fetched):
    """A fetch that copies a drawn shard into the cache (the build deletes what it read) and logs the path."""
    def fetch(path):
        fetched.append(path)
        dst = os.path.join(cache, path)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(os.path.join(root, path), dst)
        return dst
    return fetch


def kept_windows(name, r):
    text = r["text"].encode()
    return [(q, a) for q, a in cp.windows_of(r["title"].encode(), text) if not cp.dropped(name, q, a)]


def expected_train(shards, order, quota):
    """The rule restated on the drawn rows: the shards read, each slice's kept documents in order, and each shard's counts."""
    taken = dict.fromkeys(cp.NAMES, 0)
    kept = {n: [] for n in cp.NAMES}
    read, per_shard = [], {}
    for path in order:
        if all(taken[n] >= quota[n] for n in cp.NAMES):
            break
        read.append(path)
        counts = {n: [0, 0] for n in cp.NAMES}
        for r in shards[path]:
            name = cp.slice_of(r)
            if name is None or taken[name] >= quota[name] or not r["text"]:
                continue
            ws = kept_windows(name, r)
            if ws:
                got = sum(len(a) for _, a in ws)
                taken[name] += got
                kept[name].append((r["identifier"], r["text"].encode(), ws))
                counts[name][0] += 1
                counts[name][1] += got
        per_shard[path] = counts
    return read, taken, kept, per_shard


def expected_held(shards, order, trained, held):
    want = dict.fromkeys(cp.NAMES, held)
    picks = {n: [] for n in cp.NAMES}
    used = []
    for path in reversed(order):
        if not any(want.values()):
            break
        used.append(path)
        for r in shards[path]:
            name = cp.slice_of(r)
            text = r["text"].encode()
            if name is None or not want[name] or not text or hashlib.sha256(text).digest() in trained:
                continue
            ws = cp.windows_of(r["title"].encode(), text)
            pick = next(((q, a) for q, a in ws[len(ws) // 2:] if not cp.dropped(name, q, a)), None)
            if pick is not None:
                picks[name].append((r["identifier"], pick))
                want[name] -= 1
    return used, picks


def label(answer):
    """The slice whose letter an answer holds first."""
    return next(OF_LETTER[b] for b in answer if b in OF_LETTER)


def main():
    order = cp.order_of(["README.md", "common_corpus_10/subset_1_1.parquet", "common_corpus_2/subset_10_1.parquet", "logo/a.png",
                         "common_corpus_2/subset_9_10.parquet", "common_corpus_2/subset_9_2.parquet", "common_corpus_2/subset_9_2.json"])
    check("order by integers", order == ["common_corpus_2/subset_9_2.parquet", "common_corpus_2/subset_9_10.parquet",
                                         "common_corpus_2/subset_10_1.parquet", "common_corpus_10/subset_1_1.parquet"])

    for name, (ot, coll, lang) in KINDS.items():
        check(f"slice {name}", cp.slice_of(row("x", ot, coll, lang, "", "t")) == name)
    check("slice code in any language", cp.slice_of(row("x", "Open Source", "GitHub", "Rust", "", "t")) == "code")
    check("slice web collections", all(cp.slice_of(row("x", "Open Web", c, "English", "", "t")) == "web" for c in cp.WEB))
    check("slice books collections", all(cp.slice_of(row("x", "Open Culture", c, "English", "", "t")) == "books" for c in cp.BOOKS))
    check("slice wikidata in any language", cp.slice_of(row("x", "Semantic data", "Wikidata", "French", "", "t")) == "wikidata")
    for ot, coll, lang in (("Open Government", "Caselaw Access Project", "English"), ("Open Government", "Wikipedia", "English"),
                           ("Open Web", "Wikipedia", "French"), ("Open Web", "YouTube-Commons", "English"),
                           ("Open Science", "OpenAlex", "French"), ("Open Culture", "US-PD-Newspapers", "English"),
                           ("Open Culture", "English-PD", "French")):
        check(f"slice none: {ot}, {coll}, {lang}", cp.slice_of(row("x", ot, coll, lang, "", "t")) is None)

    text = bytes(range(256)) * 2 + b"xyz"
    check("grid", cp.windows_of(b"T" * 300, text) == [(b"T" * 255 + b"\n", text[:256]), (text[:256], text[256:512]),
                                                      (text[256:512], text[512:])])
    check("grid empty title", cp.windows_of(b"", b"ab") == [(b"\n", b"ab")])
    check("grid empty text", cp.windows_of(b"t", b"") == [])

    check("drop separator in answer", cp.dropped("web", b"q", b"a\x1eb") == "separator")
    check("drop separator in question", cp.dropped("web", b"q\x1f", b"a") == "separator")
    check("drop short lines in science", cp.dropped("science", b"q", (b"x" * 24 + b"\n") * 10) == "lines")
    check("keep short lines elsewhere", cp.dropped("web", b"q", (b"x" * 24 + b"\n") * 10) is None)
    check("lines at the floor kept", cp.dropped("science", b"q", b"x" * 49 + b"\n") is None)
    check("lines under the floor dropped", cp.dropped("science", b"q", b"x" * 48 + b"\n") == "lines")

    shards = draw()
    order = cp.order_of(list(shards))
    check("drawn order", order == NEAR + FAR)
    answer_bytes, prefix, held = 10_000, 3_000, 3
    quota = {n: answer_bytes * share // 100 for n, share, _ in cp.SLICES}
    with tempfile.TemporaryDirectory() as root:
        src, cache, out = (os.path.join(root, d) for d in ("src", "cache", "out"))
        write_shards(src, shards)
        os.makedirs(out)
        fetched, lines = [], []
        cp.build(order, fetcher(src, cache, fetched), out, answer_bytes, prefix, held, log=lines.append, max_shards=5, max_held=2)
        read, taken, kept, per_shard = expected_train(shards, order, quota)
        check("drawn quotas fill before the far shards", len(read) < len(NEAR))
        passage = open(os.path.join(out, "PASSAGE.txt"), "rb").read()
        train = open(os.path.join(out, "TRAIN.txt"), "rb").read()
        records = list(cp.records(os.path.join(out, "PASSAGE.txt")))
        check("records read as problems_of reads them", sp.problems_of(passage) == records)
        check("no government, French or transcript text", all(m not in f for m in (b"GOVERNMENT", b"FRENCH", b"YOUTUBE") for f in (passage, train)))
        labels = [label(a) for _, a in records]
        for n in cp.NAMES:
            mine = [rec for rec, lab in zip(records, labels) if lab == n]
            check(f"build {n}: its windows in its documents' order", mine == [w for _, _, ws in kept[n] for w in ws])
            check(f"build {n}: quota met", taken[n] >= quota[n])
            check(f"build {n}: whole documents while under", taken[n] - sum(len(a) for _, a in kept[n][-1][2]) < quota[n])
            ids = open(os.path.join(out, f"IDS_{n}.txt")).read().splitlines()
            check(f"build {n}: identifiers in order", ids == [i for i, _, _ in kept[n]])
        check("the separated web document kept in part", any(i.endswith("/web/sep") for i, _, _ in kept["web"])
              and b"\x1e" not in b"".join(a for _, a in records))
        check("a document of tables keeps nothing", not any(i.endswith("/tables") for n in cp.NAMES for i, _, _ in kept[n]))
        check("wikidata bytes raw", "é".encode() in b"".join(a for (_, a), lab in zip(records, labels) if lab == "wikidata"))

        total = dict.fromkeys(cp.NAMES, 0)
        for (_, a), n in zip(records, labels):
            total[n] += len(a)
        remaining = {n: labels.count(n) for n in cp.NAMES}
        written = dict.fromkeys(cp.NAMES, 0)
        least = True
        for (_, a), n in zip(records, labels):
            for m in cp.NAMES:
                if m == n or not remaining[m]:
                    continue
                mine, theirs = written[n] * total[m], written[m] * total[n]
                if (cp.NAMES.index(m) < cp.NAMES.index(n) and not mine < theirs) or (cp.NAMES.index(m) > cp.NAMES.index(n) and not mine <= theirs):
                    least = False
            written[n] += len(a)
            remaining[n] -= 1
        check("every record written by the slice of least progress", least)

        prefix_records, answers = [], 0
        for q, a in records:
            if answers >= prefix:
                break
            prefix_records.append(q + cp.US + a + cp.RS)
            answers += len(a)
        check("TRAIN is the prefix while its answers stand under P", train == b"".join(prefix_records) and passage.startswith(train))
        check("TRAIN reaches P", answers >= prefix and len(train) < len(passage))

        trained = {hashlib.sha256(t).digest() for n in cp.NAMES for _, t, _ in kept[n]}
        used, picks = expected_held(shards, order, trained, held)
        check("held from the far end, two shards", used == [FAR[1], FAR[0]])
        check("the fetches: the trained shards in order, then the far end backward", fetched == read + used)
        for n in cp.NAMES:
            got = list(cp.records(os.path.join(out, f"HELD_{n}.txt")))
            check(f"held {n}: its count", len(got) == held)
            check(f"held {n}: the middle windows", got == [p for _, p in picks[n]])
            hids = open(os.path.join(out, f"HELD_IDS_{n}.txt")).read().splitlines()
            check(f"held {n}: identifiers", hids == [i for i, _ in picks[n]])
            check(f"held {n}: from the far shards only", all(i.startswith(tuple(p + "/" for p in FAR)) for i in hids))
            check(f"held {n}: none trained", not set(hids) & {i for i, _, _ in kept[n]})
        check("held skips the document a training document holds", f"{FAR[1]}/dup" not in open(os.path.join(out, "HELD_IDS_web.txt")).read())
        first_code = next(r for r in shards[FAR[1]] if cp.slice_of(r) == "code")
        ws = cp.windows_of(first_code["title"].encode(), first_code["text"].encode())
        check("held window is the middle one", picks["code"][0] == (first_code["identifier"], ws[len(ws) // 2]))

        rows = [line.split("\t") for line in open(os.path.join(out, "MANIFEST.tsv")).read().splitlines()]
        head, body = rows[0], rows[1:]
        check("manifest head", head[:5] == ["role", "path", "octets", "sha256", "rows"] and len(head) == 5 + 2 * len(cp.NAMES))
        check("manifest roles", [(r[0], r[1]) for r in body] == [("train", p) for p in read] + [("held", p) for p in used])
        for r in body:
            local = os.path.join(src, r[1])
            check(f"manifest {r[0]} {r[1]}: octets, sha256, rows", int(r[2]) == os.path.getsize(local) and r[3] == cp.sha256_of(local)
                  and int(r[4]) == len(shards[r[1]]))
            if r[0] == "train":
                check(f"manifest {r[1]}: per slice", [int(x) for x in r[5:]] == [v for n in cp.NAMES for v in per_shard[r[1]][n]])
        for name in ("PASSAGE.txt", "TRAIN.txt", *(f"HELD_{n}.txt" for n in cp.NAMES)):
            p = os.path.join(out, name)
            check(f"printed {name}", f"CORPUS_FILE {name} octets={os.path.getsize(p)} sha256={cp.sha256_of(p)}" in lines)
        check("printed done", lines[-1].startswith(f"CORPUS_DONE shards_train={len(read)} shards_held={len(used)} "))
        check("read shards and windows removed", not any(f.endswith(".parquet") for _, _, fs in os.walk(cache) for f in fs)
              and not any(f.endswith(".windows") for f in os.listdir(out)))

    def run(**bounds):
        with tempfile.TemporaryDirectory() as root:
            src, cache, out = (os.path.join(root, d) for d in ("src", "cache", "out"))
            write_shards(src, shards)
            os.makedirs(out)
            return stopped(lambda: cp.build(order, fetcher(src, cache, []), out, answer_bytes, prefix, held, log=lambda s: None, **bounds))

    check("bound: shards", (run(max_shards=1) or "").startswith("CORPUS_STOPPED the training read 1 shards with quotas short: "))
    check("bound: held shards", (run(max_shards=5, max_held=1) or "").startswith("CORPUS_STOPPED the held windows read 1 shards"))
    ticks = itertools.count(0.0, 10.0)
    check("bound: early stop", (run(early=2, early_ms=1, clock=lambda: next(ticks)) or "").startswith("CORPUS_STOPPED the first 2 shards took "))
    ticks = itertools.count(0.0, 10.0)
    check("bound: early stop not reached", run(early=2, early_ms=10 ** 9, clock=lambda: next(ticks)) is None)

    with tempfile.TemporaryDirectory() as root:
        src, cache, out = (os.path.join(root, d) for d in ("src", "cache", "out"))
        both = {NEAR[0]: [row(f"{NEAR[0]}/{n}", *KINDS[n], "", text_of(n, 0, 1)) for n in cp.NAMES],
                NEAR[1]: [row(f"{NEAR[1]}/{n}", *KINDS[n], "", text_of(n, 1, 400)) for n in cp.NAMES]}
        write_shards(src, both)
        os.makedirs(out)
        message = stopped(lambda: cp.build(NEAR[:2], fetcher(src, cache, []), out, 10_000, 3_000, 1, log=lambda s: None))
        check("held refused at a trained shard", message == f"CORPUS_STOPPED the held windows reached {NEAR[1]}, which the training read")

        p = os.path.join(root, "broken.txt")
        with open(p, "wb") as f:
            f.write(b"q\x1fa\x1eq2\x1fa2")
        check("a passage ending inside a record refused", "ends inside a record" in (stopped(lambda: list(cp.records(p))) or ""))
        check("a standing out directory refused", "stands" in (stopped(lambda: cp.main([out])) or ""))
    print(f"corpus_passage controls: {len(PASSED)} passed")


if __name__ == "__main__":
    main()
