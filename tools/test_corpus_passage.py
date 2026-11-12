#!/usr/bin/env -S python3 -I
"""Controls of corpus_passage.py on drawn shards (parquet files written here with pyarrow; nothing is fetched). They run under
a python that holds pyarrow (on the PC, .local/venv-corpus), so they stand outside tools/gate.sh, whose python has none.

  order      the shards sort by (d, n, m) as integers, and the listing's other files are left out;
  slices     each slice's filter, and 'Open Government', other languages and other collections in none;
  windows    the line rule's windows: 256 bytes each from the first byte, the last taking a tail shorter than 256;
  runs       a slice with no line floor keeps a document as one piece; under the science floor the windows whose bytes stand
             under 25 times their lines are left out and the runs that stay are the pieces, with the count and the bytes left out;
  build      each slice takes whole documents while under its quota; no government, French or transcript text is kept; a
             store reads back piece by piece with its documents' ordinals, titles on the pieces that open, and both marks; a
             separator byte is a byte like any other; a document whose text an earlier one holds is left out; a document of
             tables keeps nothing, and one of prose around a table keeps two pieces;
  prefix     in each slice the prefix is the documents from the front while its text bytes stood under its share of P, with
             the SHA-256 of the store bytes they cover;
  held       the held documents come whole from the far end, never one whose text a training document or an earlier held
             one holds; a held read that reaches a trained shard is refused;
  manifest   each shard's octets, SHA-256 and rows, its documents and text bytes a slice, the identifiers in order, STORE.tsv's
             rows, and the printed SHA-256 of every store file;
  bounds     the shard bound, the held bound and the early stop each stop the run (CORPUS_STOPPED); a store whose bytes end
             inside a piece or run past its index is refused; a standing out directory is refused before anything is fetched.
"""
import hashlib
import itertools
import os
import shutil
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus_passage as cp  # noqa: E402

PASSED = []

KINDS = {  # open_type, collection, language
    "code": ("Open Source", "GitHub", "Python"),
    "web": ("Open Web", "Wikipedia", "English"),
    "science": ("Open Science", "OpenAlex", "English"),
    "books": ("Open Culture", "English-PD", "English"),
    "wikidata": ("Semantic data", "Wikidata", "German"),
}
LETTER = {"code": "c", "web": "w", "science": "s", "books": "b", "wikidata": "d"}
NEAR = [f"common_corpus_1/subset_1_{m}.parquet" for m in range(1, 6)]
FAR = ["common_corpus_2/subset_1_1.parquet", "common_corpus_2/subset_2_1.parquet"]
TABLE = ("s" * 9 + "\n") * 60


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
    transcript, an empty and a table document; the first near shard holds a science document of prose around a table; the second
    holds a web document with a separator byte and one whose text is the first web document's; the far end holds a web document
    whose text is the first web document's and two code documents of one text."""
    counter = dict.fromkeys(cp.NAMES, 0)
    shards = {}
    first_web = None
    for path in NEAR + FAR:
        rows = [row(f"{path}/gov", "Open Government", "Caselaw Access Project", "English", "GOVERNMENT", "GOVERNMENT\n" * 50),
                row(f"{path}/tables", *KINDS["science"], "TABLES", TABLE)]
        if path == FAR[-1]:
            rows.append(row(f"{path}/dup", *KINDS["web"], "WEB again", first_web))
            twin = text_of("code", 777, 9)
            rows.append(row(f"{path}/code/twin1", *KINDS["code"], "CODE twin", twin))
            rows.append(row(f"{path}/code/twin2", *KINDS["code"], "CODE twin again", twin))
        if path == NEAR[0]:
            rows.append(row(f"{path}/science/mixed", *KINDS["science"], "SCIENCE mixed",
                            text_of("science", 888, 20) + TABLE + text_of("science", 889, 20)))
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
            rows.append(row(f"{path}/web/again", *KINDS["web"], "WEB once more", first_web))
            rows.append(row(f"{path}/web/sep", *KINDS["web"], "WEB \x1f separated", line * 3 + "\x1e" + line * 4))
        rows.append(row(f"{path}/french", "Open Web", "Wikipedia", "French", "FRENCH", "FRENCH\n" * 60))
        rows.append(row(f"{path}/youtube", "Open Web", "YouTube-Commons", "English", "YOUTUBE", "YOUTUBE\n" * 60))
        rows.append(row(f"{path}/empty", *KINDS["code"], "EMPTY", ""))
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


def runs_restated(name, text):
    """The line rule restated byte by byte: a window is 256 bytes, the last takes the tail, and a window whose bytes stand
    under 25 a line is left out."""
    if name != "science":
        return [(0, len(text))] if text else []
    n = len(text)
    bounds = [0] if 0 < n < 256 else [s for s in range(0, n, 256) if n - s >= 256]
    keep = []
    for i, s in enumerate(bounds):
        e = n if i == len(bounds) - 1 else s + 256
        lines = text[s:e].count(b"\n") + 1
        keep.append((s, e, (e - s) >= 25 * lines))
    runs = []
    for s, e, ok in keep:
        if not ok:
            continue
        if runs and runs[-1][1] == s:
            runs[-1] = (runs[-1][0], e)
        else:
            runs.append((s, e))
    return runs


def expected_pieces(ordinal, r, runs):
    title, text = r["title"].encode(), r["text"].encode()
    return [(ordinal, title if s == 0 else b"", text[s:e], s == 0, e == len(text)) for s, e in runs]


def expected_train(shards, order, quota, prefix_quota):
    """The rule restated on the drawn rows: the shards read, each slice's kept documents in order, each shard's counts, the
    repeated documents, and each slice's prefix as a count of documents."""
    taken = dict.fromkeys(cp.NAMES, 0)
    kept = {n: [] for n in cp.NAMES}
    prefix = dict.fromkeys(cp.NAMES)
    seen, repeated = set(), {n: [] for n in cp.NAMES}
    emptied, left = dict.fromkeys(cp.NAMES, 0), {n: [0, 0] for n in cp.NAMES}
    read, per_shard = [], {}
    for path in order:
        if all(taken[n] >= quota[n] for n in cp.NAMES):
            break
        read.append(path)
        counts = {n: [0, 0] for n in cp.NAMES}
        for r in shards[path]:
            name = cp.slice_of(r)
            text = r["text"].encode()
            if name is None or taken[name] >= quota[name] or not text:
                continue
            if text in seen:
                repeated[name].append(r["identifier"])
                continue
            runs = runs_restated(name, text)
            if name == "science":
                kept_windows = sum(1 for s, e in cp.windows_of(len(text)) if any(a <= s and e <= b for a, b in runs))
                left[name][0] += len(cp.windows_of(len(text))) - kept_windows
                left[name][1] += len(text) - sum(e - s for s, e in runs)
            if not runs:
                emptied[name] += 1
                continue
            seen.add(text)
            got = sum(e - s for s, e in runs)
            kept[name].append((r["identifier"], r, runs, got))
            taken[name] += got
            counts[name][0] += 1
            counts[name][1] += got
            if prefix[name] is None and taken[name] >= prefix_quota[name]:
                prefix[name] = len(kept[name])
        per_shard[path] = counts
    return read, taken, kept, per_shard, repeated, prefix, seen, emptied, left


def expected_held(shards, order, seen, held):
    seen = set(seen)
    want = dict.fromkeys(cp.NAMES, held)
    picks = {n: [] for n in cp.NAMES}
    used, per_shard = [], {}
    for path in reversed(order):
        if not any(want.values()):
            break
        used.append(path)
        counts = {n: [0, 0] for n in cp.NAMES}
        for r in shards[path]:
            name = cp.slice_of(r)
            text = r["text"].encode()
            if name is None or not want[name] or not text or text in seen:
                continue
            runs = runs_restated(name, text)
            if not runs:
                continue
            seen.add(text)
            picks[name].append((r["identifier"], r, runs))
            want[name] -= 1
            counts[name][0] += 1
            counts[name][1] += sum(e - s for s, e in runs)
        per_shard[path] = counts
    return used, picks, per_shard


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

    for length, want in ((0, []), (1, [(0, 1)]), (255, [(0, 255)]), (256, [(0, 256)]), (511, [(0, 511)]), (512, [(0, 256), (256, 512)]),
                         (600, [(0, 256), (256, 600)]), (1068, [(0, 256), (256, 512), (512, 768), (768, 1068)])):
        check(f"windows of {length} bytes", cp.windows_of(length) == want)
    check("a window at the floor stays", not cp.thin(b"x" * 49 + b"\n", 25))
    check("a window under the floor is thin", cp.thin(b"x" * 48 + b"\n", 25))

    prose, table = (b"p" * 63 + b"\n") * 4, (b"t" * 7 + b"\n") * 32
    check("runs: one piece where no floor stands", cp.runs_of("web", table * 3) == ([(0, 768)], 0, 0))
    check("runs: no piece of an empty text", cp.runs_of("web", b"") == ([], 0, 0) and cp.runs_of("science", b"") == ([], 0, 0))
    check("runs: science prose is one piece", cp.runs_of("science", prose * 3) == ([(0, 768)], 0, 0))
    check("runs: a table inside", cp.runs_of("science", prose * 2 + table + prose + b"tail") == ([(0, 512), (768, 1028)], 1, 256))
    check("runs: a table first", cp.runs_of("science", table + prose) == ([(256, 512)], 1, 256))
    check("runs: a table last takes the tail", cp.runs_of("science", prose + table + b"t\n") == ([(0, 256)], 1, 258))
    check("runs: tables alone", cp.runs_of("science", table * 2) == ([], 2, 512))
    for text in (prose * 2 + table + prose + b"tail", table + prose, prose + table + b"t\n", table * 2, prose[:100], table[:100], b""):
        check(f"runs restated on {len(text)} bytes", cp.runs_of("science", text)[0] == runs_restated("science", text))

    shards = draw()
    order = cp.order_of(list(shards))
    check("drawn order", order == NEAR + FAR)
    text_bytes, prefix_bytes, held = 10_000, 3_000, 3
    quota = {n: text_bytes * share // 100 for n, share, _ in cp.SLICES}
    prefix_quota = {n: prefix_bytes * share // 100 for n, share, _ in cp.SLICES}
    with tempfile.TemporaryDirectory() as root:
        src, cache, out = (os.path.join(root, d) for d in ("src", "cache", "out"))
        write_shards(src, shards)
        os.makedirs(out)
        fetched, lines = [], []
        cp.build(order, fetcher(src, cache, fetched), out, text_bytes, prefix_bytes, held, log=lines.append, max_shards=5, max_held=2)
        read, taken, kept, per_shard, repeated, prefix, seen, emptied, left = expected_train(shards, order, quota, prefix_quota)
        check("drawn quotas fill before the far shards", len(read) < len(NEAR))
        store = {(r[0], r[1]): r for r in (line.split("\t") for line in open(os.path.join(out, "STORE.tsv")).read().splitlines()[1:])}
        check("store head", open(os.path.join(out, "STORE.tsv")).readline() == cp.STORE_HEAD)
        check("store rows", list(store) == [(role, n) for role in ("train", "prefix", "held") for n in cp.NAMES])
        bins = {n: open(os.path.join(out, f"DOCS_{n}.bin"), "rb").read() for n in cp.NAMES}
        check("no government, French or transcript text", all(m not in b for m in (b"GOVERNMENT", b"FRENCH", b"YOUTUBE") for b in bins.values()))
        for n in cp.NAMES:
            got = list(cp.pieces(out, n))
            want = [p for k, (_, r, runs, _) in enumerate(kept[n]) for p in expected_pieces(k, r, runs)]
            check(f"build {n}: its pieces in its documents' order", got == want)
            check(f"build {n}: quota met", taken[n] >= quota[n])
            check(f"build {n}: whole documents while under", taken[n] - kept[n][-1][3] < quota[n])
            ids = open(os.path.join(out, f"IDS_{n}.txt")).read().splitlines()
            check(f"build {n}: identifiers in order", ids == [i for i, _, _, _ in kept[n]])
            row_ = store[("train", n)]
            check(f"store train {n}", row_[2:] == [str(dict((a, b) for a, b, _ in cp.SLICES)[n]), str(cp.LINE_FLOOR.get(n, 0)), str(len(kept[n])),
                                                   str(len(want)), str(taken[n]), str(len(bins[n])), hashlib.sha256(bins[n]).hexdigest()])
            front = [p for p in want if p[0] < prefix[n]]
            octets = sum(len(t) + len(x) for _, t, x, _, _ in front)
            texts = sum(len(x) for _, _, x, _, _ in front)
            check(f"prefix {n}: the front documents while under its share of P", texts >= prefix_quota[n]
                  and texts - sum(len(x) for d, _, x, _, _ in front if d == prefix[n] - 1) < prefix_quota[n])
            check(f"prefix {n}: its row", store[("prefix", n)][4:] == [str(prefix[n]), str(len(front)), str(texts), str(octets),
                                                                        hashlib.sha256(bins[n][:octets]).hexdigest()])
            check(f"prefix {n}: under the whole", prefix[n] < len(kept[n]))
        check("a separator byte is a byte", any(i.endswith("/web/sep") for i, _, _, _ in kept["web"]) and b"\x1e" in bins["web"]
              and b"WEB \x1f separated" in bins["web"])
        check("a repeated document is left out", repeated["web"] == [f"{NEAR[1]}/web/again"]
              and not any(i.endswith("/web/again") for i, _, _, _ in kept["web"]))
        check("a document of tables keeps nothing", not any(i.endswith("/tables") for n in cp.NAMES for i, _, _, _ in kept[n]))
        mixed = [p for p in cp.pieces(out, "science") if p[1] == b"SCIENCE mixed" or (p[1] == b"" and not p[3])]
        check("prose around a table keeps two pieces", [(p[3], p[4]) for p in mixed] == [(True, False), (False, True)]
              and mixed[0][0] == mixed[1][0] and TABLE.encode()[:256] not in mixed[0][2] + mixed[1][2])
        check("wikidata bytes raw", "é".encode() in bins["wikidata"])
        slice_lines = {line.split()[1]: line for line in lines if line.startswith("CORPUS_SLICE ")}
        check("printed slices", all(f"quota={quota[n]} text_bytes={taken[n]} documents={len(kept[n])} " in slice_lines[n] for n in cp.NAMES))
        check("printed repeats", slice_lines["web"].endswith("documents_repeated=1") and slice_lines["code"].endswith("documents_repeated=0"))
        check("printed emptied documents", emptied["science"] >= 1 and all(
            slice_lines[n].split("documents_emptied=")[1].split()[0] == str(emptied[n]) for n in cp.NAMES))
        check("printed windows left out", all(f"windows_left_out={left[n][0]} bytes_left_out={left[n][1]} " in slice_lines[n] for n in cp.NAMES)
              and left["science"][0] >= 3 and left["web"] == [0, 0])

        used, picks, held_shard = expected_held(shards, order, seen, held)
        check("held from the far end, two shards", used == [FAR[1], FAR[0]])
        check("the fetches: the trained shards in order, then the far end backward", fetched == read + used)
        for n in cp.NAMES:
            got = list(cp.pieces(out, n, stem="HELD"))
            want = [p for k, (_, r, runs) in enumerate(picks[n]) for p in expected_pieces(k, r, runs)]
            check(f"held {n}: its count", len(picks[n]) == held and len({p[0] for p in got}) == held)
            check(f"held {n}: whole documents", got == want)
            hids = open(os.path.join(out, f"HELD_IDS_{n}.txt")).read().splitlines()
            check(f"held {n}: identifiers", hids == [i for i, _, _ in picks[n]])
            check(f"held {n}: from the far shards only", all(i.startswith(tuple(p + "/" for p in FAR)) for i in hids))
            check(f"held {n}: none trained", not set(hids) & {i for i, _, _, _ in kept[n]})
            data = open(os.path.join(out, f"HELD_{n}.bin"), "rb").read()
            check(f"store held {n}", store[("held", n)][4:] == [str(held), str(len(want)), str(sum(len(x) for _, _, x, _, _ in want)),
                                                                str(len(data)), hashlib.sha256(data).hexdigest()])
        held_web = open(os.path.join(out, "HELD_IDS_web.txt")).read()
        check("held skips the document a training document holds", f"{FAR[1]}/dup" not in held_web)
        held_code = open(os.path.join(out, "HELD_IDS_code.txt")).read().splitlines()
        check("held skips the document an earlier held one holds", f"{FAR[1]}/code/twin1" in held_code and f"{FAR[1]}/code/twin2" not in held_code)
        check("printed held", "CORPUS_HELD documents=3 a slice; documents skipped as shared with training or an earlier held one 2" in lines)

        rows = [line.split("\t") for line in open(os.path.join(out, "MANIFEST.tsv")).read().splitlines()]
        head, body = rows[0], rows[1:]
        check("manifest head", head[:5] == ["role", "path", "octets", "sha256", "rows"] and len(head) == 5 + 2 * len(cp.NAMES))
        check("manifest roles", [(r[0], r[1]) for r in body] == [("train", p) for p in read] + [("held", p) for p in used])
        for r in body:
            local = os.path.join(src, r[1])
            check(f"manifest {r[0]} {r[1]}: octets, sha256, rows", int(r[2]) == os.path.getsize(local) and r[3] == cp.sha256_of(local)
                  and int(r[4]) == len(shards[r[1]]))
            counts = per_shard[r[1]] if r[0] == "train" else held_shard[r[1]]
            check(f"manifest {r[0]} {r[1]}: per slice", [int(x) for x in r[5:]] == [v for n in cp.NAMES for v in counts[n]])
        names = ["STORE.tsv", "MANIFEST.tsv"] + [f for n in cp.NAMES for f in (f"DOCS_{n}.bin", f"DOCS_{n}.tsv", f"IDS_{n}.txt")] \
            + [f for n in cp.NAMES for f in (f"HELD_{n}.bin", f"HELD_{n}.tsv", f"HELD_IDS_{n}.txt")]
        for name in names:
            p = os.path.join(out, name)
            check(f"printed {name}", f"CORPUS_FILE {name} octets={os.path.getsize(p)} sha256={cp.sha256_of(p)}" in lines)
        check("every file written is printed", sorted(names) == sorted(os.listdir(out)))
        for role in ("train", "prefix", "held"):
            for n in cp.NAMES:
                r = store[(role, n)]
                check(f"printed store {role} {n}", f"CORPUS_STORE role={role} slice={n} documents={r[4]} pieces={r[5]} text_bytes={r[6]} "
                      f"octets={r[7]} sha256={r[8]}" in lines)
        check("printed done", lines[-1].startswith(f"CORPUS_DONE shards_train={len(read)} shards_held={len(used)} "))
        check("read shards removed", not any(f.endswith(".parquet") for _, _, fs in os.walk(cache) for f in fs))

        broken = os.path.join(root, "broken")
        os.makedirs(broken)
        for name, index, data in (("short", cp.INDEX_HEAD + "0\t1\t3\t1\t1\n", b"Tab"), ("long", cp.INDEX_HEAD + "0\t1\t3\t1\t1\n", b"Tabcd"),
                                  ("head", "document\ttext\n0\t1\t3\t1\t1\n", b"Tabc")):
            with open(os.path.join(broken, f"DOCS_{name}.tsv"), "w") as f:
                f.write(index)
            with open(os.path.join(broken, f"DOCS_{name}.bin"), "wb") as f:
                f.write(data)
        check("a store ending inside a piece refused", "ends inside a piece" in (stopped(lambda: list(cp.pieces(broken, "short"))) or ""))
        check("a store past its index refused", "past its index" in (stopped(lambda: list(cp.pieces(broken, "long"))) or ""))
        check("an index without its head refused", "head" in (stopped(lambda: list(cp.pieces(broken, "head"))) or ""))

    def run(**bounds):
        with tempfile.TemporaryDirectory() as root:
            src, cache, out = (os.path.join(root, d) for d in ("src", "cache", "out"))
            write_shards(src, shards)
            os.makedirs(out)
            return stopped(lambda: cp.build(order, fetcher(src, cache, []), out, text_bytes, prefix_bytes, held, log=lambda s: None, **bounds))

    check("bound: shards", (run(max_shards=1) or "").startswith("CORPUS_STOPPED the training read 1 shards with quotas short: "))
    check("bound: held shards", (run(max_shards=5, max_held=1) or "").startswith("CORPUS_STOPPED the held documents read 1 shards"))
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
        check("held refused at a trained shard", message == f"CORPUS_STOPPED the held documents reached {NEAR[1]}, which the training read")
        check("a standing out directory refused", "stands" in (stopped(lambda: cp.main([out])) or ""))
    print(f"corpus_passage controls: {len(PASSED)} passed")


if __name__ == "__main__":
    main()
