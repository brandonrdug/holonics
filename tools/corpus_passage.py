#!/usr/bin/env -S python3 -I
"""The wider passage's boundary codec (Brandon, November 12 16:13Z: neutral text past the code set, from Common Corpus,
without its government collection; the slices and the held cut follow the plan record of November 12). It writes a store
of documents. The cut of a document into regions is the trainer's, and no grid of regions is fixed here.

Usage: corpus_passage.py OUT [--revision REV] [--text-bytes N] [--prefix-bytes P] [--held K] [--cache DIR]
                             [--max-shards S] [--max-held-shards T] [--early E] [--early-ms MS]

The dataset is `PleIAs/common_corpus` at REV (`307910e4`, the prefix of one commit of its default branch, resolved to the
full commit). Its shards are `common_corpus_{d}/subset_{n}_{m}.parquet`, read in the order (d, n, m). A row falls in at
most one slice:

  code      open_type 'Open Source'                                                                  40 of each 100 bytes
  web       open_type 'Open Web', language 'English', collection Wikipedia, StackExchange or CCC      20
  science   open_type 'Open Science', language 'English'                                             20
  books     open_type 'Open Culture', language 'English', collection English-PD or US-PD-Books       12
  wikidata  open_type 'Semantic data'                                                                 8

and no row of 'Open Government' falls in any.

A slice's store is three files. `DOCS_<slice>.bin` holds its documents' bytes one after another, raw (a title and a text
are UTF-8 as the dataset gives them, and no byte is a separator). `DOCS_<slice>.tsv` holds one row a piece with its
document's ordinal in the slice, its title's octets, its text's octets and two marks, `opens` (the piece begins at its
document's first byte) and `closes` (it ends at the document's last byte); a piece's bytes are its title's and then its
text's, and only a piece that opens carries the title. `IDS_<slice>.txt` holds one identifier a document, by ordinal.

A document is one piece, except under a slice's line floor. The science slice has a floor of 25 bytes a line (its PDF
tables and figures arrive one number a line): its text is measured on windows of 256 bytes from its first byte, the last
window taking a tail shorter than 256, and a window whose bytes stand under 25 times its lines (its newlines plus one) is
left out. The runs of windows that stay are the document's pieces. The 256 is this rule's own grain, the one its rate was
measured at (7.6% of the science slice's windows on one shard, November 12); it is no extent of a training region. A
document with no window left is counted and writes nothing.

Why the marks: a region's question is the bytes before its answer, and a document's end is a true end. A piece that
does not open has no title before it, and one that does not close ends at a cut, so the trainer needs both.

From the front of the order each slice takes whole documents while its kept text bytes stand under its share of N
(8,000,000,000 text bytes). A document whose text's SHA-256 an earlier training document holds is left out and counted.
Each shard is read once and deleted, and its SHA-256 is kept. The smaller passage is a prefix: in each slice, the
documents from the front while its text bytes stood under its share of P (1,000,000,000). `STORE.tsv` gives each
slice's counts for the whole store, the prefix and the held store, with the SHA-256 of the bytes each covers.

Held: from the far end of the order backward, each slice takes K (128, the count of problems of the code line's held
passage, whose reads' spread is on record) whole documents whose text's SHA-256 stands in no training document and no
earlier held one, written the same way as `HELD_<slice>.bin`, `HELD_<slice>.tsv` and `HELD_IDS_<slice>.txt`. How much of a
held document a read takes is the read's. A held shard that the training already read is refused.

The run's bounds are its projection's upper ends (the slice plan's 96 shards, from one shard read whole, whose web yield
binds): it stops, reported incomplete (`CORPUS_STOPPED`), when the training has read S (120) shards with a quota still
short, when the held documents have read T (4) shards with a slice still short, or when its first E (8) training shards
took more than MS (40,000) ms a shard on the mean.

Also writes LISTING.tsv (the shards at the revision) and MANIFEST.tsv (each shard read, with its role, path, octets,
SHA-256, rows, and documents and text bytes a slice). Prints one line a shard with its own ms, each slice's counts, and
every store file's SHA-256. Dataset roles are exterior codec information, not native identities.
"""
import argparse
import hashlib
import os
import re
import sys
import time

LINE_GRID = 256
REPO = "PleIAs/common_corpus"
COLUMNS = ("identifier", "collection", "open_type", "language", "title", "text")
SHARD = re.compile(r"^common_corpus_(\d+)/subset_(\d+)_(\d+)\.parquet$")
WEB = ("Wikipedia", "StackExchange", "Creative Commons Common Crawl (CCC)")
BOOKS = ("English-PD", "US-PD-Books")
SLICES = (
    ("code", 40, lambda r: r["open_type"] == "Open Source"),
    ("web", 20, lambda r: r["open_type"] == "Open Web" and r["language"] == "English" and r["collection"] in WEB),
    ("science", 20, lambda r: r["open_type"] == "Open Science" and r["language"] == "English"),
    ("books", 12, lambda r: r["open_type"] == "Open Culture" and r["language"] == "English" and r["collection"] in BOOKS),
    ("wikidata", 8, lambda r: r["open_type"] == "Semantic data"),
)
NAMES = tuple(name for name, _, _ in SLICES)
LINE_FLOOR = {"science": 25}
INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"
STORE_HEAD = "role\tslice\tshare\tline_floor\tdocuments\tpieces\ttext_octets\tstore_octets\tsha256\n"


def order_of(paths):
    """The shards among `paths`, in the order (d, n, m)."""
    keyed = []
    for p in paths:
        m = SHARD.match(p)
        if m:
            keyed.append((tuple(int(g) for g in m.groups()), p))
    return [p for _, p in sorted(keyed)]


def slice_of(row):
    """The slice a row falls in, or None. 'Open Government' falls in none."""
    if row["open_type"] == "Open Government":
        return None
    for name, _, test in SLICES:
        if test(row):
            return name
    return None


def windows_of(length):
    """The line rule's windows over a text of `length` bytes, (start, end): 256 bytes each from the first byte, the last one
    taking a tail shorter than 256."""
    starts = list(range(0, length - LINE_GRID + 1, LINE_GRID)) or ([0] if length else [])
    return [(s, length if s == starts[-1] else s + LINE_GRID) for s in starts]


def thin(window, floor):
    """Whether a window's bytes stand under `floor` times its lines (its newlines plus one)."""
    return len(window) < floor * (window.count(b"\n") + 1)


def runs_of(name, text):
    """A document's pieces as (start, end) in its text, and the count and bytes of the windows its slice's line floor
    left out. A slice with no floor keeps the document as one piece."""
    floor = LINE_FLOOR.get(name)
    if not floor:
        return ([(0, len(text))] if text else []), 0, 0
    runs, start, left, left_bytes = [], None, 0, 0
    for s, e in windows_of(len(text)):
        if thin(text[s:e], floor):
            left += 1
            left_bytes += e - s
            if start is not None:
                runs.append((start, s))
                start = None
        elif start is None:
            start = s
    if start is not None:
        runs.append((start, len(text)))
    return runs, left, left_bytes


def rows_of(local):
    """A shard's rows, each a dict of COLUMNS with the title and text as UTF-8 bytes."""
    import pyarrow.parquet as pq

    pf = pq.ParquetFile(local)
    for batch in pf.iter_batches(batch_size=1024, columns=list(COLUMNS)):
        cols = {c: batch.column(c).to_pylist() for c in COLUMNS}
        for i in range(batch.num_rows):
            row = {c: cols[c][i] for c in COLUMNS}
            row["title"] = (row["title"] or "").encode("utf-8")
            row["text"] = (row["text"] or "").encode("utf-8")
            yield row


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 24), b""):
            h.update(chunk)
    return h.hexdigest()


class Store:
    """A slice's store while it is written: the bytes, the index, the identifiers, the counts and the bytes' SHA-256."""

    def __init__(self, out, stem, ids_stem, name):
        self.names = (f"{stem}_{name}.bin", f"{stem}_{name}.tsv", f"{ids_stem}_{name}.txt")
        self.bin = open(os.path.join(out, self.names[0]), "wb")
        self.tsv = open(os.path.join(out, self.names[1]), "w")
        self.ids = open(os.path.join(out, self.names[2]), "w")
        self.tsv.write(INDEX_HEAD)
        self.sha = hashlib.sha256()
        self.documents = self.pieces = self.text_octets = self.octets = 0

    def add(self, identifier, title, text, runs):
        """Writes a document's pieces and returns its kept text bytes."""
        got = 0
        for start, end in runs:
            opens, closes = start == 0, end == len(text)
            body = (title if opens else b"") + text[start:end]
            self.bin.write(body)
            self.sha.update(body)
            self.tsv.write(f"{self.documents}\t{len(title) if opens else 0}\t{end - start}\t{int(opens)}\t{int(closes)}\n")
            self.pieces += 1
            self.octets += len(body)
            got += end - start
        self.ids.write(str(identifier).replace("\n", " ") + "\n")
        self.documents += 1
        self.text_octets += got
        return got

    def counts(self):
        return f"{self.documents}\t{self.pieces}\t{self.text_octets}\t{self.octets}\t{self.sha.copy().hexdigest()}"

    def close(self):
        for f in (self.bin, self.tsv, self.ids):
            f.close()


def pieces(out, name, stem="DOCS"):
    """A written store's pieces in order: (document, title, text, opens, closes), the title and text as bytes."""
    with open(os.path.join(out, f"{stem}_{name}.tsv")) as tsv, open(os.path.join(out, f"{stem}_{name}.bin"), "rb") as data:
        if tsv.readline() != INDEX_HEAD:
            raise SystemExit(f"{stem}_{name}.tsv does not open with the index's head")
        for line in tsv:
            document, title_octets, text_octets, opens, closes = (int(x) for x in line.split("\t"))
            title, text = data.read(title_octets), data.read(text_octets)
            if len(title) != title_octets or len(text) != text_octets:
                raise SystemExit(f"{stem}_{name}.bin ends inside a piece")
            yield document, title, text, bool(opens), bool(closes)
        if data.read(1):
            raise SystemExit(f"{stem}_{name}.bin holds bytes past its index")


def build(order, fetch, out, text_bytes, prefix_bytes, held, remove=True, log=print, max_shards=None, max_held=None, early=0,
          early_ms=None, clock=time.monotonic):
    """The stores, the prefix's counts and the held stores from the shards in `order` (`fetch(path)` gives a local file)."""
    started = clock()
    ms = lambda: int((clock() - started) * 1000)  # noqa: E731
    share = {name: s for name, s, _ in SLICES}
    quota = {name: text_bytes * share[name] // 100 for name in NAMES}
    prefix_quota = {name: prefix_bytes * share[name] // 100 for name in NAMES}
    stores = {n: Store(out, "DOCS", "IDS", n) for n in NAMES}
    prefix = dict.fromkeys(NAMES)
    left = {n: [0, 0, 0, 0] for n in NAMES}  # windows left out, their bytes, documents with nothing kept, repeated documents
    trained = set()
    manifest = open(os.path.join(out, "MANIFEST.tsv"), "w")
    manifest.write("role\tpath\toctets\tsha256\trows\t" + "\t".join(f"{n}_documents\t{n}_text_bytes" for n in NAMES) + "\n")
    taken = lambda n: stores[n].text_octets  # noqa: E731
    read, times = [], []
    for path in order:
        if all(taken(n) >= quota[n] for n in NAMES):
            break
        if max_shards is not None and len(read) == max_shards:
            short = ", ".join(f"{n} {taken(n)} of {quota[n]}" for n in NAMES if taken(n) < quota[n])
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the training read {max_shards} shards with quotas short: {short}")
        shard_start = ms()
        local = fetch(path)
        octets, digest = os.path.getsize(local), sha256_of(local)
        rows, kept_docs, kept_bytes = 0, dict.fromkeys(NAMES, 0), dict.fromkeys(NAMES, 0)
        for row in rows_of(local):
            rows += 1
            name = slice_of(row)
            if name is None or taken(name) >= quota[name] or not row["text"]:
                continue
            key = hashlib.sha256(row["text"]).digest()
            if key in trained:
                left[name][3] += 1
                continue
            runs, windows, window_bytes = runs_of(name, row["text"])
            left[name][0] += windows
            left[name][1] += window_bytes
            if not runs:
                left[name][2] += 1
                continue
            got = stores[name].add(row["identifier"], row["title"], row["text"], runs)
            trained.add(key)
            kept_docs[name] += 1
            kept_bytes[name] += got
            if prefix[name] is None and taken(name) >= prefix_quota[name]:
                prefix[name] = stores[name].counts()
        read.append(path)
        manifest.write(f"train\t{path}\t{octets}\t{digest}\t{rows}\t" + "\t".join(f"{kept_docs[n]}\t{kept_bytes[n]}" for n in NAMES) + "\n")
        manifest.flush()
        if remove:
            os.remove(local)
        times.append(ms() - shard_start)
        log(f"CORPUS_SHARD role=train k={len(read)} path={path} octets={octets} rows={rows} " + " ".join(f"{n}={taken(n)}" for n in NAMES)
            + f" shard_ms={times[-1]} ms={ms()}")
        if early and len(times) == early and early_ms is not None and sum(times) > early * early_ms:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the first {early} shards took {sum(times) // early} ms a shard, past {early_ms}")
    for s in stores.values():
        s.close()
    short = [n for n in NAMES if taken(n) < quota[n]]
    if short:
        manifest.close()
        raise SystemExit(f"CORPUS_STOPPED the order ran out before the quotas of {', '.join(short)}")

    # The held documents, from the far end backward.
    helds = {n: Store(out, "HELD", "HELD_IDS", n) for n in NAMES}
    want = dict.fromkeys(NAMES, held)
    shared, held_read = 0, 0
    for path in reversed(order):
        if not any(want.values()):
            break
        if path in read:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the held documents reached {path}, which the training read")
        if max_held is not None and held_read == max_held:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the held documents read {max_held} shards with slices short: "
                             + ", ".join(f"{n} {held - want[n]} of {held}" for n in NAMES if want[n]))
        shard_start = ms()
        local = fetch(path)
        octets, digest = os.path.getsize(local), sha256_of(local)
        rows, kept, kept_bytes = 0, dict.fromkeys(NAMES, 0), dict.fromkeys(NAMES, 0)
        for row in rows_of(local):
            rows += 1
            name = slice_of(row)
            if name is None or not want[name] or not row["text"]:
                continue
            key = hashlib.sha256(row["text"]).digest()
            if key in trained:
                shared += 1
                continue
            runs, _, _ = runs_of(name, row["text"])
            if not runs:
                continue
            kept_bytes[name] += helds[name].add(row["identifier"], row["title"], row["text"], runs)
            trained.add(key)
            want[name] -= 1
            kept[name] += 1
        held_read += 1
        manifest.write(f"held\t{path}\t{octets}\t{digest}\t{rows}\t" + "\t".join(f"{kept[n]}\t{kept_bytes[n]}" for n in NAMES) + "\n")
        manifest.flush()
        if remove:
            os.remove(local)
        log(f"CORPUS_SHARD role=held k={held_read} path={path} octets={octets} rows={rows} " + " ".join(f"{n}={held - want[n]}" for n in NAMES)
            + f" shard_ms={ms() - shard_start} ms={ms()}")
    for s in helds.values():
        s.close()
    manifest.close()
    if any(want.values()):
        raise SystemExit("CORPUS_STOPPED the order ran out before the held documents")

    with open(os.path.join(out, "STORE.tsv"), "w") as f:
        f.write(STORE_HEAD)
        for role, of in (("train", lambda n: stores[n].counts()), ("prefix", lambda n: prefix[n] or stores[n].counts()),
                         ("held", lambda n: helds[n].counts())):
            for n in NAMES:
                f.write(f"{role}\t{n}\t{share[n]}\t{LINE_FLOOR.get(n, 0)}\t{of(n)}\n")
                documents, count, text_octets, store_octets, sha = of(n).split("\t")
                log(f"CORPUS_STORE role={role} slice={n} documents={documents} pieces={count} text_bytes={text_octets} "
                    f"octets={store_octets} sha256={sha}")
    for n in NAMES:
        log(f"CORPUS_SLICE {n} quota={quota[n]} text_bytes={taken(n)} documents={stores[n].documents} pieces={stores[n].pieces} "
            f"windows_left_out={left[n][0]} bytes_left_out={left[n][1]} documents_emptied={left[n][2]} documents_repeated={left[n][3]}")
    log(f"CORPUS_HELD documents={held} a slice; documents skipped as shared with training or an earlier held one {shared}")
    for name in ("STORE.tsv", "MANIFEST.tsv", *(f for n in NAMES for f in stores[n].names), *(f for n in NAMES for f in helds[n].names)):
        p = os.path.join(out, name)
        log(f"CORPUS_FILE {name} octets={os.path.getsize(p)} sha256={sha256_of(p)}")
    log(f"CORPUS_DONE shards_train={len(read)} shards_held={held_read} ms={ms()}")


def resolve(api, revision):
    """The full commit of `revision`: the one commit of the default branch it prefixes, or else what the Hub resolves it to."""
    hits = [c.commit_id for c in api.list_repo_commits(REPO, repo_type="dataset") if c.commit_id.startswith(revision)]
    if len(hits) > 1:
        sys.exit(f"revision {revision} prefixes {len(hits)} commits")
    if hits:
        return hits[0]
    sha = api.dataset_info(REPO, revision=revision).sha
    if re.fullmatch(r"[0-9a-f]{7,40}", revision) and not sha.startswith(revision):
        sys.exit(f"revision {revision} resolved to {sha}")
    return sha


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("out")
    ap.add_argument("--revision", default="307910e4")
    ap.add_argument("--text-bytes", type=int, default=8_000_000_000)
    ap.add_argument("--prefix-bytes", type=int, default=1_000_000_000)
    ap.add_argument("--held", type=int, default=128)
    ap.add_argument("--cache", default=None, help="where a shard stands while it is read (default OUT/cache)")
    ap.add_argument("--max-shards", type=int, default=120)
    ap.add_argument("--max-held-shards", type=int, default=4)
    ap.add_argument("--early", type=int, default=8)
    ap.add_argument("--early-ms", type=int, default=40_000)
    args = ap.parse_args(argv)
    if os.path.exists(args.out):
        sys.exit(f"{args.out} stands; a store is written under a new directory")
    from huggingface_hub import HfApi, hf_hub_download

    api = HfApi()
    sha = resolve(api, args.revision)
    os.makedirs(args.out)
    cache = args.cache or os.path.join(args.out, "cache")
    files = api.list_repo_files(REPO, repo_type="dataset", revision=sha)
    order = order_of(files)
    with open(os.path.join(args.out, "LISTING.tsv"), "w") as f:
        f.write(f"# {REPO} at {sha}: {len(files)} files, {len(order)} shards in order\n")
        f.writelines(p + "\n" for p in order)
    print(f"CORPUS_REVISION {REPO} {sha} files={len(files)} shards={len(order)}", flush=True)

    def fetch(path):
        return hf_hub_download(REPO, path, repo_type="dataset", revision=sha, local_dir=cache)

    build(order, fetch, args.out, args.text_bytes, args.prefix_bytes, args.held, log=lambda s: print(s, flush=True),
          max_shards=args.max_shards, max_held=args.max_held_shards, early=args.early, early_ms=args.early_ms)


if __name__ == "__main__":
    main()
