#!/usr/bin/env -S python3 -I
"""The wider passage's boundary codec (Brandon, November 12 16:13Z: neutral text past the code set, from Common Corpus,
without its government collection; the slices, the grid and the held cut follow the Fable thread's plan of November 12
16:35Z).

Usage: corpus_passage.py OUT [--revision REV] [--answer-bytes N] [--prefix-bytes P] [--held K] [--cache DIR]
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

A document (its text's UTF-8 bytes) is read on a fixed grid of 256-byte answers from its first byte, each with the 256
bytes before it as its question; the first answer's question is the title line (the title's first 255 bytes and a
newline). Each window is a record `question US answer RS` (US 0x1F, RS 0x1E), as field_train.rs `problems_of` reads one,
raw bytes. So a passage file holds about twice its answer bytes. Two kinds of window are dropped and counted: one whose
question or answer holds a separator, and a science window whose answer's lines average under 25 bytes (its bytes under
25 times its newlines plus one; PDF tables).

From the front of the order each slice takes whole documents while its answer bytes stand under its share of N
(8,000,000,000 answer bytes). Each shard is read once and deleted, and its SHA-256 is kept. The slices then interleave by
the smallest share of their progress (the answer bytes written over the slice's own total; ties by the table's order), so
every stretch holds the mix. PASSAGE.txt holds every kept window, and TRAIN.txt its prefix while the answer bytes written
stand under P (1,000,000,000), so the smaller passage is a prefix of the larger.

Held: from the far end of the order backward, each slice takes K (128) windows, one a document, from documents whose
text's SHA-256 stands in no training document. The window taken is the document's middle one (index windows // 2), or the
first kept window after it, written to HELD_<slice>.txt. A held shard that the training already read is refused.

The run's bounds are its projection's upper ends (the slice plan's 96 shards, from one shard read whole, whose web yield
binds): it stops, reported incomplete (`CORPUS_STOPPED`), when the training has read S (120) shards with a quota still
short, when the held windows have read T (4) shards with a slice still short, or when its first E (8) training shards
took more than MS (40,000) ms a shard on the mean.

Writes:
- LISTING.tsv: the shards at the revision;
- MANIFEST.tsv: each shard read, with its role, path, octets, SHA-256, rows, and documents and answer bytes a slice;
- IDS_<slice>.txt and HELD_IDS_<slice>.txt: the documents' identifiers in order.
Prints one line a shard with its own ms, each slice's counts and drops, and every passage's SHA-256. Dataset roles are
exterior codec information, not native identities.
"""
import argparse
import hashlib
import os
import re
import sys
import time

RS, US = b"\x1e", b"\x1f"
GRID = 256
TITLE = GRID - 1
LINE_FLOOR = 25
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


def windows_of(title, text):
    """A document's windows on the grid, (question, answer) byte strings."""
    head = title[:TITLE] + b"\n"
    return [(head if s == 0 else text[s - GRID:s], text[s:s + GRID]) for s in range(0, len(text), GRID)]


def dropped(name, question, answer):
    """Why a window is dropped, or None."""
    if RS in question or US in question or RS in answer or US in answer:
        return "separator"
    if name == "science" and len(answer) < LINE_FLOOR * (answer.count(b"\n") + 1):
        return "lines"
    return None


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


def records(path):
    """The records of a passage file, (question, answer), read in chunks."""
    with open(path, "rb") as f:
        rest = b""
        for chunk in iter(lambda: f.read(1 << 24), b""):
            parts = (rest + chunk).split(RS)
            rest = parts.pop()
            for record in parts:
                cut = record.find(US)
                yield record[:cut], record[cut + 1:]
        if rest:
            raise SystemExit(f"{path} ends inside a record")


def build(order, fetch, out, answer_bytes, prefix_bytes, held, remove=True, log=print, max_shards=None, max_held=None, early=0,
          early_ms=None, clock=time.monotonic):
    """The passage, its prefix and the held windows from the shards in `order` (`fetch(path)` gives a local file)."""
    started = clock()
    ms = lambda: int((clock() - started) * 1000)  # noqa: E731
    quota = {name: answer_bytes * share // 100 for name, share, _ in SLICES}
    taken = dict.fromkeys(NAMES, 0)
    docs = dict.fromkeys(NAMES, 0)
    windows = dict.fromkeys(NAMES, 0)
    drops = {(n, why): 0 for n in NAMES for why in ("separator", "lines")}
    trained = set()
    manifest = open(os.path.join(out, "MANIFEST.tsv"), "w")
    manifest.write("role\tpath\toctets\tsha256\trows\t" + "\t".join(f"{n}_documents\t{n}_answer_bytes" for n in NAMES) + "\n")
    parts = {n: open(os.path.join(out, f"slice_{n}.windows"), "wb") for n in NAMES}
    ids = {n: open(os.path.join(out, f"IDS_{n}.txt"), "w") for n in NAMES}
    read, times = [], []
    for path in order:
        if all(taken[n] >= quota[n] for n in NAMES):
            break
        if max_shards is not None and len(read) == max_shards:
            short = ", ".join(f"{n} {taken[n]} of {quota[n]}" for n in NAMES if taken[n] < quota[n])
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the training read {max_shards} shards with quotas short: {short}")
        shard_start = ms()
        local = fetch(path)
        octets, digest = os.path.getsize(local), sha256_of(local)
        rows, kept_docs, kept_bytes = 0, dict.fromkeys(NAMES, 0), dict.fromkeys(NAMES, 0)
        for row in rows_of(local):
            rows += 1
            name = slice_of(row)
            if name is None or taken[name] >= quota[name] or not row["text"]:
                continue
            got = 0
            for q, a in windows_of(row["title"], row["text"]):
                why = dropped(name, q, a)
                if why:
                    drops[(name, why)] += 1
                    continue
                parts[name].write(q + US + a + RS)
                got += len(a)
                windows[name] += 1
            if got:
                taken[name] += got
                docs[name] += 1
                kept_docs[name] += 1
                kept_bytes[name] += got
                trained.add(hashlib.sha256(row["text"]).digest())
                ids[name].write(str(row["identifier"]).replace("\n", " ") + "\n")
        read.append(path)
        manifest.write(f"train\t{path}\t{octets}\t{digest}\t{rows}\t" + "\t".join(f"{kept_docs[n]}\t{kept_bytes[n]}" for n in NAMES) + "\n")
        manifest.flush()
        if remove:
            os.remove(local)
        times.append(ms() - shard_start)
        log(f"CORPUS_SHARD role=train k={len(read)} path={path} octets={octets} rows={rows} " + " ".join(f"{n}={taken[n]}" for n in NAMES)
            + f" shard_ms={times[-1]} ms={ms()}")
        if early and len(times) == early and early_ms is not None and sum(times) > early * early_ms:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the first {early} shards took {sum(times) // early} ms a shard, past {early_ms}")
    for f in (*parts.values(), *ids.values()):
        f.close()
    short = [n for n in NAMES if taken[n] < quota[n]]
    if short:
        manifest.close()
        raise SystemExit(f"CORPUS_STOPPED the order ran out before the quotas of {', '.join(short)}")

    # The interleave: the slice of least progress writes its next window (a/A < b/B as a·B < b·A, in integers).
    readers = {n: records(os.path.join(out, f"slice_{n}.windows")) for n in NAMES}
    written = dict.fromkeys(NAMES, 0)
    pending = {n: next(readers[n], None) for n in NAMES}
    answers = 0
    with open(os.path.join(out, "PASSAGE.txt"), "wb") as passage, open(os.path.join(out, "TRAIN.txt"), "wb") as train:
        while True:
            live = [n for n in NAMES if pending[n] is not None]
            if not live:
                break
            n = live[0]
            for m in live[1:]:
                if written[m] * taken[n] < written[n] * taken[m]:
                    n = m
            q, a = pending[n]
            record = q + US + a + RS
            passage.write(record)
            if answers < prefix_bytes:
                train.write(record)
            answers += len(a)
            written[n] += len(a)
            pending[n] = next(readers[n], None)
    if remove:
        for n in NAMES:
            os.remove(os.path.join(out, f"slice_{n}.windows"))
    log(f"CORPUS_INTERLEAVE answer_bytes={answers} ms={ms()}")

    # The held windows, from the far end backward.
    want = dict.fromkeys(NAMES, held)
    held_files = {n: open(os.path.join(out, f"HELD_{n}.txt"), "wb") for n in NAMES}
    held_ids = {n: open(os.path.join(out, f"HELD_IDS_{n}.txt"), "w") for n in NAMES}
    shared, held_read = 0, 0
    for path in reversed(order):
        if not any(want.values()):
            break
        if path in read:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the held windows reached {path}, which the training read")
        if max_held is not None and held_read == max_held:
            manifest.close()
            raise SystemExit(f"CORPUS_STOPPED the held windows read {max_held} shards with slices short: "
                             + ", ".join(f"{n} {held - want[n]} of {held}" for n in NAMES if want[n]))
        shard_start = ms()
        local = fetch(path)
        octets, digest = os.path.getsize(local), sha256_of(local)
        rows, kept = 0, dict.fromkeys(NAMES, 0)
        for row in rows_of(local):
            rows += 1
            name = slice_of(row)
            if name is None or not want[name] or not row["text"]:
                continue
            if hashlib.sha256(row["text"]).digest() in trained:
                shared += 1
                continue
            ws = windows_of(row["title"], row["text"])
            pick = next(((q, a) for q, a in ws[len(ws) // 2:] if not dropped(name, q, a)), None)
            if pick is None:
                continue
            held_files[name].write(pick[0] + US + pick[1] + RS)
            held_ids[name].write(str(row["identifier"]).replace("\n", " ") + "\n")
            want[name] -= 1
            kept[name] += 1
        held_read += 1
        manifest.write(f"held\t{path}\t{octets}\t{digest}\t{rows}\t" + "\t".join(f"{kept[n]}\t0" for n in NAMES) + "\n")
        manifest.flush()
        if remove:
            os.remove(local)
        log(f"CORPUS_SHARD role=held k={held_read} path={path} octets={octets} rows={rows} " + " ".join(f"{n}={held - want[n]}" for n in NAMES)
            + f" shard_ms={ms() - shard_start} ms={ms()}")
    for f in (*held_files.values(), *held_ids.values()):
        f.close()
    manifest.close()
    if any(want.values()):
        raise SystemExit("CORPUS_STOPPED the order ran out before the held windows")

    for n in NAMES:
        seen = windows[n] + drops[(n, "separator")] + drops[(n, "lines")]
        log(f"CORPUS_SLICE {n} quota={quota[n]} answer_bytes={taken[n]} documents={docs[n]} windows={windows[n]} "
            f"dropped_separator={drops[(n, 'separator')]} dropped_lines={drops[(n, 'lines')]} of={seen}")
    log(f"CORPUS_HELD windows={held} a slice; documents skipped as shared with training {shared}")
    for name in ("PASSAGE.txt", "TRAIN.txt", *(f"HELD_{n}.txt" for n in NAMES)):
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
    ap.add_argument("--answer-bytes", type=int, default=8_000_000_000)
    ap.add_argument("--prefix-bytes", type=int, default=1_000_000_000)
    ap.add_argument("--held", type=int, default=128)
    ap.add_argument("--cache", default=None, help="where a shard stands while it is read (default OUT/cache)")
    ap.add_argument("--max-shards", type=int, default=120)
    ap.add_argument("--max-held-shards", type=int, default=4)
    ap.add_argument("--early", type=int, default=8)
    ap.add_argument("--early-ms", type=int, default=40_000)
    args = ap.parse_args(argv)
    if os.path.exists(args.out):
        sys.exit(f"{args.out} stands; a passage is written under a new directory")
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

    build(order, fetch, args.out, args.answer_bytes, args.prefix_bytes, args.held, log=lambda s: print(s, flush=True),
          max_shards=args.max_shards, max_held=args.max_held_shards, early=args.early, early_ms=args.early_ms)


if __name__ == "__main__":
    main()
