#!/usr/bin/env python3
"""The verbatim runs a text shares with the heard text, resolved to the heard documents.

    python3 -I tools/listener/heard_runs.py MANIFEST HEARD TEXT [TEXT ...]

An exterior census of recitation: how much of a release repeats the heard text verbatim. It was
first written for the binding bank's trace, retired on October 26 with the bank. Nothing here
enters the machine: it reads a release after it is made, beside it.

HEARD is the heard text, the concatenation MANIFEST names (medium, split, path, size, SHA-256 per
file, in order; each file's bytes are checked). For each TEXT it reads, at every byte, the longest
span starting there that occurs somewhere in HEARD, and keeps the maximal runs (those no run
starting one byte earlier contains). For each maximal run it prints its place, its length, the whole
words it holds (a word cut by the run's edge is not counted), the heard documents it occurs in, and
the run itself. Between consecutive maximal runs it prints the seam: the shortest window crossing
the junction, the byte before the later run through the byte after the earlier one, and whether it
occurs in HEARD.

Summary per TEXT (`HEARD_RUNS`): the longest run, the runs of at least two whole words, the distinct
documents those runs can name, and the seams found nowhere in HEARD. With `--continuations`, the
TEXT arguments are the held-out paragraphs' own continuations, and the line `RECITATION_BAR` gives
`l_rec`, the longest run any of them shares with HEARD: what the authors themselves reuse.
"""
import hashlib
import re
import sys

WORD = re.compile(rb"[A-Za-z0-9']+")


def documents(manifest, heard):
    spans = []
    at = 0
    for line in open(manifest):
        _medium, split, path, size, sha = line.rstrip("\n").split("\t")
        if split != "train":
            continue
        size = int(size)
        if hashlib.sha256(heard[at:at + size]).hexdigest() != sha:
            raise SystemExit("the heard text is not the manifest's")
        spans.append((at, at + size, path))
        at += size
    if at != len(heard):
        raise SystemExit("the manifest does not cover the heard text")
    return spans


def document_of(spans, place):
    lo, hi = 0, len(spans)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if spans[mid][0] <= place:
            lo = mid
        else:
            hi = mid
    return spans[lo][2]


def occurrences(heard, piece, cap=4096):
    out = []
    at = heard.find(piece)
    while at >= 0 and len(out) < cap:
        out.append(at)
        at = heard.find(piece, at + 1)
    return out


def longest_from_each(heard, text):
    """`match[i]`: the longest `L` with `text[i:i+L]` in `heard`; `match[i+1] >= match[i] - 1`."""
    match = []
    length = 0
    for i in range(len(text)):
        length = max(length - 1, 0)
        while i + length < len(text) and heard.find(text[i:i + length + 1]) >= 0:
            length += 1
        match.append(length)
    return match


def maximal_runs(match):
    runs = []
    for i, length in enumerate(match):
        if length and (i == 0 or i + length > i - 1 + match[i - 1]):
            runs.append((i, i + length))
    return runs


def whole_words(text, start, end):
    return [m.group() for m in WORD.finditer(text, start, end) if m.start() >= start and m.end() <= end
            and (m.start() > start or start == 0 or not WORD.match(text, start - 1))
            and (m.end() < end or end == len(text) or not WORD.match(text, end))]


def census(spans, heard, name, text, show=True):
    match = longest_from_each(heard, text)
    runs = maximal_runs(match)
    named = []
    for start, end in runs:
        words = whole_words(text, start, end)
        docs = sorted({document_of(spans, p) for p in occurrences(heard, text[start:end])})
        if show:
            print(f"RUN text={name} at={start} length={end - start} whole_words={len(words)} documents={len(docs)} "
                  f"first={docs[0] if docs else '-'} run={text[start:end]!r}")
        if len(words) >= 2:
            named.append(set(docs))
    seams_absent = 0
    for (s1, e1), (s2, e2) in zip(runs, runs[1:]):
        lo, hi = max(s2 - 1, 0), min(e1 + 1, len(text))
        window = text[lo:hi] if lo < hi else text[e1 - 1:s2 + 1]
        found = heard.find(window) >= 0
        seams_absent += not found
        if show:
            print(f"SEAM text={name} at={lo} window={window!r} in_heard={found}")
    distinct = set().union(*named) if named else set()
    # Two runs can name two different documents exactly when there are two runs and their
    # documents are not all one.
    two = len(named) >= 2 and len(distinct) >= 2
    longest = max(match) if match else 0
    print(f"HEARD_RUNS text={name} bytes={len(text)} longest={longest} runs={len(runs)} two_word_runs={len(named)} "
          f"documents_named={len(distinct)} two_documents={two} seams={max(len(runs) - 1, 0)} seams_absent={seams_absent}",
          flush=True)
    return longest


def main():
    args = sys.argv[1:]
    continuations = "--continuations" in args
    args = [a for a in args if a != "--continuations"]
    if len(args) < 3:
        raise SystemExit(__doc__)
    manifest, heard_path, texts = args[0], args[1], args[2:]
    heard = open(heard_path, "rb").read()
    spans = documents(manifest, heard)
    longest = [census(spans, heard, t, open(t, "rb").read(), show=not continuations) for t in texts]
    if continuations:
        print(f"RECITATION_BAR l_rec={max(longest)} continuations={len(texts)}")


if __name__ == "__main__":
    main()
