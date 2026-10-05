#!/usr/bin/env python3
"""Copy length: the longest verbatim run of a release inside the admitted passage.

An exterior receipt, a contamination detector. It makes recitation of seen text visible at once:
a release whose copy length is a large part of its length was copied from the admitted passage.
It is never a control, a grade, a reward or a loss, and nothing in the machine consumes it. It
reads no HNN state: its inputs are two kinds of plain file (the release text and the passage text
the machine was exposed to), and its output is integers.

    python3 tools/copy_length.py --release R.txt --passage P1 [P2 ...] [--min-run 8] [--json]

The law (exact). Treat the release R and each passage file P_f as byte strings. The copy length is

    L = max_f max { |w| : w is a substring of R and a substring of P_f },

the longest common substring of the release and the passage, taken over bytes, never characters
(a run may start or end inside a UTF-8 sequence). A run lies within one passage file: the end of
one file and the start of the next are not adjacent, so a run never spans two files. The release
start is the offset in R of the first (earliest) run of length L, the passage file is the index
(in the order given, from 0) of the first file in which that run occurs, and the passage offset
is its first offset in that file. The covered count is the number of release bytes i for which
some run R[a:b] with a <= i < b and b - a >= K (K = --min-run) occurs verbatim in a single
passage file. Equivalently, byte i is covered iff some K-byte window of R containing i occurs in
one passage file.

Output is plain integers. When L = 0 the three locations are -1 (there is no run). A passage
path is never printed, and passage text is never printed unless `--show` is given: passages may
be private, so `--show` is off by default and prints only the longest run (as JSON-escaped text).

Method (linear time). Build the suffix automaton of the release once, O(|R|) states. Each
passage file streams through it in chunks, byte by byte, tracking the longest suffix of the
passage read so far that is a substring of R, and marking the automaton state that holds it. A
sweep over the suffix links then lifts the marks to the matching statistics of the release,
ms[i] = the longest suffix of R[:i+1] that occurs in the passage file, from which L, the release
start and the covered count follow (ms is non-decreasing in start, so the cover is one sweep).
Time is O(|R| + |P|) per file and memory is O(|R|) plus one chunk, so a passage of tens of MB
streams without being held. The automaton is built over the release rather than over the
passage (the equivalent dual: the longest common substring is symmetric): a suffix automaton over
a 16 MiB passage has up to 32 Mi states, far beyond what Python holds, while the release (a
generation) is small. `agent-inferred`. Measured: a 256 KiB release against a 16 MiB passage
held 148,088 KiB resident (several hundred bytes per release byte); a 4 KiB release held 22,256 KiB.
"""

import argparse
import json
import mmap
import os
import sys

# The read size of the passage stream: a buffer, not a law. The result is independent of it.
CHUNK = 1 << 20


class ReleaseAutomaton:
    """The suffix automaton of one byte string, with the matching-statistics sweep."""

    def __init__(self, data):
        trans = [{}]
        link = [-1]
        length = [0]
        prefix_state = []
        last = 0
        for c in data:
            cur = len(trans)
            trans.append({})
            length.append(length[last] + 1)
            link.append(0)
            p = last
            while p != -1 and c not in trans[p]:
                trans[p][c] = cur
                p = link[p]
            if p != -1:
                q = trans[p][c]
                if length[p] + 1 == length[q]:
                    link[cur] = q
                else:
                    clone = len(trans)
                    trans.append(dict(trans[q]))
                    length.append(length[p] + 1)
                    link.append(link[q])
                    while p != -1 and trans[p].get(c) == q:
                        trans[p][c] = clone
                        p = link[p]
                    link[q] = clone
                    link[cur] = clone
            last = cur
            prefix_state.append(cur)
        self.data = data
        self.trans = trans
        self.link = link
        self.length = length
        self.prefix_state = prefix_state
        # States by increasing length: a topological order of the suffix-link tree.
        self.order = sorted(range(len(trans)), key=length.__getitem__)

    def mark(self, chunks):
        """Stream chunks through the automaton: best[v] = the longest suffix of the stream
        read so far that was held by state v at some step (0 when none)."""
        trans = self.trans
        link = self.link
        length = self.length
        best = [0] * len(trans)
        v = 0
        n = 0
        for chunk in chunks:
            for c in chunk:
                t = trans[v]
                while c not in t:
                    if v == 0:
                        break
                    v = link[v]
                    n = length[v]
                    t = trans[v]
                else:
                    v = t[c]
                    n += 1
                    if n > best[v]:
                        best[v] = n
                    continue
                n = 0
        return best

    def matching_statistics(self, best):
        """ms[i] = the longest suffix of data[:i+1] that occurs in the streamed passage."""
        link = self.link
        length = self.length
        order = self.order
        # A state with an occurring string has its whole suffix-link parent occurring.
        for v in reversed(order):
            if v and best[v]:
                p = link[v]
                if p > 0:
                    best[p] = length[p]
        top = [0] * len(best)
        for v in order:
            if v:
                top[v] = best[v] or top[link[v]]
        return [top[v] for v in self.prefix_state]


def _chunks_of(path, chunk_size):
    with open(path, "rb") as handle:
        while True:
            chunk = handle.read(chunk_size)
            if not chunk:
                return
            yield chunk


def _first_offset(path, needle):
    """The first offset of `needle` in the file at `path`, or -1."""
    if not needle or os.path.getsize(path) == 0:
        return -1
    with open(path, "rb") as handle:
        with mmap.mmap(handle.fileno(), 0, access=mmap.ACCESS_READ) as view:
            return view.find(needle)


def copy_length(release, passages, min_run=8, chunk_size=CHUNK):
    """The copy-length receipt of `release` (bytes) against `passages`, a list of file paths
    (each one a separate admitted passage; a run never spans two). Returns a dict of integers:

    copy_length    the longest run of release bytes occurring verbatim in one passage file
    release_start  its first start in the release, or -1
    passage_file   the index of the first passage file holding it, or -1
    passage_offset its first offset in that file, or -1
    covered_bytes  release bytes covered by runs of length >= min_run
    min_run, release_bytes, passage_bytes
    """
    if min_run < 1:
        raise ValueError("min_run must be at least 1")
    n = len(release)
    covered = bytearray(n)
    best_key = None  # (-length, release_start, file index): the least is reported
    passage_bytes = 0
    automaton = ReleaseAutomaton(release) if n else None
    for index, path in enumerate(passages):
        passage_bytes += os.path.getsize(path)
        if automaton is None:
            continue
        ms = automaton.matching_statistics(
            automaton.mark(_chunks_of(path, chunk_size)))
        longest = 0
        end = -1
        hi = -1  # the last release index covered by this file's runs
        for i, m in enumerate(ms):
            if m > longest:
                longest = m
                end = i
            if m >= min_run:
                s = i - m + 1
                if s <= hi:
                    s = hi + 1
                if s <= i:
                    covered[s:i + 1] = b"\x01" * (i - s + 1)
                hi = i
        if longest:
            key = (-longest, end - longest + 1, index)
            if best_key is None or key < best_key:
                best_key = key
    if best_key is None:
        return {
            "copy_length": 0, "release_start": -1, "passage_file": -1,
            "passage_offset": -1, "covered_bytes": 0, "min_run": min_run,
            "release_bytes": n, "passage_bytes": passage_bytes,
        }
    longest, start, index = -best_key[0], best_key[1], best_key[2]
    return {
        "copy_length": longest,
        "release_start": start,
        "passage_file": index,
        "passage_offset": _first_offset(passages[index], release[start:start + longest]),
        "covered_bytes": covered.count(1),
        "min_run": min_run,
        "release_bytes": n,
        "passage_bytes": passage_bytes,
    }


def _positive(text):
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return value


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Copy length: the longest verbatim run of the release in the admitted "
                    "passage (an exterior receipt; integers only).")
    parser.add_argument("--release", required=True, help="the release text file")
    parser.add_argument("--passage", required=True, nargs="+",
                        help="admitted-passage files; a run never spans two files")
    parser.add_argument("--min-run", type=_positive, default=8,
                        help="threshold K for the covered-bytes count (default 8)")
    parser.add_argument("--json", action="store_true", help="print one JSON object")
    parser.add_argument("--show", action="store_true",
                        help="also print the longest run (passages may be private; off by default)")
    args = parser.parse_args(argv)

    with open(args.release, "rb") as handle:
        release = handle.read()
    result = copy_length(release, args.passage, args.min_run)
    if args.show:
        start, longest = result["release_start"], result["copy_length"]
        run = release[start:start + longest] if longest else b""
        text = run.decode("utf-8", "backslashreplace")
    if args.json:
        if args.show:
            result = dict(result, run=text)
        print(json.dumps(result))
    else:
        for key, value in result.items():
            print(f"{key} {value}")
        if args.show:
            print(f"run {json.dumps(text, ensure_ascii=False)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
