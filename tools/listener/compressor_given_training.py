#!/usr/bin/env python3
"""A classical compressor's code of a held-out text given the training text, read three ways.

    python3 tools/listener/compressor_given_training.py MANIFEST TRAIN DEV DEV_ROLES STREAMS

The tower's held-out read cuts DEV into STREAMS chunks of ceil(len/STREAMS) bytes, reads each from
rest on the constitution the whole training text deposited, and counts each byte's code under its
role (its medium). A compressor is read here on the same information in three ways, each medium
separately, for bz2 at its largest block and xz at its strongest preset:

- `chunks|all`: the context is the whole training text in its order, and the pieces are the
  medium's bytes inside each of the tower's chunks. This is the tower's own partition and the
  tower's own training text: the declared comparison.
- `chunks|own`: the context is the medium's own part of the training text, the same pieces.
- `whole|own`: the context is the medium's own part, and the piece is the medium's whole held-out
  text, so the compressor also reads across the tower's chunk boundaries.
- `n16|own` and `n64|own`: the context is the medium's own part, and the medium's held-out text is
  cut into 16 or 64 equal pieces. These are not comparisons with the tower's read: they show how a
  compressor's conditional code moves with the piece count alone, so a reading that does not state
  its pieces cannot be repeated.

A piece's code is `len(C(context + piece)) - len(C(context))` bytes. bz2 sorts blocks of 900 kB,
so a context longer than one block reaches a piece only through the block the piece lands in;
xz's window holds the whole training text. The medium regions of TRAIN are read from MANIFEST
(medium, split, path, size, SHA-256 per file, in the order the files were concatenated), each
file's bytes checked against its SHA-256. Each line prints the code as an exact ratio of bits to
bytes and its decimal reading.
"""
import bz2
import hashlib
import lzma
import sys
from fractions import Fraction

MEDIA = ["prose", "lean", "rust", "arithmetic"]

manifest, train_path, dev_path, roles_path, streams = sys.argv[1:6]
train = open(train_path, "rb").read()
dev = open(dev_path, "rb").read()
roles = open(roles_path, "rb").read()
streams = int(streams)
assert len(dev) == len(roles)

own = {}
at = 0
for line in open(manifest):
    medium, split, _path, size, sha = line.rstrip("\n").split("\t")
    if split != "train":
        continue
    size = int(size)
    assert hashlib.sha256(train[at:at + size]).hexdigest() == sha, "the training text is not the manifest's"
    lo, _ = own.get(medium, (at, at))
    own[medium] = (lo, at + size)
    at += size
assert at == len(train)

chunk = -(-len(dev) // streams)
compressors = {
    "bz2": lambda b: bz2.compress(b, 9),
    "xz": lambda b: lzma.compress(b, preset=9 | lzma.PRESET_EXTREME),
}


def pieces_in_chunks(role):
    out = []
    for start in range(0, len(dev), chunk):
        piece = bytes(b for b, r in zip(dev[start:start + chunk], roles[start:start + chunk]) if r == role)
        if piece:
            out.append(piece)
    return out


for name, c in compressors.items():
    base_all = len(c(train))
    for role, medium in enumerate(MEDIA):
        lo, hi = own[medium]
        context_own = train[lo:hi]
        base_own = len(c(context_own))
        chunked = pieces_in_chunks(role)
        whole = bytes(b for b, r in zip(dev, roles) if r == role)
        size = len(whole)
        def equal(n):
            step = -(-size // n)
            return [whole[i:i + step] for i in range(0, size, step)]

        readings = [
            ("chunks|all", chunked, train, base_all),
            ("chunks|own", chunked, context_own, base_own),
            ("whole|own", [whole], context_own, base_own),
            ("n16|own", equal(16), context_own, base_own),
            ("n64|own", equal(64), context_own, base_own),
        ]
        for how, pieces, context, base in readings:
            code = sum(len(c(context + p)) - base for p in pieces)
            bits = Fraction(8 * code, size)
            print(f"COMPRESSOR_GIVEN_TRAINING compressor={name} medium={medium} read={how} "
                  f"pieces={len(pieces)} bytes={size} code_bytes={code} "
                  f"bits_a_byte={bits.numerator}/{bits.denominator} ~{float(bits):.3f}", flush=True)
