#!/usr/bin/env python3
"""Show what the tower released through a composed passage's charts (`compose.py`).

Usage:
  python3 -I tools/listener/render.py strokes RELEASES.tsv OUT_DIR   # one PNG a release
  python3 -I tools/listener/render.py cycles RELEASES.tsv OUT_DIR    # one WAV a release

An exterior reading, never learner material. A release carries only the chart's octets; the exact
fibre (an intensity's remainder in its octave, a sample's residual from its half-cycle's peak) was
never released, so a pixel is drawn at the top of its octave, `2^(o+1) − 1`, and a half-cycle as a
half-sine of its length whose peak is the middle of its octave, `3·2^(o−1)`. Octets the chart cannot
read (a revisited or out-of-frame pixel, an octave past the chart's, a truncated jump) are skipped and
counted as slips, never dropped silently.
"""

import math
from pathlib import Path
import struct
import sys
import wave
import zlib

DIRECTIONS = ((0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1))


def octets_of(field):
    return field.encode("latin-1").decode("unicode_escape").encode("latin-1")


def releases(tsv):
    lines = Path(tsv).read_text().splitlines()[1:]
    for line in lines:
        parts = line.split("\t")
        yield int(parts[0]), octets_of(parts[5] if len(parts) > 5 else "")


def strokes(octets, width=28, height=28):
    image, slips = [0] * (width * height), 0
    row = col = heading = 0
    at = 0
    started = False
    while at < len(octets):
        turn, octave = octets[at] >> 4, octets[at] & 15
        at += 1
        if turn > 8 or octave > 7 or (not started and turn != 8):
            slips += 1
            continue
        if turn == 8:
            if at + 2 > len(octets):
                slips += 1
                break
            dr, dc = struct.unpack("bb", octets[at:at + 2])
            at += 2
            r, c, heading = row + dr, col + dc, 0
        else:
            heading = (heading + turn) % 8
            r, c = row + DIRECTIONS[heading][0], col + DIRECTIONS[heading][1]
        if not (0 <= r < height and 0 <= c < width) or image[r * width + c]:
            slips += 1
            continue
        image[r * width + c] = (1 << (octave + 1)) - 1
        row, col, started = r, c, True
    return image, slips


def png(path, image, width, height, scale=4):
    rows = b"".join(b"\0" + bytes(image[(y // scale) * width + x // scale] for x in range(width * scale)) for y in range(height * scale))
    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)
    Path(path).write_bytes(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", width * scale, height * scale, 8, 0, 0, 0, 0)) + chunk(b"IDAT", zlib.compress(rows, 9)) + chunk(b"IEND", b""))


def cycles(octets):
    samples, slips, at, length = [], 0, 0, 0
    while at < len(octets):
        b = octets[at]
        at += 1
        if b == 255:
            length += 255
            continue
        length += b
        if at >= len(octets):
            slips += 1
            break
        sign, octave = octets[at] >> 4, octets[at] & 15
        at += 1
        if sign > 2 or octave > 14 or length == 0:
            slips += 1
            length = 0
            continue
        peak = 0 if sign == 2 else (3 << octave) // 2 if octave else 1
        s = -1 if sign == 1 else 1
        samples.extend(int(s * peak * math.sin(math.pi * (k + 0.5) / length)) for k in range(length))
        length = 0
    return samples, slips


def main(argv):
    kind, tsv, out = argv[1], argv[2], Path(argv[3])
    out.mkdir()
    for p, octets in releases(tsv):
        if kind == "strokes":
            image, slips = strokes(octets)
            png(out / f"release{p}.png", image, 28, 28)
            print(f"release {p}: {sum(1 for v in image if v)} pixels, {slips} slips")
        else:
            samples, slips = cycles(octets)
            with wave.open(str(out / f"release{p}.wav"), "wb") as w:
                w.setnchannels(1)
                w.setsampwidth(2)
                w.setframerate(16000)
                w.writeframes(struct.pack("<%dh" % len(samples), *samples))
            print(f"release {p}: {len(samples)} samples ({len(samples) / 16000:.2f} s), {slips} slips")


if __name__ == "__main__":
    main(sys.argv)
