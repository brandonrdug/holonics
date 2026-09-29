"""Select the pinned F1 bounded held-out part by sections and length only.

The rule is fixed in the F1 gate record: first complete nonempty validation part of at most
128 byte cells, ending at its actual next section. The emitted part stays owner-only; stdout is
counts and hashes. No evaluation partition is opened.

    HOLONICS_ROOT=<checkout with private cuts> python3 f1_validation_part.py

F1's split is a spent family-unit split that holds the development reserve, so its cut is refused
unless the logged flag `--read-reserve` is passed (`development_families.py`).
"""

import hashlib
import json
import os
import sys
from array import array

from development_families import require_reserve_excluded, reserve_flag
from standing_cut import OUT_DIR, private_directory, private_write

CEILING = 128


def main():
    arguments, read_reserve = reserve_flag(sys.argv[1:], "f1_validation_part.py")
    if arguments:
        sys.exit(__doc__)
    prefix = os.path.join(OUT_DIR, "curated-f1-validation-cut")
    with open(prefix + ".json", "rb") as handle:
        manifest = json.load(handle)
    require_reserve_excluded(manifest, "curated-f1-validation-cut", read_reserve)
    with open(prefix + ".bin", "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == manifest["cut_sha256"]
    codes = array("H")
    codes.frombytes(raw)
    if sys.byteorder != "little":
        codes.byteswap()
    sections = [at for at, code in enumerate(codes) if code >= 256]
    assert sections and sections[0] == 0, "the cut opens at a section"
    chosen = None
    for opening, closing in zip(sections, sections[1:]):
        length = closing - opening - 1
        if 0 < length <= CEILING:
            chosen = (opening, closing)
            break
    assert chosen is not None, "a bounded complete part exists"
    opening, closing = chosen
    part = codes[opening + 1:closing]
    assert all(code < 256 for code in part)
    packed = array("H", part)
    if sys.byteorder != "little":
        packed.byteswap()
    data = packed.tobytes()
    receipt = {
        "schema": "holonics.f1-validation-part.v1",
        "validation_cut_sha256": manifest["cut_sha256"],
        "opening_tick": opening,
        "closing_tick": closing,
        "closing_section": int(codes[closing]),
        "bytes": len(part),
        "part_sha256": hashlib.sha256(data).hexdigest(),
    }
    private_directory()
    private_write("f1-validation-part.bin", data)
    private_write("f1-validation-part.json", json.dumps(receipt, indent=2).encode())
    print(json.dumps({key: receipt[key] for key in (
        "schema", "validation_cut_sha256", "bytes", "part_sha256"
    )}, indent=2))


if __name__ == "__main__":
    main()
