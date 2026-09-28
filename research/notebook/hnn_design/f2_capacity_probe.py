"""Pin the least capacity-admissible F2 byte-chart exposure across its split roles.

Only development-role curated sources are read. Their last 4,096 and 2,052 byte cells form the
existing field's `n* = 6,148` cut; section letters do not enter this byte-chart probe. Private
files are owner-only; stdout contains counts and hashes, never source text.

    HOLONICS_ROOT=<checkout with private cuts> python3 f2_capacity_probe.py
"""

import hashlib
import json
import os
import sys
from array import array

from standing_cut import OUT_DIR, private_directory, private_write

ROLES = (("choosing", 4096), ("validation", 2052))
NAME = "f2-capacity-probe"


def tail(role, count):
    prefix = os.path.join(OUT_DIR, f"curated-f2-{role}-source")
    with open(prefix + ".json", "rb") as handle:
        manifest = json.load(handle)
    with open(prefix + ".bin", "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == manifest["development_stream_sha256"]
    codes = array("H")
    codes.frombytes(raw)
    if sys.byteorder != "little":
        codes.byteswap()
    bytes_only = bytes(int(code) for code in codes if code < 256)
    assert len(bytes_only) >= count
    return bytes_only[-count:]


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    pieces = [tail(role, count) for role, count in ROLES]
    cut = b"".join(pieces)
    assert len(cut) == 6148
    private_directory()
    private_write(NAME + ".bin", cut)
    receipt = {
        "schema": "holonics.standing-cut.v2",
        "population": len(cut),
        "held_out_range": [len(pieces[0]), len(cut)],
        "source": "F2 choosing and validation role streams, final byte cells; section letters removed",
        "cut_sha256": hashlib.sha256(cut).hexdigest(),
        "choosing_sha256": hashlib.sha256(pieces[0]).hexdigest(),
        "validation_sha256": hashlib.sha256(pieces[1]).hexdigest(),
    }
    private_write(NAME + ".json", json.dumps(receipt, indent=2).encode())
    print(json.dumps({key: receipt[key] for key in (
        "population", "held_out_range", "cut_sha256", "choosing_sha256", "validation_sha256"
    )}, indent=2))


if __name__ == "__main__":
    main()
