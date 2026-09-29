"""Encode F5's 32 pinned development requests for one native prospective pass.

The owner-only bundle contains requests and exact draw keys, never recorded validation replies.
Its order is the already pinned hash selection. Only counts and a hash are printed.

    HOLONICS_ROOT=<checkout with private cuts> python3 f5_request_bundle.py

The selection comes from F5's spent diagnostic split, which holds the development reserve, so it is
refused unless the logged flag `--read-reserve` is passed (`development_families.py`).
"""

import hashlib
import json
import os
import struct
import sys

from development_families import require_reserve_excluded, reserve_flag
from standing_cut import OUT_DIR, private_directory, private_write


def main():
    arguments, read_reserve = reserve_flag(sys.argv[1:], "f5_request_bundle.py")
    if arguments:
        sys.exit(__doc__)
    with open(os.path.join(OUT_DIR, "f5-retrospective.json"), "rb") as handle:
        selection = json.load(handle)
    require_reserve_excluded(selection, "the F5 retrospective selection", read_reserve)
    assert selection["schema"] == "holonics.f5-retrospective.v1"
    items = selection["items"]
    assert len(items) == selection["selected"] == 32
    bundle = bytearray(b"F5R1" + struct.pack("<I", len(items)))
    total_bytes = 0
    for item in items:
        request = item["request"].encode("utf-8")
        assert 0 < len(request) < 1 << 32
        key = hashlib.sha256((selection["seed"] + "\0F5 native draw\0" + item["coordinate"]).encode()).digest()
        seed = int.from_bytes(key[:8], "little")
        bundle.extend(struct.pack("<IQ", len(request), seed))
        bundle.extend(request)
        total_bytes += len(request)
    private_directory()
    private_write("f5-request-bundle.bin", bytes(bundle))
    receipt = {"schema": "holonics.f5-request-bundle.v1", "selected_coordinates_sha256": selection["coordinates_sha256"],
               "requests": len(items), "request_bytes": total_bytes,
               "bundle_sha256": hashlib.sha256(bundle).hexdigest()}
    private_write("f5-request-bundle.json", json.dumps(receipt, indent=2).encode())
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
