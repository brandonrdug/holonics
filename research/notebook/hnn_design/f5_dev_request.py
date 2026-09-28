"""Pin one F5 development request for a native release probe.

The input is the owner-only F5 retrospective selection, which contains request text and an
earlier choosing retrieval control but no selected recorded reply. The first hash-ordered
request and its exact draw key are written owner-only; stdout is counts and hashes.

    HOLONICS_ROOT=<checkout with private cuts> python3 f5_dev_request.py
"""

import hashlib
import json
import os
import sys

from standing_cut import OUT_DIR, private_directory, private_write


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    with open(os.path.join(OUT_DIR, "f5-retrospective.json"), "rb") as handle:
        selection = json.load(handle)
    assert selection["schema"] == "holonics.f5-retrospective.v1"
    assert selection["items"] and selection["selected"] == len(selection["items"])
    item = selection["items"][0]
    request = item["request"].encode("utf-8")
    key = hashlib.sha256((selection["seed"] + "\0F5 native draw\0" + item["coordinate"]).encode()).digest()
    seed = int.from_bytes(key[:8], "little")
    family_key = hashlib.sha256((selection["seed"] + "\0F5 family draw\0" + item["coordinate"]).encode()).digest()
    family_seed = int.from_bytes(family_key[:8], "little")
    private_directory()
    private_write("f5-dev-request.bin", request)
    private_write("f5-dev-seed.bin", seed.to_bytes(8, "little"))
    private_write("f5-dev-family-seed.bin", family_seed.to_bytes(8, "little"))
    receipt = {
        "schema": "holonics.f5-dev-request.v1",
        "selection_sha256": selection["coordinates_sha256"],
        "request_bytes": len(request),
        "request_sha256": hashlib.sha256(request).hexdigest(),
        "draw_seed_u64": seed,
    }
    private_write("f5-dev-request.json", json.dumps(receipt, indent=2).encode())
    print(json.dumps({k: receipt[k] for k in (
        "schema", "selection_sha256", "request_bytes", "request_sha256"
    )}, indent=2))


if __name__ == "__main__":
    main()
