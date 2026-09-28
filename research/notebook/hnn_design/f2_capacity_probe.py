"""Pin the least capacity-admissible F2 byte-chart exposure across its split roles.

Only development-role curated sources are read. Their last 4,096 and 2,052 byte cells form the
existing field's `n* = 6,148` cut; section letters do not enter this byte-chart probe. Private
files are owner-only; stdout contains counts and hashes, never source text.

    HOLONICS_ROOT=<checkout with private cuts> python3 f2_capacity_probe.py [F2 | F2V2]

`F2` (the default) is the capacity probe of September 27 (`f2-capacity-probe`). `F2V2` is F2's
adoption gate on the receiving population (THE_REBUILD F2, the pins of September 28): the same
shape over the fresh split (`f2v2-gate-probe`), whose manifest also carries the counts the gate's
budgets read from the declared validation passage, the validation role's cut at F4's aperture
(`curated_source.py 524288 validation F2V2`): its byte cells (`declared_validation_cells`), its
agent responses (`agent_responses`, each an agent-channel part, the cells after an agent letter up
to the next letter, as F0's response stops count them) and the longest of them
(`longest_agent_response`). Only counts are read from it.
"""

import hashlib
import json
import os
import sys
from array import array

from standing_cut import OUT_DIR, private_directory, private_write

ROLES = (("choosing", 4096), ("validation", 2052))
ITEMS = {"F2": ("f2", "f2-capacity-probe"), "F2V2": ("f2v2", "f2v2-gate-probe")}
BYTES = 256
CHANNELS = 3
AGENT = 1


def codes_of(raw):
    codes = array("H")
    codes.frombytes(raw)
    if sys.byteorder != "little":
        codes.byteswap()
    return codes


def tail(item, role, count):
    prefix = os.path.join(OUT_DIR, f"curated-{item}-{role}-source")
    with open(prefix + ".json", "rb") as handle:
        manifest = json.load(handle)
    with open(prefix + ".bin", "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == manifest["development_stream_sha256"]
    bytes_only = bytes(int(code) for code in codes_of(raw) if code < BYTES)
    assert len(bytes_only) >= count
    return bytes_only[-count:]


def declared_passage(item):
    """The declared validation passage's counts: its byte cells and its agent responses' lengths."""
    prefix = os.path.join(OUT_DIR, f"curated-{item}-validation-cut")
    with open(prefix + ".json", "rb") as handle:
        manifest = json.load(handle)
    with open(prefix + ".bin", "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == manifest["cut_sha256"]
    cells, responses, current = 0, [], None
    for code in codes_of(raw):
        if code < BYTES:
            cells += 1
            if current is not None:
                current += 1
            continue
        if current is not None:
            responses.append(current)
        current = 0 if (code - BYTES) % CHANNELS == AGENT else None
    if current is not None:
        responses.append(current)
    return {
        "declared_validation_sha256": manifest["cut_sha256"],
        "declared_validation_cells": cells,
        "agent_responses": len(responses),
        "longest_agent_response": max(responses),
    }


def main():
    arguments = sys.argv[1:]
    if len(arguments) > 1 or (arguments and arguments[0] not in ITEMS):
        sys.exit(__doc__)
    key = arguments[0] if arguments else "F2"
    item, name = ITEMS[key]
    pieces = [tail(item, role, count) for role, count in ROLES]
    cut = b"".join(pieces)
    assert len(cut) == 6148
    private_directory()
    private_write(name + ".bin", cut)
    receipt = {
        "schema": "holonics.standing-cut.v2",
        "population": len(cut),
        "held_out_range": [len(pieces[0]), len(cut)],
        "source": f"{key} choosing and validation role streams, final byte cells; section letters removed",
        "cut_sha256": hashlib.sha256(cut).hexdigest(),
        "choosing_sha256": hashlib.sha256(pieces[0]).hexdigest(),
        "validation_sha256": hashlib.sha256(pieces[1]).hexdigest(),
    }
    if key == "F2V2":
        receipt.update(declared_passage(item))
    private_write(name + ".json", json.dumps(receipt, indent=2).encode())
    print(json.dumps({field: value for field, value in receipt.items() if field not in ("schema", "source")},
                     indent=2))


if __name__ == "__main__":
    main()
