"""Join a pinned item's choosing cut and one disjoint validation cut for one passage.

The join is an exterior chart of two disjoint populations: choosing deposits first, validation is read
once afterward. Under the conversation split (`U6`, the default item) the two roles share no
conversation, so their aeons are disjoint: validation's conversation ordinals are shifted past
choosing's, and each letter's aeon is written beside the joint cut (`-cut.aeons.bin`, one
little-endian u32 a section letter). Relations retain their role-local target and are shifted into
the joint tick chart. The boundary between the cuts is a declared section, not an invented causal
edge. Only counts and hashes leave the owner-only cut directory.

    HOLONICS_ROOT=<checkout with private cuts> python3 family_passage.py [U6 | <spent item> --read-reserve]

A role cut whose manifest does not name the development reserve as excluded (every spent family-unit
item's, `F1`, `F2`, `F5`, `U2`, `F0`) is refused unless the logged flag `--read-reserve` is passed
(`development_families.py`); a spent item's join carries no aeons.
"""

import hashlib
import json
import os
import sys
from array import array

from development_families import SEEDS, SPENT, reserve_flag, require_reserve_excluded
from standing_cut import OUT_DIR, private_directory, private_write

POPULATION = 1 << 20


def read(item, role, read_reserve):
    prefix = os.path.join(OUT_DIR, f"curated-{item}-{role}")
    with open(prefix + "-cut.json", "rb") as handle:
        cut = json.load(handle)
    require_reserve_excluded(cut, f"curated-{item}-{role}-cut", read_reserve)
    with open(prefix + "-cut.bin", "rb") as handle:
        codes = handle.read()
    assert hashlib.sha256(codes).hexdigest() == cut["cut_sha256"]
    assert len(codes) == 2 * cut["cells"]
    with open(prefix + "-flat-cut.json", "rb") as handle:
        flat_manifest = json.load(handle)
    with open(prefix + "-flat-cut.bin", "rb") as handle:
        flat = handle.read()
    assert hashlib.sha256(flat).hexdigest() == flat_manifest["cut_sha256"]
    with open(prefix + "-cut.incidence.json", "rb") as handle:
        incidence_manifest = json.load(handle)
    with open(prefix + "-cut.incidence.bin", "rb") as handle:
        incidence = handle.read()
    assert hashlib.sha256(incidence).hexdigest() == incidence_manifest["sha256"]
    assert len(incidence) == 12 * incidence_manifest["relations"]
    aeons = None
    if "aeons" in cut:
        with open(prefix + "-cut.aeons.bin", "rb") as handle:
            raw = handle.read()
        assert hashlib.sha256(raw).hexdigest() == cut["aeons"]["aeons_sha256"]
        aeons = array("I")
        aeons.frombytes(raw)
        if sys.byteorder != "little":
            aeons.byteswap()
        assert len(aeons) == cut["aeons"]["section_letters"]
    return cut, codes, flat, incidence_manifest, incidence, aeons


def main():
    arguments, read_reserve = reserve_flag(sys.argv[1:], "family_passage.py")
    if len(arguments) > 1 or (arguments and arguments[0] not in tuple(SEEDS) + tuple(SPENT)):
        sys.exit(__doc__)
    item = arguments[0].lower() if arguments else "u6"
    name = f"curated-{item}-passage"
    c_cut, c_codes, c_flat, c_inc, c_relations, c_aeons = read(item, "choosing", read_reserve)
    v_cut, v_codes, v_flat, v_inc, v_relations, v_aeons = read(item, "validation", read_reserve)
    assert c_cut["alphabet"] == v_cut["alphabet"] == 268
    offset = c_cut["cells"]
    assert offset + v_cut["cells"] <= POPULATION
    assert c_cut["cells"] > 0 and v_cut["cells"] > 0
    joined = c_codes + v_codes
    flat = c_flat + v_flat
    relation_words = array("I")
    relation_words.frombytes(c_relations)
    if sys.byteorder != "little":
        relation_words.byteswap()
    for at in range(0, len(v_relations), 12):
        tick = int.from_bytes(v_relations[at:at + 4], "little") + offset
        kind = int.from_bytes(v_relations[at + 4:at + 8], "little")
        target = int.from_bytes(v_relations[at + 8:at + 12], "little") + offset
        assert target < tick and kind in (0, 1)
        relation_words.extend((tick, kind, target))
    # The machine is little-endian on this host; byteswap keeps the codec portable.
    if sys.byteorder != "little":
        relation_words.byteswap()
    relations = relation_words.tobytes()
    aeons = None
    if c_aeons is not None and v_aeons is not None:
        # Disjoint conversations: validation's ordinals follow choosing's.
        shift = c_cut["aeons"]["conversations"]
        joint = array("I", list(c_aeons) + [aeon + shift for aeon in v_aeons])
        if sys.byteorder != "little":
            joint.byteswap()
        aeons = joint.tobytes()
    private_directory()
    private_write(name + "-cut.bin", joined)
    private_write(name + "-flat-cut.bin", flat)
    private_write(name + "-cut.incidence.bin", relations)
    excluded = c_cut.get("reserve_excluded") if c_cut.get("reserve_excluded") == v_cut.get("reserve_excluded") else None
    cut_manifest = {
        "schema": "holonics.curated-cut.v1",
        "encoding": "u16 little-endian, one code a cell",
        "alphabet": c_cut["alphabet"],
        "population": POPULATION,
        "cells": offset + v_cut["cells"],
        "held_out_start": offset,
        "cut_sha256": hashlib.sha256(joined).hexdigest(),
        "choosing_sha256": c_cut["cut_sha256"],
        "validation_sha256": v_cut["cut_sha256"],
        "reserve_excluded": excluded,
    }
    if aeons is not None:
        private_write(name + "-cut.aeons.bin", aeons)
        cut_manifest["aeons"] = {
            "encoding": "u32 little-endian, one conversation ordinal a section letter",
            "section_letters": len(aeons) // 4,
            "conversations": c_cut["aeons"]["conversations"] + v_cut["aeons"]["conversations"],
            "aeons_sha256": hashlib.sha256(aeons).hexdigest(),
        }
    private_write(name + "-cut.json", json.dumps(cut_manifest, indent=2).encode())
    flat_manifest = {
        "schema": "holonics.standing-cut.v2",
        "population": len(flat),
        "held_out_range": [len(c_flat), len(flat)],
        "cut_sha256": hashlib.sha256(flat).hexdigest(),
        "reserve_excluded": excluded,
    }
    private_write(name + "-flat-cut.json", json.dumps(flat_manifest, indent=2).encode())
    relation_manifest = {
        "schema": "holonics.curated-cut-incidence.v1",
        "relations": c_inc["relations"] + v_inc["relations"],
        "sha256": hashlib.sha256(relations).hexdigest(),
        "reserve_excluded": excluded,
    }
    private_write(name + "-cut.incidence.json", json.dumps(relation_manifest, indent=2).encode())
    print(json.dumps({"cells": cut_manifest["cells"], "choosing_cells": offset,
                      "validation_cells": v_cut["cells"], "cut_sha256": cut_manifest["cut_sha256"],
                      "relations": relation_manifest["relations"],
                      "incidence_sha256": relation_manifest["sha256"],
                      "aeons_sha256": cut_manifest.get("aeons", {}).get("aeons_sha256"),
                      "reserve_excluded": excluded}, indent=2))


if __name__ == "__main__":
    main()
