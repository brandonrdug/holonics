"""The curated cut's admitted relations (HNN_FORMULA, "The source and release contract", item 7;
`holonics::receiver::population::admitted`; #73, #148).

An exterior codec step, stdlib only, run once after `curated_source.py`. It reads the curated
source's manifest and incidence file (`.local/cuts/curated-source.json`,
`curated-source.incidence.jsonl`) and the pinned cut (`curated-cut.bin`), and writes the relations
the admitted receivers read, placed on the cut's ticks, into `.local/cuts/` (each file created mode
0600, `standing_cut.private_write`). Nothing it writes is published, and it prints counts and hashes
only, never any text.

The relations (agent-inferred from the data rules at `13f8c734:docs/CONVERSATION_DATA.md`, "The
primary distinction"):
- **request** (kind 0): an agent occurrence's `comparison-request`, resolved to an earlier human
  occurrence: the response reaches its request;
- **later human** (kind 1): a human occurrence's `later-human-after-agent`, resolved to an earlier
  agent occurrence: the human return reaches the response it follows.

A relation is declared exactly when its reading occurrence and its target both open a part in the
cut (each occurrence holds one part with cells): the letter ticks of both, the target's earlier.
Every other relation is counted by why it is not declared (`outside`: no development occurrence
holds its target; `before the cut`: the target's part lies before the cut's first cell; `no
cells`: the target holds no part with cells, a harness or a material reference; `none`: the
occurrence declares no such relation). Each declared relation's two letters are checked against the
cut's codes: a letter on the reading port and a letter on the target's.

    HOLONICS_ROOT=<main checkout> python3 research/notebook/hnn_design/curated_incidence.py

An optional `choosing` or `validation` argument reads that F4 role's private source and cut;
pass `F1`, `F2` or `F5` second to read that item's role. Targets absent from the role's source remain unheld.
The exterior join shifts validation's within-role relation ticks into the joint passage.

Outputs in `.local/cuts/`:
- `curated-cut.incidence.bin`: the declared relations in letter order, three little-endian u32 a
  relation (the reading part's letter tick, the kind, the target's letter tick);
- `curated-cut.incidence.json`: its manifest (counts and hashes only).
"""

import hashlib
import json
import os
import sys
from array import array

from standing_cut import OUT_DIR, private_directory, private_write

BYTES = 256
CHANNELS = ("human", "agent", "tool")
KINDS = {"comparison-request": (0, "agent", "human"), "later-human-after-agent": (1, "human", "agent")}


def letter_tick(occurrence, start):
    """The stream position of the occurrence's section letter less the cut's start, or None."""
    for part in occurrence["parts"]:
        if "letter" in part:
            return part["cells"][0] - 1 - start
    return None


def main():
    arguments = sys.argv[1:]
    if arguments and (len(arguments) not in (1, 2) or arguments[0] not in ("choosing", "validation") or (len(arguments) == 2 and arguments[1] not in ("F1", "F2", "F5"))):
        sys.exit(__doc__)
    item = arguments[1].lower() if len(arguments) == 2 else "f4"
    prefix = "curated" if not arguments else f"curated-{item}-{arguments[0]}"
    with open(os.path.join(OUT_DIR, prefix + "-source.json"), "rb") as handle:
        manifest = json.load(handle)
    cut = manifest["cut"]
    start, cells, held = cut["stream_start"], cut["cells"], cut["held_out_start"]
    with open(os.path.join(OUT_DIR, prefix + "-cut.bin"), "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == cut["cut_sha256"], "the pinned cut"
    codes = array("H")
    codes.frombytes(raw)
    if sys.byteorder != "little":
        codes.byteswap()
    assert len(codes) == cells
    incidence_path = os.path.join(OUT_DIR, prefix + "-source.incidence.jsonl")
    with open(incidence_path, "rb") as handle:
        incidence_bytes = handle.read()
    assert hashlib.sha256(incidence_bytes).hexdigest() == manifest["incidence_sha256"], "the incidence"
    occurrences = [json.loads(line) for line in incidence_bytes.splitlines()]

    def channel_at(tick):
        code = codes[tick]
        return CHANNELS[(code - BYTES) % len(CHANNELS)] if code >= BYTES else None

    records = []
    counts = {name: {part: {} for part in ("development", "held_out")} for name in KINDS}
    for occurrence in occurrences:
        tick = letter_tick(occurrence, start)
        if tick is None or tick < 0:
            continue
        part = "development" if tick < held else "held_out"
        for name, (kind, reader, target_port) in KINDS.items():
            if occurrence["port"] != reader:
                continue
            table = counts[name][part]
            relations = [r for r in occurrence["relations"] if r["kind"] == name]
            if not relations:
                table["none"] = table.get("none", 0) + 1
                continue
            assert len(relations) == 1, "one relation of a kind an occurrence"
            relation = relations[0]
            if relation["state"] != "earlier":
                reason = relation["state"]
            else:
                target = occurrences[relation["occurrence"]]
                target_tick = letter_tick(target, start)
                if target["port"] != target_port or target_tick is None:
                    reason = "no cells"
                elif target_tick < 0:
                    reason = "before the cut"
                else:
                    assert target_tick < tick
                    assert channel_at(tick) == reader and channel_at(target_tick) == target_port
                    records.append((tick, kind, target_tick))
                    reason = "declared"
            table[reason] = table.get(reason, 0) + 1
    records.sort()
    assert all(a[0] < b[0] for a, b in zip(records, records[1:])), "one relation a part"
    packed = array("I", [value for record in records for value in record])
    if sys.byteorder != "little":
        packed.byteswap()
    data = packed.tobytes()
    private_directory()
    private_write(prefix + "-cut.incidence.bin", data)
    out = {
        "schema": "holonics.curated-cut-incidence.v1",
        "encoding": "u32 little-endian triples: reading letter tick, kind (0 request, 1 later human), target letter tick",
        "cut_sha256": cut["cut_sha256"],
        "incidence_sha256": manifest["incidence_sha256"],
        "relations": len(records),
        "counts": counts,
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    private_write(prefix + "-cut.incidence.json", json.dumps(out, indent=2).encode("utf-8"))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
