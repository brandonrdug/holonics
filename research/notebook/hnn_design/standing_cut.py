"""Pin the standing real cut of campaign 1 (THE_REBUILD, review E1, Decisions 16 and 23).

An exterior codec step, run once. It reads the private conversation exposure dataset
(`.local/datasets/athena-alpha-exposure-2026-09-06.jsonl`, schema
`holonics.conversation-exposure.v1`) and writes a pinned byte cut and its manifest into `.local/cuts/`.
Nothing it writes is published; the notebook README reports the cut by scope and counts only.

The dataset declares its own partition at its temporal cut (2026-09-04): `development` families
before it, `evaluation` families at or after it, `deferred` families with conflicting views. The
standing real cut is a development cut (E1): the development stream's last `population` cells, of
which the final `held_out` cells are held out. They are the stream's own later occurrences, so no
held-out cell precedes a training cell. The evaluation partition is not read into the cut: it stays
unspent for the outcomes' frozen task splits (step 8).

Cells are the UTF-8 bytes of each family's first view's visible parts, in the dataset's declared
order (timestamp, then capture coordinates), parts and families each closed by one newline. Roles
and provenance are exterior codec information and are not encoded.

    python3 research/notebook/hnn_design/standing_cut.py <population>

`population` is the declared field's `n*` (campaign 1's smallest admitted population, printed by
`hnn_exposure`). The held-out length is one mean aeon of the joint clock on uniform bytes,
`⌈5·7·11·13·2^8 / (52 + 5·37 + 5·7·24)⌉` cells (the design's "Locks" row), set from the field,
never from the data.
"""

import hashlib
import json
import os
import sys

ROOT = os.environ.get(
    "HOLONICS_ROOT",
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))),
)
SOURCE = os.path.join(ROOT, ".local", "datasets", "athena-alpha-exposure-2026-09-06.jsonl")
OUT_DIR = os.path.join(ROOT, ".local", "cuts")
NAME = "standing-real-cut-campaign-1"


def mean_aeon_cells():
    numerator = 5 * 7 * 11 * 13 * 2**8
    denominator = 52 + 5 * 37 + 5 * 7 * 24
    return -(-numerator // denominator)


def family_bytes(record):
    view = record["views"][0]
    parts = [part.get("text") or "" for part in view.get("visible_parts", [])]
    return ("\n".join(parts) + "\n").encode("utf-8")


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    population = int(sys.argv[1])
    held_out = mean_aeon_cells()
    development = bytearray()
    counts = {"development": 0, "evaluation": 0, "deferred": 0}
    source_hash = hashlib.sha256()
    with open(SOURCE, "rb") as handle:
        for line in handle:
            source_hash.update(line)
            record = json.loads(line)
            if record.get("kind") != "occurrence-family":
                continue
            counts[record["partition"]] += 1
            if record["partition"] == "development":
                development += family_bytes(record)
    assert held_out < population <= len(development), "the development stream cannot hold the cut"
    cut = bytes(development[len(development) - population:])
    os.makedirs(OUT_DIR, exist_ok=True)
    with open(os.path.join(OUT_DIR, NAME + ".bin"), "wb") as handle:
        handle.write(cut)
    os.chmod(os.path.join(OUT_DIR, NAME + ".bin"), 0o600)
    manifest = {
        "schema": "holonics.standing-cut.v2",
        "source": os.path.relpath(SOURCE, ROOT),
        "source_sha256": source_hash.hexdigest(),
        "families": counts,
        "development_stream_bytes": len(development),
        "population": population,
        "held_out_range": [population - held_out, population],
        "from": "development stream tail; the final held_out_range cells held out",
        "cut_sha256": hashlib.sha256(cut).hexdigest(),
    }
    path = os.path.join(OUT_DIR, NAME + ".json")
    with open(path, "w") as handle:
        json.dump(manifest, handle, indent=2)
    os.chmod(path, 0o600)
    print(json.dumps({key: manifest[key] for key in ("families", "development_stream_bytes",
                                                      "population", "held_out_range", "cut_sha256")}))


if __name__ == "__main__":
    main()
