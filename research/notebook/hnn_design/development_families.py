"""Pin F4's choosing/validation split over development occurrence families.

The source's evaluation and deferred records are inspected only for their partition label.
Family keys and assignments stay in an owner-only file; stdout contains counts and hashes.

    HOLONICS_ROOT=<checkout with private data> python3 development_families.py

Pass `F1`, `F2`, `F5`, `U2`, `F2V2` or `F0` for an independent item split before its validation; the
default remains the pinned F4 split. Each item's seed is declared in `SEEDS` (U2's acceptance run: its
record's pin 1; `F2V2`, F2's adoption gate on the receiving population: THE_REBUILD F2, the pins of
September 28, a fresh split because F2's first validation tail was read once on September 27; `F0`,
F0's acceptance run: its record's pin 1, a fresh split because every earlier split is spent).

The split belongs to the exterior codec. A family is the undivided pair
``(provider, record_group)`` from the dataset, not a byte span or an aeon. SHA-256 of the
declared seed, a NUL separator and its canonical JSON gives a hash-seeded assignment: residue
zero modulo five is validation, the other four residues are choosing. The family is assigned
before any response is read. Later consumers recompute the same assignment from their family
keys; no private family key is written to a tracked file.
"""

import hashlib
import json
import os
import re
import sys

from standing_cut import OUT_DIR, SOURCE, private_directory, private_write

SEED = "holonics-f4-development-families-2026-09-27-v1"
SEEDS = {
    "F4": SEED,
    "F1": "holonics-f1-development-families-2026-09-27-v1",
    "F2": "holonics-f2-development-families-2026-09-27-v1",
    "F5": "holonics-f5-development-families-2026-09-27-v1",
    "U2": "holonics-u2-development-families-2026-09-28-v1",
    "F2V2": "holonics-f2-development-families-2026-09-28-v2",
    "F0": "holonics-f0-development-families-2026-09-28-v1",
}
NAME = "development-families-f4.json"
PARTITION = re.compile(rb'"partition"\s*:\s*"(development|evaluation|deferred)"')


def canonical_family(family):
    assert set(family) == {"provider", "record_group"}, "one declared family key"
    return json.dumps(family, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def assignment(family, seed=SEED):
    key = canonical_family(family)
    digest = hashlib.sha256(seed.encode() + b"\0" + key).digest()
    return ("validation" if int.from_bytes(digest, "big") % 5 == 0 else "choosing",
            hashlib.sha256(key).hexdigest())


def main():
    arguments = sys.argv[1:]
    if len(arguments) > 1 or (arguments and arguments[0] not in SEEDS):
        sys.exit(__doc__)
    item = arguments[0] if arguments else "F4"
    seed = SEEDS[item]
    name = NAME if item == "F4" else f"development-families-{item.lower()}.json"
    with open(os.path.join(OUT_DIR, "curated-source.json"), "rb") as handle:
        source_manifest = json.load(handle)
    counts = {"choosing": 0, "validation": 0}
    partitions = {"development": 0, "evaluation": 0, "deferred": 0}
    members = []
    seen = set()
    with open(SOURCE, "rb") as handle:
        for line in handle:
            # The partition label precedes the views in this pinned source schema. No
            # nondevelopment record is decoded, and no response field is examined here.
            prefix = line[:line.find(b'"views"')] if b'"views"' in line[:1024] else line[:1024]
            match = PARTITION.search(prefix)
            if match is None:
                continue
            partition = match.group(1).decode("ascii")
            partitions[partition] += 1
            if partition != "development":
                continue
            record = json.loads(line)
            assert record["kind"] == "occurrence-family" and record["partition"] == partition
            role, family_hash = assignment(record["family"], seed)
            assert family_hash not in seen, "each development family occurs once"
            seen.add(family_hash)
            counts[role] += 1
            members.append({"family_sha256": family_hash, "role": role})
    assert partitions == source_manifest["families"], "same pinned source population"
    assert counts["choosing"] > 0 and counts["validation"] > 0
    members.sort(key=lambda item: item["family_sha256"])
    membership_bytes = json.dumps(members, separators=(",", ":"), sort_keys=True).encode()
    receipt = {
        "schema": f"holonics.development-families-{item.lower()}.v1",
        "source_sha256": source_manifest["source_sha256"],
        "seed": seed,
        "canonical": "UTF-8 JSON of family {provider,record_group}, sorted keys, compact separators",
        "hash": "SHA-256(seed UTF-8 || NUL || canonical); big-endian integer mod 5",
        "validation_residue": 0,
        "counts": counts,
        "membership_sha256": hashlib.sha256(membership_bytes).hexdigest(),
        "members": members,
    }
    private_directory()
    private_write(name, json.dumps(receipt, indent=2).encode())
    print(json.dumps({k: receipt[k] for k in ("schema", "source_sha256", "seed", "counts", "membership_sha256")}, indent=2))


if __name__ == "__main__":
    main()
