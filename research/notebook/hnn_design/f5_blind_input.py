"""Prepare private development-diagnostic blind cases without opening recorded replies.

The native candidates are provisional and the context refusals are explicit; this package is
for development inspection, not F5's final acceptance or evaluation partition. Raw text stays
owner-only. Stdout contains counts and hashes.

    HOLONICS_ROOT=<checkout with private cuts> python3 f5_blind_input.py
"""

import hashlib
import json
import os
import re
import sys
from pathlib import Path

from standing_cut import OUT_DIR, private_directory, private_write


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    root = Path(OUT_DIR)
    selection = json.loads((root / "f5-retrospective.json").read_bytes())
    contexts = [json.loads(line) for line in (root / "f5-context.jsonl").read_bytes().splitlines()]
    assert selection["schema"] == "holonics.f5-retrospective.v1"
    assert len(selection["items"]) == len(contexts) == 32
    statuses = {}
    for line in (root / "f5-diagnostic-32.log").read_text().splitlines():
        match = re.search(r"^F5 development diagnostic request (\d+): status ([^;]+)", line)
        if match:
            statuses[int(match.group(1))] = match.group(2)
    assert sorted(statuses) == list(range(32))

    cases = []
    for index, (item, context) in enumerate(zip(selection["items"], contexts)):
        assert int(item["coordinate"].split(":")[1]) == context["request_occurrence"]
        status = statuses[index]
        response_path = root / "f5-diagnostic-32" / f"request-{index:02}.bin"
        assert response_path.stat().st_mode & 0o777 == 0o600
        candidate = response_path.read_bytes().decode("utf-8") if status.startswith("provisional-") else f"[typed refusal: {status}]"
        if context["status"] == "context":
            earlier = context["causal_occurrences"][:-1]
            declared = "\n".join(f"[{part['port']}/{part['section']}] {part['text']}"
                                 for occurrence in earlier for part in occurrence["parts"])
        else:
            declared = "[unresolved provider-parent; context refused]"
        cases.append({"coordinate": item["coordinate"], "request": item["request"],
                      "context": declared, "grain": "L_R = 16; provisional development face",
                      "responses": {
                          "athena": {"label": "native family diagnostic", "text": candidate},
                          "control": {"label": "request-aware retrieval control", "text": item["retrieval"] or "[retrieval refused]"},
                      }})
    document = {"schema": "holonics.athena-blind-input.v1",
                "coordinate_order": [case["coordinate"] for case in cases], "cases": cases}
    raw = json.dumps(document, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    private_directory()
    private_write("f5-blind-input.json", raw)
    seed_path = root / "f5-blind-seed.bin"
    if seed_path.exists():
        assert seed_path.stat().st_mode & 0o777 == 0o600
        seed = seed_path.read_bytes()
    else:
        seed = os.urandom(32).hex().encode("ascii")
        private_write("f5-blind-seed.bin", seed)
    assert len(seed) == 64 and b"\0" not in seed
    print(json.dumps({"cases": len(cases), "provisional": sum(status.startswith("provisional-") for status in statuses.values()),
                      "input_sha256": hashlib.sha256(raw).hexdigest(),
                      "seed_commitment": hashlib.sha256(b"holonics/athena-blind/seed-commitment/v1\0" + seed).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
