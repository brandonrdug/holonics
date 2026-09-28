"""Select F4's development-validation requests and build its retrieval control.

Only development incidence and request text, plus choosing-family response text, are read.
The validation responses are not sought or decoded. The owner-only output contains the selected
requests and control responses for the later release inspection; stdout is counts and hashes.

    HOLONICS_ROOT=<checkout with private cuts> python3 f4_retrospective.py
"""

import hashlib
import json
import os
from array import array

from development_families import PARTITION, SEED, assignment
from standing_cut import OUT_DIR, SOURCE, private_directory, private_write

LIMIT = 32
NAME = "f4-retrospective.json"


def header_object(prefix, key):
    at = prefix.index(('"' + key + '"').encode())
    colon = prefix.index(b":", at)
    return json.JSONDecoder().raw_decode(prefix[colon + 1:].decode("utf-8").lstrip())[0]


def role_by_event():
    roles = {}
    counts = {"choosing": 0, "validation": 0}
    with open(SOURCE, "rb") as handle:
        for line in handle:
            prefix = line[:line.find(b'"views"')] if b'"views"' in line[:1024] else line[:1024]
            match = PARTITION.search(prefix)
            if match is None or match.group(1) != b"development":
                continue
            family = header_object(prefix, "family")
            position = header_object(prefix, "position")
            role, _ = assignment(family)
            counts[role] += 1
            roles[position["first_event"]] = role
    with open(os.path.join(OUT_DIR, "development-families-f4.json"), "rb") as handle:
        pinned = json.load(handle)
    assert counts == pinned["counts"], "the pinned split"
    return roles


def relation(occurrence, kind):
    entries = [r for r in occurrence["relations"] if r["kind"] == kind and r["state"] == "earlier"]
    assert len(entries) <= 1
    return entries[0]["occurrence"] if entries else None


def text_of(source, occurrence, channel):
    parts = []
    for part in occurrence["parts"]:
        if part["channel"] != channel or "letter" not in part:
            continue
        start, end = part["cells"]
        source.seek(start * 2)
        raw = source.read((end - start) * 2)
        assert len(raw) == 2 * (end - start)
        codes = array("H")
        codes.frombytes(raw)
        import sys
        if sys.byteorder != "little":
            codes.byteswap()
        assert all(code < 256 for code in codes), "a part's bytes"
        parts.append(bytes(int(code) for code in codes).decode("utf-8"))
    return "\n".join(parts)


def grams(text):
    data = text.encode("utf-8")
    return set(data[i:i + 3] for i in range(len(data) - 2)) if len(data) >= 3 else {data}


def best_control(request, before, candidates):
    query = grams(request)
    best = None
    for request_at, response_at, candidate_request, candidate_response in candidates:
        if response_at >= before:
            continue
        candidate = grams(candidate_request)
        overlap = len(query & candidate)
        union = len(query | candidate)
        if best is None or overlap * best[1] > best[0] * union or (
            overlap * best[1] == best[0] * union and request_at > best[2]
        ):
            best = (overlap, union, request_at, candidate_response)
    return None if best is None else best[3]


def main():
    roles = role_by_event()
    with open(os.path.join(OUT_DIR, "curated-source.incidence.jsonl"), "rb") as handle:
        all_occurrences = [json.loads(line) for line in handle]
    with open(os.path.join(OUT_DIR, "curated-f4-validation-source.json"), "rb") as handle:
        validation_manifest = json.load(handle)
    with open(os.path.join(OUT_DIR, "curated-f4-validation-source.incidence.jsonl"), "rb") as handle:
        validation_occurrences = [json.loads(line) for line in handle]
    by_event = {entry["event"]: entry for entry in all_occurrences}
    assert len(by_event) == len(all_occurrences)
    start = validation_manifest["cut"]["stream_start"]
    candidates = []
    eligible = []
    with open(os.path.join(OUT_DIR, "curated-source.bin"), "rb") as source:
        for response in all_occurrences:
            if response["port"] != "agent" or roles.get(response["event"]) != "choosing":
                continue
            request_at = relation(response, "comparison-request")
            if request_at is None:
                continue
            request = all_occurrences[request_at]
            if request["port"] != "human" or roles.get(request["event"]) != "choosing":
                continue
            query = text_of(source, request, "human")
            answer = text_of(source, response, "agent")
            if query and answer:
                candidates.append((request_at, response["occurrence"], query, answer))

        for local in validation_occurrences:
            if local["port"] != "agent":
                continue
            first_letters = [part["cells"][0] - 1 for part in local["parts"] if "letter" in part]
            if not first_letters or min(first_letters) < start:
                continue
            response = by_event[local["event"]]
            assert roles.get(response["event"]) == "validation"
            request_at = relation(response, "comparison-request")
            if request_at is None:
                continue
            request = all_occurrences[request_at]
            if request["port"] != "human":
                continue
            query = text_of(source, request, "human")
            if not query:
                continue
            coordinate = f'{response["occurrence"]}:{request_at}'
            order = hashlib.sha256(SEED.encode() + b"\0F4 inspection" + coordinate.encode()).digest()
            eligible.append((order, coordinate, response["occurrence"], request_at, query))
        eligible.sort()
        chosen = []
        for _, coordinate, response_at, request_at, query in eligible[:LIMIT]:
            control = best_control(query, request_at, candidates)
            chosen.append({"coordinate": coordinate, "request": query, "retrieval": control,
                           "retrieval_refusal": control is None})
    coordinate_bytes = "\n".join(item["coordinate"] for item in chosen).encode()
    receipt = {
        "schema": "holonics.f4-retrospective.v1",
        "seed": SEED,
        "eligible": len(eligible),
        "selected": len(chosen),
        "choosing_pairs": len(candidates),
        "retrieval_refusals": sum(item["retrieval_refusal"] for item in chosen),
        "coordinates_sha256": hashlib.sha256(coordinate_bytes).hexdigest(),
        "items": chosen,
    }
    private_directory()
    private_write(NAME, json.dumps(receipt, ensure_ascii=False).encode("utf-8"))
    print(json.dumps({key: receipt[key] for key in (
        "schema", "eligible", "selected", "choosing_pairs", "retrieval_refusals", "coordinates_sha256"
    )}, indent=2))


if __name__ == "__main__":
    main()
