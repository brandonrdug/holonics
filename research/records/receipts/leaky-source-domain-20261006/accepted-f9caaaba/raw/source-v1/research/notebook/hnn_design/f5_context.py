"""Extract F5 request context from declared provider-parent incidence.

This is an exterior source codec. It reads only visible part byte ranges in the
request's provider-parent closure, never a selected response's source range. The
caller supplies the full-source cell extent and context-cell ceiling. A context is a causal
boundary over actual incidence; source adjacency is never used to fill a gap.

The prospective F5 consumer is the request/response helical pair: request and
response are its receiving ports, while this packet supplies the request-side
tube and its continuation thread. Helix, pair and cell holonomy remain attached.
Winding objects touched: faces/placement, tube, and tower thread.

A full-source manifest that does not name the development reserve as excluded (every source written
before the reserve was named) is refused unless the logged flag `--read-reserve` is passed
(`development_families.py`).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import BinaryIO, Mapping, Sequence

from development_families import require_reserve_excluded, reserve_flag


class ContextRefusal(ValueError):
    """The declared causal chain cannot be represented under its cell ceiling."""


def parse_coordinates(coordinate: str) -> tuple[int, int]:
    """Return response/request occurrence ordinals, without reading their contents."""
    try:
        response, request = (int(value) for value in coordinate.split(":"))
    except (ValueError, TypeError) as exc:
        raise ContextRefusal("malformed retrospective coordinate") from exc
    if request < 0 or response <= request:
        raise ContextRefusal("selected response must follow its request")
    return response, request


def load_incidence(path: Path, max_occurrence: int,
                   excluded_occurrences: set[int] | None = None) -> list[dict | None]:
    """Read incidence only through the greatest requested ordinal.

    Selected response rows before the last request ordinal are skipped before
    JSON decoding. The binary source is separately accessed only at part
    coordinates reached by parent traversal.
    """
    excluded = excluded_occurrences or set()
    rows: list[dict | None] = []
    with path.open("rb") as handle:
        for line_number in range(max_occurrence + 1):
            raw = handle.readline()
            if not raw:
                break
            if line_number in excluded:
                rows.append(None)
                continue
            row = json.loads(raw)
            if row.get("occurrence") != line_number:
                raise ContextRefusal("incidence occurrence ordinals are not contiguous")
            rows.append(row)
    if len(rows) <= max_occurrence:
        raise ContextRefusal("request occurrence is outside the supplied incidence prefix")
    return rows


def _provider_parent(row: Mapping) -> int | None:
    relations = [link for link in row.get("relations", []) if link.get("kind") == "provider-parent"]
    if len(relations) > 1:
        raise ContextRefusal("multiple provider-parent edges on one occurrence")
    if not relations:
        return None
    link = relations[0]
    if link.get("state") == "earlier":
        parent = link.get("occurrence")
        if not isinstance(parent, int):
            raise ContextRefusal("earlier provider-parent has no occurrence coordinate")
        return parent
    if link.get("state") == "none declared":
        return None
    raise ContextRefusal(f"provider-parent is unresolved ({link.get('state', 'unknown')})")


def _part_ranges(row: Mapping, source_cell_extent: int) -> list[tuple[int, int, Mapping]]:
    result = []
    for part in row.get("parts", []):
        if "letter" not in part:
            # Empty parts and material references have no visible UTF-8 cells.
            continue
        cells = part.get("cells")
        if not (isinstance(cells, list) and len(cells) == 2
                and all(isinstance(cell, int) for cell in cells)):
            raise ContextRefusal("visible part has no exact cell range")
        start, end = cells
        if start < 0 or end < start or end > source_cell_extent:
            raise ContextRefusal("causal chain leaves the full-source cell extent")
        result.append((start, end, part))
    return result


def _text(reader: BinaryIO, start: int, end: int) -> str:
    reader.seek(start * 2)
    raw = reader.read((end - start) * 2)
    if len(raw) != (end - start) * 2:
        raise ContextRefusal("source binary ends inside a visible part")
    codes = [raw[i] | raw[i + 1] << 8 for i in range(0, len(raw), 2)]
    if any(code > 255 for code in codes):
        raise ContextRefusal("part range contains a section code, not UTF-8 bytes")
    try:
        return bytes(codes).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContextRefusal("visible part is not valid UTF-8") from exc


def extract_one(
    rows: Sequence[Mapping], reader: BinaryIO, request_occurrence: int,
    source_cell_extent: int, context_cell_ceiling: int,
) -> dict:
    """Build one ordered request-plus-parent packet, refusing any broken chain."""
    if not 0 <= request_occurrence < len(rows):
        raise ContextRefusal("request occurrence is outside supplied incidence")
    if source_cell_extent < 0 or context_cell_ceiling < 0:
        raise ContextRefusal("source extent and context-cell ceiling must be nonnegative")

    reverse_chain: list[int] = []
    seen: set[int] = set()
    current = request_occurrence
    while True:
        if current in seen:
            raise ContextRefusal("cyclic provider-parent chain")
        if current < 0 or current >= len(rows):
            raise ContextRefusal("provider-parent is outside the supplied incidence prefix")
        if rows[current] is None:
            raise ContextRefusal("provider-parent reaches a selected response occurrence")
        seen.add(current)
        reverse_chain.append(current)
        parent = _provider_parent(rows[current])
        if parent is None:
            break
        if parent in seen:
            raise ContextRefusal("cyclic provider-parent chain")
        if parent >= current:
            raise ContextRefusal("provider-parent does not point to an earlier occurrence")
        current = parent

    ordered = list(reversed(reverse_chain))
    # Certify the complete incidence restriction and source extent before seeking
    # any source cells, so a refused chain does not partially expose a branch.
    ranges_by_occurrence = {
        ordinal: _part_ranges(rows[ordinal], source_cell_extent) for ordinal in ordered
    }
    # A visible section letter precedes each nonempty part in curated_source's
    # u16 chart. Count it with the part's UTF-8 byte cells in the context bound.
    context_cells = sum(end - start + 1 for ranges in ranges_by_occurrence.values()
                        for start, end, _ in ranges)
    if context_cells > context_cell_ceiling:
        raise ContextRefusal("causal parent chain exceeds the declared context-cell ceiling")
    occurrences = []
    for ordinal in ordered:
        row = rows[ordinal]
        if row.get("occurrence") != ordinal:
            raise ContextRefusal("occurrence coordinate mismatch")
        parts = []
        ranges = ranges_by_occurrence[ordinal]
        range_by_cells = {(start, end): part for start, end, part in ranges}
        for source_index, source_part in enumerate(row.get("parts", [])):
            if "letter" not in source_part:
                continue
            start, end = source_part["cells"]
            part = range_by_cells[(start, end)]
            parts.append({
                "part": source_index,
                "occurrence": ordinal,
                "port": row.get("port"),
                "channel": part.get("channel"),
                "section": part.get("letter"),
                "cells": [start, end],
                "text": _text(reader, start, end),
            })
        occurrences.append({
            "occurrence": ordinal,
            "port": row.get("port"),
            "conversation": row.get("conversation"),
            "parts": parts,
        })
    request = occurrences[-1]
    if request["port"] != "human" or not any(
        part["channel"] == "human" and part["text"] for part in request["parts"]
    ):
        raise ContextRefusal("request occurrence is not a nonempty visible human request")
    return {
        "schema": "holonics.f5-request-context.v1",
        "status": "context",
        "request_occurrence": request_occurrence,
        "source_cell_extent": source_cell_extent,
        "context_cells": context_cells,
        "context_cell_ceiling": context_cell_ceiling,
        "causal_occurrences": occurrences,
    }


def _private_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    os.chmod(path.parent, 0o700)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT, 0o600)
    with os.fdopen(descriptor, "wb") as handle:
        os.fchmod(handle.fileno(), 0o600)
        os.ftruncate(handle.fileno(), 0)
        handle.write(data)


def _refusal_packet(request_occurrence: int, refusal: ContextRefusal) -> dict:
    return {
        "schema": "holonics.f5-request-context.v1",
        "status": "refused",
        "request_occurrence": request_occurrence,
        "refusal": {"type": "context-refusal", "reason": str(refusal)},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True, help="little-endian u16 curated source")
    parser.add_argument("--selection", type=Path, required=True, help="owner-only F5 retrospective JSON")
    parser.add_argument("--manifest", type=Path, required=True,
                        help="full development curated-source manifest")
    parser.add_argument("--output", type=Path, required=True, help="owner-only JSONL context packets")
    parser.add_argument("--context-cells", type=int, required=True,
                        help="caller-declared n* ceiling for causal context cells")
    arguments, read_reserve = reserve_flag(sys.argv[1:], "f5_context.py")
    args = parser.parse_args(arguments)
    with args.manifest.open("rb") as handle:
        manifest = json.load(handle)
    if manifest.get("schema") != "holonics.curated-source.v1":
        raise ContextRefusal("unexpected full-source manifest schema")
    require_reserve_excluded(manifest, "the full development curated source", read_reserve)

    # Read only request ordinals from the selector. Its request text is not used;
    # selected response ordinals are validated as later coordinates and discarded.
    with args.selection.open("rb") as handle:
        selection = json.load(handle)
    if selection.get("schema") != "holonics.f5-retrospective.v1":
        raise ContextRefusal("unexpected F5 selector schema")
    items = selection.get("items")
    if not isinstance(items, list) or len(items) != selection.get("selected") or len(items) != 32:
        raise ContextRefusal("F5 selector must contain its 32 pinned requests")
    coordinates = [parse_coordinates(item.get("coordinate", "")) for item in items]
    request_ordinals = [request for _, request in coordinates]
    response_ordinals = {response for response, _ in coordinates}
    source_cell_extent = manifest.get("development_stream_cells")
    if not isinstance(source_cell_extent, int) or source_cell_extent < 0:
        raise ContextRefusal("manifest has no full-source cell extent")
    if args.source.stat().st_size != source_cell_extent * 2:
        raise ContextRefusal("source binary extent does not match the manifest")
    rows = load_incidence(args.incidence, max(request_ordinals), response_ordinals)

    output = bytearray()
    refused = 0
    with args.source.open("rb") as source:
        for request in request_ordinals:
            try:
                packet = extract_one(rows, source, request, source_cell_extent, args.context_cells)
            except ContextRefusal as refusal:
                packet = _refusal_packet(request, refusal)
                refused += 1
            output.extend(json.dumps(packet, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
            output.extend(b"\n")
    _private_write(args.output, bytes(output))
    print(json.dumps({"requests": len(request_ordinals), "refused": refused,
                      "context_sha256": hashlib.sha256(output).hexdigest()}))


if __name__ == "__main__":
    main()
