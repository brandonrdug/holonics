"""Cold, source-qualified occurrence-family exposure from a prepared package.

This is an exterior reader. It does not tokenize, call a model, construct a native
current, select a response, or assign a score. Each JSONL frame represents one
provider-declared occurrence family; captured views of that occurrence stay together.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import collections
import json
import os
from pathlib import Path
import sqlite3
import tempfile
from typing import Any, TextIO

from conversation_data import SCHEMA as CONVERSATION_SCHEMA, connect


EXPOSURE_SCHEMA = "holonics.conversation-exposure.v1"
DEVELOPMENT_CUT = "2026-09-04T00:00:00Z"
HUMAN_VISIBLE = frozenset({"human-text", "human-material", "human-command"})
AGENT_VISIBLE = frozenset({"agent-text", "agent-material"})


class ExposureError(ValueError):
    """A malformed source package or exposure request."""


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def _aware_time(value: str | None) -> _dt.datetime | None:
    if not isinstance(value, str) or not value:
        return None
    try:
        parsed = _dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
        return parsed.astimezone(_dt.timezone.utc) if parsed.tzinfo is not None else None
    except (TypeError, ValueError, OverflowError):
        return None


def _normalized_time(value: str | None) -> str | None:
    parsed = _aware_time(value)
    return parsed.isoformat(timespec="microseconds") if parsed is not None else None


def _development_cut(value: str) -> _dt.datetime:
    parsed = _aware_time(value)
    if parsed is None:
        raise ExposureError(f"development cut is not an aware ISO timestamp: {value}")
    return parsed


def _event_row(db: sqlite3.Connection, event: int) -> sqlite3.Row:
    row = db.execute(
        """
        SELECT e.id,e.source,e.record_number,e.byte_start,e.byte_end,e.timestamp,
               e.native_id,e.parent_id,e.session_id,e.branch_id,e.workspace,e.phase,
               e.turn_id,e.model,e.author_class,e.record_kind,e.flags,e.previous_record,e.provider_metadata,
               s.provider
        FROM events AS e JOIN sources AS s ON s.id=e.source
        WHERE e.id=?
        """,
        (event,),
    ).fetchone()
    if row is None:
        raise ExposureError(f"event {event} is absent")
    return row


def _target_metadata(db: sqlite3.Connection, event: int | None) -> dict[str, Any] | None:
    if event is None:
        return None
    row = _event_row(db, event)
    group = f"declared:{row['native_id']}" if row["native_id"] is not None else f"capture:{row['id']}"
    return {
        "event": row["id"],
        "source": row["source"],
        "provider": row["provider"],
        "record_group": group,
        "timestamp": row["timestamp"],
        "normalized_timestamp": _normalized_time(row["timestamp"]),
    }


def _link_availability(
    kind: str,
    source_timestamp: str | None,
    target: dict[str, Any] | None,
    target_event: int | None,
) -> str:
    if target_event is None or target is None:
        return "unresolved"
    if kind.endswith("-candidate"):
        return "ambiguous"
    source_time = _aware_time(source_timestamp)
    target_time = _aware_time(target["timestamp"])
    if source_time is None or target_time is None:
        return "unresolved"
    return "prior" if target_time < source_time else "not-prior"


def _event_frame(db: sqlite3.Connection, event: int, comparison_requests: dict) -> dict[str, Any]:
    row = _event_row(db, event)
    flags = json.loads(row["flags"] or "[]")
    parts = [dict(part) for part in db.execute(
        "SELECT ordinal,pointer,kind,text FROM parts WHERE event=? ORDER BY ordinal", (event,)
    )]
    if row["author_class"] == "human":
        visible = HUMAN_VISIBLE
    elif row["author_class"] == "agent-visible":
        visible = AGENT_VISIBLE
    else:
        visible = frozenset()
    links: list[dict[str, Any]] = []
    # Only actual outgoing edges. Reversing a descendant's parent edge would name a future
    # descendant as this occurrence's parent, even if its payload stayed outside the frame.
    raw_links = db.execute(
        "SELECT kind,target_event,reference,evidence FROM links WHERE source_event=? "
        "ORDER BY kind,target_event", (event,)
    )
    for link in raw_links:
        target = _target_metadata(db, link["target_event"])
        links.append({
            "kind": link["kind"],
            "target_event": link["target_event"],
            "reference": link["reference"],
            "evidence": link["evidence"],
            "target": target,
            "availability": _link_availability(link["kind"], row["timestamp"], target, link["target_event"]),
        })
    # Comparison request references belong only on the actual agent occurrence.
    if row["author_class"] == "agent-visible":
        for comparison in comparison_requests.get(event, ()):
            target = _target_metadata(db, comparison["user_event"])
            links.append({
                "kind": "comparison-request",
                "target_event": comparison["user_event"],
                "reference": None,
                "evidence": comparison["evidence"],
                "target": target,
                "availability": _link_availability("provider-parent", row["timestamp"], target, comparison["user_event"]),
            })
    links.sort(key=lambda item: (item["kind"], item["target_event"] is None, item["target_event"] or -1))
    return {
        "event": row["id"],
        "source": row["source"],
        "provider": row["provider"],
        "record": {
            "number": row["record_number"],
            "byte_start": row["byte_start"],
            "byte_end": row["byte_end"],
        },
        "timestamp": row["timestamp"],
        "normalized_timestamp": _normalized_time(row["timestamp"]),
        "native_id": row["native_id"],
        "parent_id": row["parent_id"],
        "session_id": row["session_id"],
        "branch_id": row["branch_id"],
        "workspace": row["workspace"],
        "phase": row["phase"],
        "turn_id": row["turn_id"],
        "model": row["model"],
        "author_class": row["author_class"],
        "record_kind": row["record_kind"],
        "flags": flags,
        "provider_metadata": json.loads(row["provider_metadata"]),
        "previous_record": row["previous_record"],
        "visible_parts": [
            {"ordinal": p["ordinal"], "pointer": p["pointer"], "kind": p["kind"], "text": p["text"]}
            for p in parts if p["kind"] in visible
        ],
        "nonvisible_part_references": [
            {"ordinal": p["ordinal"], "pointer": p["pointer"], "kind": p["kind"]}
            for p in parts if p["kind"] not in visible
        ],
        "links": links,
    }


def _selected_event_keys(db: sqlite3.Connection) -> set[tuple[str, str, int | None]]:
    keys: set[tuple[str, str, int | None]] = set()
    for row in db.execute(
        """
        SELECT s.provider,e.native_id,e.id
        FROM events AS e JOIN sources AS s ON s.id=e.source
        WHERE e.author_class IN ('human','agent-visible')
        """
    ):
        keys.add((row["provider"], f"declared:{row['native_id']}" if row["native_id"] is not None else f"capture:{row['id']}", None if row["native_id"] is not None else row["id"]))
    return keys


def _family_views(db: sqlite3.Connection, key: tuple[str, str, int | None]) -> list[int]:
    provider, group, capture_event = key
    if group.startswith("capture:"):
        return [capture_event]
    native_id = group.removeprefix("declared:")
    return [
        row["id"] for row in db.execute(
            "SELECT e.id FROM events e JOIN sources s ON s.id=e.source WHERE s.provider=? AND e.native_id=? ORDER BY e.source,e.record_number,e.id",
            (provider, native_id),
        )
    ]


def _family_partition(views: list[dict[str, Any]], cut: _dt.datetime) -> tuple[str, list[str], list[dict[str, Any]]]:
    reasons: list[str] = []
    conflicts: list[dict[str, Any]] = []
    times = [(v["event"], v["timestamp"], v["normalized_timestamp"]) for v in views]
    parsed = [_aware_time(v["timestamp"]) for v in views]
    known = [value for value in parsed if value is not None]
    if any(value is None for value in parsed):
        reasons.append("missing-or-invalid-timestamp")
    if len({v["normalized_timestamp"] for v in views}) > 1 and known:
        reasons.append("conflicting-view-timestamps")
        conflicts.append({"kind": "timestamp", "views": times})
    if any(value >= cut for value in known):
        reasons.append("timestamp-at-or-after-development-cut")
    if known and any(value >= cut for value in known) and any(value < cut for value in known):
        reasons.append("crosses-development-cut")
    authors = [(v["event"], v["author_class"]) for v in views]
    if len({v["author_class"] for v in views}) > 1:
        reasons.append("conflicting-view-author-roles")
        conflicts.append({"kind": "author-role", "views": authors})
    # These are exact exterior codeword comparisons within an already declared view family,
    # not hashes identifying different occurrences. JSON pointers remain view-local coordinates.
    presentations = [tuple((p["ordinal"], p["kind"], p["text"]) for p in v["visible_parts"])
                     for v in views]
    if any(material != presentations[0] for material in presentations[1:]):
        reasons.append("conflicting-view-material")
        conflicts.append({"kind": "material", "events": [v["event"] for v in views]})
    if any(v["author_class"] in {"human", "agent-visible"} and not v["visible_parts"] for v in views):
        reasons.append("missing-visible-role-material")
    contradictory = [
        {
            "event": view["event"],
            "request_event": link["target_event"],
            "availability": link["availability"],
        }
        for view in views
        for link in view["links"]
        if link["kind"] == "comparison-request" and link["availability"] == "not-prior"
    ]
    if contradictory:
        reasons.append("contradictory-request-response-order")
        conflicts.append({"kind": "request-response-order", "views": contradictory})
    reasons = list(dict.fromkeys(reasons))
    if any(reason.startswith("missing") or reason.startswith("conflicting") or reason.startswith("contradictory") for reason in reasons):
        partition = "deferred"
    elif any(reason.startswith("timestamp-at") or reason.startswith("crosses") for reason in reasons):
        partition = "evaluation"
    else:
        partition = "development"
    return partition, reasons, conflicts


def _manifest(db: sqlite3.Connection, cut: str) -> dict[str, Any]:
    return {
        "schema": EXPOSURE_SCHEMA,
        "kind": "manifest",
        "temporal_cut": cut,
        "temporal_cut_normalized": _normalized_time(cut),
        "private_sources": [
            {
                "source": row["id"],
                "provider": row["provider"],
                "private_path": row["path"],
                "captured_octets": row["captured_octets"],
                "records": row["records"],
            }
            for row in db.execute("SELECT id,provider,path,captured_octets,records FROM sources ORDER BY id")
        ],
        "boundary": {
            "family_key": "provider plus declared native_id; capture event when native_id is absent",
            "population": "every visible human/agent event and all captured views of its declared occurrence; unpaired material is retained",
            "ordering": "known occurrence timestamp, then source/record/event capture coordinates",
            "unknown_or_conflicting": "retain every view and defer the family with exact view evidence",
            "links": "target metadata and coordinates only; no target text",
            "paths": "private manifest coordinates, never native semantic fields",
        },
        "visible_parts": {"human": sorted(HUMAN_VISIBLE), "agent": sorted(AGENT_VISIBLE)},
    }


def _atomic_private_text(path: Path) -> tuple[TextIO, Path]:
    if path.exists():
        raise FileExistsError(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.partial-", dir=path.parent)
    os.fchmod(fd, 0o600)
    return os.fdopen(fd, "w", encoding="utf-8"), Path(temporary)


def export_exposure(dataset: Path, output: Path, development_cut: str = DEVELOPMENT_CUT) -> dict[str, Any]:
    """Export one cold occurrence-family stream from a prepared SQLite package."""

    cut = _development_cut(development_cut)
    target, temporary = _atomic_private_text(output)
    family_count = development_count = evaluation_count = deferred_count = view_count = 0
    try:
        with connect(dataset) as db:
            db.execute("BEGIN")  # One coherent read transaction; the source is opened read-only.
            schema = db.execute("SELECT value FROM metadata WHERE key='schema'").fetchone()
            if schema is None or json.loads(schema[0]) != CONVERSATION_SCHEMA:
                raise ExposureError("unsupported conversation package schema")
            comparison_requests = collections.defaultdict(list)
            for row in db.execute("SELECT agent_event,user_event,evidence FROM comparisons ORDER BY agent_event,user_event"):
                comparison_requests[row["agent_event"]].append(dict(row))
            target.write(_json(_manifest(db, development_cut)) + "\n")
            families = []
            # Sort narrow source metadata, not every visible message body. Material is fetched
            # one family at a time after the order has been established.
            for provider, group, capture_event in _selected_event_keys(db):
                event_ids = _family_views(db, (provider, group, capture_event))
                metadata = [_event_row(db, event) for event in event_ids]
                known = [t for v in metadata if (t := _aware_time(v["timestamp"])) is not None]
                sort_time = min(known) if known else _dt.datetime.max.replace(tzinfo=_dt.timezone.utc)
                first_position = min((v["source"], v["record_number"], v["id"]) for v in metadata)
                families.append((sort_time, first_position, provider, group, event_ids))
            families.sort(key=lambda item: (item[0], item[1], item[2], item[3]))
            for sequence, (_, first_position, provider, group, event_ids) in enumerate(families):
                views = [_event_frame(db, event, comparison_requests) for event in event_ids]
                partition, reasons, conflicts = _family_partition(views, cut)
                family_count += 1
                view_count += len(views)
                if partition == "development": development_count += 1
                elif partition == "evaluation": evaluation_count += 1
                else: deferred_count += 1
                record_group = group if group.startswith("declared:") else f"capture:{group.removeprefix('capture:')}"
                target.write(_json({
                    "schema": EXPOSURE_SCHEMA,
                    "kind": "occurrence-family",
                    "sequence": sequence,
                    "position": {
                        "first_source": first_position[0],
                        "first_record": first_position[1],
                        "first_event": first_position[2],
                    },
                    "family": {"provider": provider, "record_group": record_group},
                    "partition": partition,
                    "partition_reasons": reasons,
                    "conflicts": conflicts,
                    "views": views,
                }) + "\n")
        target.flush()
        os.fsync(target.fileno())
        target.close()
        os.link(temporary, output)
        temporary.unlink()
        directory = os.open(output.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except BaseException:
        try:
            target.close()
        finally:
            temporary.unlink(missing_ok=True)
        raise
    return {
        "schema": EXPOSURE_SCHEMA,
        "output": str(output),
        "private": True,
        "families": family_count,
        "development_families": development_count,
        "evaluation_families": evaluation_count,
        "deferred_families": deferred_count,
        "views": view_count,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dataset", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--development-cut", default=DEVELOPMENT_CUT)
    args = parser.parse_args()
    print(_json(export_exposure(args.dataset, args.output, args.development_cut)))


if __name__ == "__main__":
    main()
