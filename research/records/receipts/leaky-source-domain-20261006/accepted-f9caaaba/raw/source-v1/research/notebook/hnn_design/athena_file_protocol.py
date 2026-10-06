"""Bounded file-backed protocol fixture with durable JSONL input staging.

This joins a pure candidate transition to the streaming v2 checkpoint. It is a
fixture only: callers supply their native standing decoder/transition/writer.
Input bytes are staged in the v2 metadata. One complete frame remains there
until its transition and pending output commit with candidate standing.
"""
from __future__ import annotations

import base64
import json
from dataclasses import dataclass
from typing import Any, BinaryIO, Callable, Mapping, Protocol

from athena_file_checkpoint import AtomicFileCheckpoint, FileCheckpoint
from athena_protocol import ProtocolError, TypedRefusal, _validate_exact_json

WIRE_VERSION = 1
COMMANDS = frozenset(("Ask", "Inspect", "Checkpoint"))


class CandidateEngine(Protocol):
    """A transition reads old standing by bounded reads and streams its candidate.

    The returned writer owns its prepared state; the old standing reader closes before the
    atomic candidate file is written.
    """

    def ask(self, payload: Mapping[str, Any], standing: BinaryIO) -> "FileTransition": ...
    def inspect(self, payload: Mapping[str, Any], standing: BinaryIO) -> "FileTransition": ...


@dataclass(frozen=True)
class FileTransition:
    result: Mapping[str, Any]
    pending_comparisons: tuple[Mapping[str, Any], ...]
    emit_standing: Callable[[BinaryIO], None]


def _canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def _decode_b64(text: str) -> bytes:
    raw = base64.b64decode(text, validate=True)
    if base64.b64encode(raw).decode("ascii") != text:
        raise ProtocolError("checkpoint base64 is not canonical")
    return raw


def _metadata(checkpoint: FileCheckpoint) -> dict[str, Any]:
    return checkpoint.metadata


def _copy_standing(old: FileCheckpoint, out: BinaryIO) -> None:
    with old.open_standing() as src:
        while True:
            chunk = src.read(1024 * 1024)
            if not chunk:
                break
            out.write(chunk)


class FileProtocol:
    """One complete Ask/Inspect/Checkpoint transition with streamed standing."""

    def __init__(self, store: AtomicFileCheckpoint, engine: CandidateEngine):
        self.store, self.engine = store, engine
        self.state = store.read() if store.path.exists() else None

    def _current(self) -> FileCheckpoint:
        if self.state is None:
            raise ProtocolError("initialize the file checkpoint before processing")
        return self.state

    def process(self, raw_frame: bytes) -> bytes:
        """Compatibility entry for a complete frame; staging precedes transition."""
        frame_bytes = raw_frame[:-1] if raw_frame.endswith(b"\n") else raw_frame
        frame = self._parse(frame_bytes)
        old = self._current()
        meta = _metadata(old)
        pending = meta["pending_output_b64"]
        if pending is not None:
            if frame["sequence"] == meta["pending_sequence"]:
                return _decode_b64(pending)
            raise ProtocolError("pending output must be replayed before another frame")
        if _decode_b64(meta["input_tail_b64"]):
            raise ProtocolError("use feed when an input tail is already staged")
        outputs = self.feed(raw_frame if raw_frame.endswith(b"\n") else raw_frame + b"\n")
        if not outputs:
            raise ProtocolError("complete frame was not committed")
        return outputs[0]

    def _process_frame(self, raw_frame: bytes, remaining_tail: bytes) -> bytes:
        frame = self._parse(raw_frame)
        old = self._current()
        meta = _metadata(old)
        seq, command, payload = frame["sequence"], frame["command"], frame["payload"]
        pending = meta["pending_output_b64"]
        if pending is not None:
            if seq == meta["pending_sequence"]:
                return _decode_b64(pending)
            raise ProtocolError("pending output must be replayed before another frame")
        if seq != meta["cursor"] + 1:
            raise ProtocolError("sequence must immediately follow acknowledged cursor")

        comparisons = meta["pending_comparisons"]
        status = "ok"
        try:
            if command == "Checkpoint":
                result: Mapping[str, Any] = {
                    "cursor": meta["cursor"],
                    "standing_bytes": old.standing_length,
                    "pending_comparisons": len(comparisons),
                }
                emit = lambda out: _copy_standing(old, out)
                next_comparisons = comparisons
            else:
                with old.open_standing() as standing:
                    transition = (self.engine.ask(payload, standing) if command == "Ask"
                                  else self.engine.inspect(payload, standing))
                if not isinstance(transition, FileTransition) or not isinstance(transition.result, Mapping):
                    raise TypedRefusal("incomplete-release-receipt", "missing typed candidate transition")
                result = transition.result
                if command == "Ask":
                    _validate_ask(result)
                _validate_exact_json(dict(result))
                next_comparisons = list(transition.pending_comparisons)
                _validate_exact_json(next_comparisons)
                emit = transition.emit_standing
        except TypedRefusal as refusal:
            status = "refused"
            result = {"type": refusal.code, "detail": refusal.detail}
            next_comparisons = comparisons
            emit = lambda out: _copy_standing(old, out)

        output = _canonical({"version": WIRE_VERSION, "sequence": seq,
                             "command": command, "status": status,
                             "result": dict(result)}) + b"\n"
        new_meta = {
            "cursor": seq,
            "pending_comparisons": next_comparisons,
            "input_tail_b64": base64.b64encode(remaining_tail).decode("ascii"),
            "pending_output_b64": base64.b64encode(output).decode("ascii"),
            "pending_sequence": seq,
        }
        # The engine's candidate writer runs inside AtomicFileCheckpoint's temp file.
        self.state = self.store.write_generated(new_meta, None, emit)
        return output

    def feed(self, chunk: bytes) -> list[bytes]:
        """Stage bytes atomically, then commit at most one complete frame.

        Metadata-only staging copies standing by bounded reads. A transition failure
        leaves the durable tail untouched, including the complete unacknowledged frame.
        Later frames remain in that tail until the current output is acknowledged.
        """
        if not isinstance(chunk, bytes):
            raise ProtocolError("input chunk must be bytes")
        old = self._current()
        meta = _metadata(old)
        prior_tail = _decode_b64(meta["input_tail_b64"])
        if chunk:
            staged = dict(meta)
            staged["input_tail_b64"] = base64.b64encode(prior_tail + chunk).decode("ascii")
            self.state = self.store.write_generated(
                staged, old.standing_length, lambda out: _copy_standing(old, out))
            old = self.state
            meta = _metadata(old)
            prior_tail += chunk

        if meta["pending_output_b64"] is not None:
            return []
        frame_bytes, separator, remainder = prior_tail.partition(b"\n")
        if not separator:
            return []
        if not frame_bytes:
            raise ProtocolError("empty input frame")
        output = self._process_frame(frame_bytes, remainder)
        return [output]

    def replay_pending(self) -> bytes | None:
        pending = _metadata(self._current())["pending_output_b64"]
        return _decode_b64(pending) if pending is not None else None

    def acknowledge_output(self, sequence: int) -> None:
        old = self._current()
        meta = _metadata(old)
        if meta["pending_sequence"] != sequence or meta["pending_output_b64"] is None:
            raise ProtocolError("no matching pending output")
        updated = dict(meta)
        updated["pending_output_b64"] = None
        updated["pending_sequence"] = None
        self.state = self.store.write_generated(
            updated, old.standing_length, lambda out: _copy_standing(old, out))

    @staticmethod
    def _parse(raw: bytes) -> dict[str, Any]:
        try:
            value = json.loads(raw)
            if not isinstance(value, dict) or set(value) != {"version", "sequence", "command", "payload"}:
                raise ProtocolError("frame fields must be version, sequence, command, payload")
            if type(value["version"]) is not int or value["version"] != WIRE_VERSION:
                raise ProtocolError("unsupported input wire version")
            if type(value["sequence"]) is not int or value["sequence"] < 1:
                raise ProtocolError("sequence must be a positive integer")
            if value["command"] not in COMMANDS or not isinstance(value["payload"], dict):
                raise ProtocolError("unknown command or non-object payload")
            _validate_exact_json(value["payload"])
            return value
        except ProtocolError:
            raise
        except (ValueError, TypeError) as exc:
            raise ProtocolError("invalid complete input frame") from exc


def _validate_ask(result: Mapping[str, Any]) -> None:
    health = result.get("numerical_health")
    required = {"radius", "robust_count", "operator_bound", "contraction"}
    if (type(result.get("response")) is not str or not result["response"]
            or not isinstance(health, Mapping) or not required.issubset(health)
            or result.get("provenance") is None or result.get("decoder") is None
            or result.get("grain_fibre") is None or result.get("costs") is None):
        raise TypedRefusal("incomplete-release-receipt",
                           "Ask requires health, provenance, decoder, grain/fibre, and costs")
    if result.get("simplex_covering") is not False:
        raise TypedRefusal("simplex-covering-face", "Ask face is not certified outside the simplex")
    try:
        _validate_exact_json(dict(result))
    except ProtocolError as exc:
        raise TypedRefusal("inexact-release-receipt", str(exc)) from exc


def initialize(store: AtomicFileCheckpoint, standing: BinaryIO, standing_length: int) -> FileCheckpoint:
    """Create the initial v2 file with empty cursor and protocol fields."""
    metadata = {"cursor": 0, "pending_comparisons": [], "input_tail_b64": "",
                "pending_output_b64": None, "pending_sequence": None}
    return store.write(metadata, standing, standing_length)
