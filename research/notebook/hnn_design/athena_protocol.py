"""Development-only exterior protocol for a future Athena release owner.

This module defines transport and durability only. Its fixture engine refuses every
Ask; it is not an Athena answer path and provides no F5 evidence.
"""
from __future__ import annotations

import base64
import json
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol

WIRE_VERSION = 1
COMMANDS = frozenset(("Ask", "Inspect", "Checkpoint"))


class ProtocolError(Exception):
    """Malformed frame, sequence violation, or unsupported wire version."""


class TypedRefusal(Exception):
    def __init__(self, code: str, detail: str):
        super().__init__(detail)
        self.code = code
        self.detail = detail


class Engine(Protocol):
    def ask(self, payload: Mapping[str, Any], standing: bytes) -> "EngineTransition": ...
    def inspect(self, payload: Mapping[str, Any], standing: bytes) -> "EngineTransition": ...


@dataclass(frozen=True)
class EngineTransition:
    """Pure candidate transition returned by native work.

    Durable replay prevents rerunning work after pending output is committed. A crash
    inside native work before that commit still needs a transactional engine integration.
    """
    result: Mapping[str, Any]
    standing: bytes
    pending_comparisons: tuple[Mapping[str, Any], ...] = ()


class RefusingFixtureEngine:
    """Safe fixture: no fabricated text, numerical health, or product capability."""

    def ask(self, payload: Mapping[str, Any], standing: bytes) -> EngineTransition:
        raise TypedRefusal("fixture-no-release-owner", "native text release is not integrated")

    def inspect(self, payload: Mapping[str, Any], standing: bytes) -> EngineTransition:
        return EngineTransition({"kind": "fixture-inspection", "standing_bytes": len(standing),
                                 "release_owner": "absent"}, standing)


def _json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


@dataclass
class Checkpoint:
    standing: bytes = b""
    cursor: int = 0
    pending_comparisons: list[Mapping[str, Any]] | None = None
    pending_output: bytes | None = None
    pending_sequence: int | None = None
    input_tail: bytes = b""

    def __post_init__(self) -> None:
        if self.pending_comparisons is None:
            self.pending_comparisons = []

    def encode(self) -> bytes:
        _validate_checkpoint(self)
        body = {
            "version": WIRE_VERSION,
            "standing": base64.b64encode(self.standing).decode("ascii"),
            "cursor": self.cursor,
            "pending_comparisons": self.pending_comparisons,
            "pending_output": (base64.b64encode(self.pending_output).decode("ascii")
                               if self.pending_output is not None else None),
            "pending_sequence": self.pending_sequence,
            "input_tail": base64.b64encode(self.input_tail).decode("ascii"),
        }
        return _json_bytes(body) + b"\n"

    @classmethod
    def decode(cls, raw: bytes) -> "Checkpoint":
        try:
            obj = json.loads(raw, parse_float=lambda _: (_ for _ in ()).throw(
                ProtocolError("checkpoint floats are forbidden")))
            expected = {"version", "standing", "cursor", "pending_comparisons",
                        "pending_output", "pending_sequence", "input_tail"}
            if not isinstance(obj, dict) or set(obj) != expected:
                raise ProtocolError("invalid checkpoint fields")
            if type(obj["version"]) is not int or obj["version"] != WIRE_VERSION:
                raise ProtocolError("unsupported checkpoint wire version")
            if type(obj["cursor"]) is not int or obj["cursor"] < 0:
                raise ProtocolError("checkpoint cursor must be a nonnegative integer")
            if not isinstance(obj["pending_comparisons"], list):
                raise ProtocolError("pending comparisons must be a list")
            _validate_exact_json(obj["pending_comparisons"])
            if obj["pending_sequence"] is not None and type(obj["pending_sequence"]) is not int:
                raise ProtocolError("pending sequence must be an integer or null")
            if (obj["pending_output"] is None) != (obj["pending_sequence"] is None):
                raise ProtocolError("pending output and sequence must be present together")
            return cls(base64.b64decode(obj["standing"], validate=True),
                       obj["cursor"], obj["pending_comparisons"],
                       base64.b64decode(obj["pending_output"], validate=True)
                       if obj["pending_output"] is not None else None,
                       obj["pending_sequence"],
                       base64.b64decode(obj["input_tail"], validate=True))
        except ProtocolError:
            raise
        except (KeyError, TypeError, ValueError, json.JSONDecodeError) as exc:
            raise ProtocolError("invalid checkpoint") from exc


class AtomicCheckpoint:
    """One owner-only file, replaced atomically; no sidecar or history is written."""

    def __init__(self, path: os.PathLike[str] | str):
        self.path = Path(path)
        self._secure_parent()

    def _secure_parent(self) -> None:
        self.path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        if hasattr(os, "getuid") and self.path.parent.stat().st_uid != os.getuid():
            raise ProtocolError("checkpoint parent must be owned by this user")
        os.chmod(self.path.parent, 0o700)
        if self.path.is_symlink():
            raise ProtocolError("checkpoint path may not be a symlink")

    def save(self, checkpoint: Checkpoint) -> bytes:
        raw = checkpoint.encode()
        self._secure_parent()
        fd, temp_name = tempfile.mkstemp(prefix=".checkpoint-", dir=self.path.parent)
        try:
            os.fchmod(fd, 0o600)
            with os.fdopen(fd, "wb") as stream:
                stream.write(raw)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temp_name, self.path)
            os.chmod(self.path, 0o600)
            dir_fd = os.open(self.path.parent, os.O_RDONLY)
            try:
                os.fsync(dir_fd)
            finally:
                os.close(dir_fd)
        finally:
            if os.path.exists(temp_name):
                os.unlink(temp_name)
        return raw

    def load(self) -> Checkpoint:
        self._secure_parent()
        if not self.path.exists():
            return Checkpoint()
        if self.path.is_symlink():
            raise ProtocolError("checkpoint path may not be a symlink")
        if self.path.stat().st_mode & 0o077:
            raise ProtocolError("checkpoint permissions must be owner-only")
        return Checkpoint.decode(self.path.read_bytes())


class Protocol:
    """One Ask/Inspect/Checkpoint vocabulary and one canonical receipt per command."""

    def __init__(self, checkpoint: AtomicCheckpoint, engine: Engine):
        self.store = checkpoint
        self.engine = engine
        self.state = checkpoint.load()

    def process(self, raw_frame: bytes) -> bytes:
        return self._process(raw_frame, consumed_tail=None)

    def _process(self, raw_frame: bytes, consumed_tail: bytes | None) -> bytes:
        frame = self._parse_frame(raw_frame)
        seq, command, payload = frame["sequence"], frame["command"], frame["payload"]
        if self.state.pending_output is not None:
            if seq == self.state.pending_sequence:
                return self.state.pending_output
            raise ProtocolError("pending output must be replayed before another frame")
        if seq != self.state.cursor + 1:
            raise ProtocolError("sequence must immediately follow acknowledged cursor")

        candidate = _clone_checkpoint(self.state)
        if consumed_tail is not None:
            candidate.input_tail = consumed_tail
        status = "ok"
        try:
            if command == "Ask":
                transition = self.engine.ask(payload, candidate.standing)
                _validate_ask_transition(transition)
            elif command == "Inspect":
                transition = self.engine.inspect(payload, candidate.standing)
            else:
                transition = EngineTransition(
                    {"cursor": candidate.cursor,
                     "standing_bytes": len(candidate.standing),
                     "pending_comparisons": len(candidate.pending_comparisons or [])},
                    candidate.standing, tuple(candidate.pending_comparisons or ()))
            result = dict(transition.result)
            candidate.standing = transition.standing
            candidate.pending_comparisons = list(transition.pending_comparisons)
        except TypedRefusal as refusal:
            status = "refused"
            result = {"type": refusal.code, "detail": refusal.detail}

        receipt = {"version": WIRE_VERSION, "sequence": seq, "command": command,
                   "status": status, "result": result}
        _validate_exact_json(receipt)
        output = _json_bytes(receipt) + b"\n"
        # The native call has returned. Cursor and exact replay bytes become durable together.
        candidate.cursor = seq
        candidate.pending_sequence = seq
        candidate.pending_output = output
        self.store.save(candidate)
        self.state = candidate
        return output

    def replay_pending(self) -> bytes | None:
        return self.state.pending_output

    def acknowledge_output(self, sequence: int) -> None:
        if self.state.pending_sequence != sequence or self.state.pending_output is None:
            raise ProtocolError("no matching pending output")
        candidate = _clone_checkpoint(self.state)
        candidate.pending_sequence = None
        candidate.pending_output = None
        self.store.save(candidate)
        self.state = candidate

    def feed(self, chunk: bytes) -> list[bytes]:
        """Durably stage input and commit at most one complete frame with its native result.

        A frame stays in the same checkpoint until the native transition and output commit.
        Further frames remain in the tail until the pending output is acknowledged. This makes
        restart before that commit retry the still-unacknowledged frame from identical standing.
        """
        if chunk:
            candidate = _clone_checkpoint(self.state)
            candidate.input_tail += chunk
            self.store.save(candidate)
            self.state = candidate
        if self.state.pending_output is not None:
            return []
        frame, separator, rest = self.state.input_tail.partition(b"\n")
        if not separator:
            return []
        if not frame:
            raise ProtocolError("empty input frame")
        return [self._process(frame, consumed_tail=rest)]

    @staticmethod
    def _parse_frame(raw: bytes) -> dict[str, Any]:
        try:
            frame = json.loads(raw)
            if type(frame.get("version")) is not int or frame["version"] != WIRE_VERSION:
                raise ProtocolError("unsupported input wire version")
            if set(frame) != {"version", "sequence", "command", "payload"}:
                raise ProtocolError("frame fields must be version, sequence, command, payload")
            if type(frame["sequence"]) is not int or frame["sequence"] < 1:
                raise ProtocolError("sequence must be a positive integer")
            if frame["command"] not in COMMANDS or not isinstance(frame["payload"], dict):
                raise ProtocolError("unknown command or non-object payload")
            _validate_exact_json(frame["payload"])
            return frame
        except ProtocolError:
            raise
        except (ValueError, AttributeError, TypeError) as exc:
            raise ProtocolError("invalid complete input frame") from exc


def render_human(output: bytes) -> str:
    """Render the same canonical receipt as a terse human view."""
    receipt = json.loads(output)
    return f"{receipt['command']} #{receipt['sequence']}: {receipt['status']} — " + \
        json.dumps(receipt["result"], ensure_ascii=False, sort_keys=True)


def render_json(output: bytes) -> str:
    """The JSON view is the canonical receipt without its JSONL line terminator."""
    return output.decode("utf-8").rstrip("\n")


def render_jsonl(output: bytes) -> bytes:
    """JSONL transports the canonical receipt unchanged."""
    return output


def _validate_exact_json(value: Any) -> None:
    if value is None or type(value) in (str, int, bool):
        return
    if isinstance(value, list):
        for item in value:
            _validate_exact_json(item)
        return
    if isinstance(value, dict):
        if not all(type(key) is str for key in value):
            raise ProtocolError("checkpoint object keys must be strings")
        for item in value.values():
            _validate_exact_json(item)
        return
    raise ProtocolError("checkpoint values must be exact JSON values; floats are forbidden")


def _validate_checkpoint(state: Checkpoint) -> None:
    if type(state.standing) is not bytes or type(state.input_tail) is not bytes:
        raise ProtocolError("standing and input tail must be opaque bytes")
    if type(state.cursor) is not int or state.cursor < 0:
        raise ProtocolError("checkpoint cursor must be a nonnegative integer")
    if state.pending_sequence is not None and type(state.pending_sequence) is not int:
        raise ProtocolError("pending sequence must be an integer or null")
    if state.pending_output is not None and type(state.pending_output) is not bytes:
        raise ProtocolError("pending output must be bytes or null")
    if (state.pending_output is None) != (state.pending_sequence is None):
        raise ProtocolError("pending output and sequence must be present together")
    if state.pending_sequence is not None and state.pending_sequence != state.cursor:
        raise ProtocolError("pending sequence must equal the advanced cursor")
    if not isinstance(state.pending_comparisons, list):
        raise ProtocolError("pending comparisons must be a list")
    _validate_exact_json(state.pending_comparisons)


def _clone_checkpoint(state: Checkpoint) -> Checkpoint:
    return Checkpoint.decode(state.encode())


def _validate_ask_transition(transition: EngineTransition) -> None:
    if not isinstance(transition, EngineTransition) or not isinstance(transition.result, Mapping):
        raise TypedRefusal("incomplete-release-receipt", "Ask did not return a typed release transition")
    result = transition.result
    health = result.get("numerical_health")
    required_health = {"radius", "robust_count", "operator_bound", "contraction"}
    if (type(result.get("response")) is not str or not result["response"]
            or not isinstance(health, Mapping) or not required_health.issubset(health)
            or result.get("provenance") is None or result.get("decoder") is None
            or result.get("grain_fibre") is None or result.get("costs") is None):
        raise TypedRefusal("incomplete-release-receipt",
                           "Ask requires numerical health, provenance, decoder, grain/fibre, and costs")
    if result.get("simplex_covering") is not False:
        raise TypedRefusal("simplex-covering-face", "Ask face is not certified outside the simplex")
    try:
        _validate_exact_json(dict(result))
        _validate_exact_json(dict(health))
    except ProtocolError as exc:
        raise TypedRefusal("inexact-release-receipt", str(exc)) from exc
