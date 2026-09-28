"""Streaming exterior checkpoint transport; this is not a native standing codec."""
from __future__ import annotations

import base64
import json
import os
import stat
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, BinaryIO, Callable, Mapping

MAGIC = b"ATHF5CP2"
VERSION = 2
_HEADER_SIZE = len(MAGIC) + 16
_COPY_SIZE = 1024 * 1024


class CheckpointError(ValueError):
    """Invalid, noncanonical, or unsupported file checkpoint."""


def _canonical_json(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def _exact_json(value: Any) -> None:
    if value is None or type(value) in (str, bool, int):
        return
    if isinstance(value, list):
        for item in value:
            _exact_json(item)
        return
    if isinstance(value, dict) and all(type(key) is str for key in value):
        for item in value.values():
            _exact_json(item)
        return
    raise CheckpointError("metadata must contain only exact JSON values")


def _metadata_bytes(metadata: Mapping[str, Any]) -> bytes:
    required = {"cursor", "pending_comparisons", "input_tail_b64",
                "pending_output_b64", "pending_sequence"}
    if not isinstance(metadata, Mapping) or set(metadata) != required:
        raise CheckpointError("metadata fields do not match checkpoint v2")
    obj = dict(metadata)
    if type(obj["cursor"]) is not int or obj["cursor"] < 0:
        raise CheckpointError("cursor must be a nonnegative integer")
    if type(obj["pending_comparisons"]) is not list:
        raise CheckpointError("pending comparisons must be a list")
    if type(obj["input_tail_b64"]) is not str:
        raise CheckpointError("input tail must be base64 text")
    if obj["pending_output_b64"] is not None and type(obj["pending_output_b64"]) is not str:
        raise CheckpointError("pending output must be base64 text or null")
    seq = obj["pending_sequence"]
    if seq is not None and (type(seq) is not int or seq < 0):
        raise CheckpointError("pending sequence must be a nonnegative integer or null")
    if (obj["pending_output_b64"] is None) != (seq is None):
        raise CheckpointError("pending output and sequence must be present together")
    if seq is not None and seq != obj["cursor"]:
        raise CheckpointError("pending sequence must equal the committed cursor")
    try:
        input_tail = base64.b64decode(obj["input_tail_b64"], validate=True)
        if base64.b64encode(input_tail).decode("ascii") != obj["input_tail_b64"]:
            raise CheckpointError("input tail base64 is not canonical")
        if obj["pending_output_b64"] is not None:
            output = base64.b64decode(obj["pending_output_b64"], validate=True)
            if base64.b64encode(output).decode("ascii") != obj["pending_output_b64"]:
                raise CheckpointError("pending output base64 is not canonical")
    except (ValueError, TypeError) as exc:
        raise CheckpointError("metadata contains invalid base64") from exc
    _exact_json(obj["pending_comparisons"])
    _exact_json(obj)
    return _canonical_json({"version": VERSION, **obj}) + b"\n"


def _reject_float(_: str) -> None:
    raise CheckpointError("metadata floats are forbidden")


def _reject_constant(_: str) -> None:
    raise CheckpointError("non-finite metadata number")


@dataclass(frozen=True)
class FileCheckpoint:
    path: Path
    metadata: dict[str, Any]
    standing_offset: int
    standing_length: int
    device: int
    inode: int
    file_size: int

    def open_standing(self) -> BinaryIO:
        """Open a bounded reader over the standing region without loading it."""
        flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
        try:
            fd = os.open(self.path, flags)
        except OSError as exc:
            raise CheckpointError("checkpoint path changed or is a symlink") from exc
        info = os.fstat(fd)
        if (info.st_dev, info.st_ino, info.st_size) != (self.device, self.inode, self.file_size):
            os.close(fd)
            raise CheckpointError("checkpoint changed after metadata was read")
        stream = os.fdopen(fd, "rb")
        stream.seek(self.standing_offset)
        return _LimitedReader(stream, self.standing_length)


class _LimitedReader:
    def __init__(self, stream: BinaryIO, remaining: int):
        self._stream, self._remaining = stream, remaining

    def read(self, size: int = -1) -> bytes:
        if size == 0 or self._remaining == 0:
            return b""
        if size < 0 or size > _COPY_SIZE:
            size = _COPY_SIZE
        size = min(size, self._remaining)
        data = self._stream.read(size)
        if not data:
            raise CheckpointError("standing region truncated")
        self._remaining -= len(data)
        return data

    def close(self) -> None:
        self._stream.close()

    def __enter__(self) -> "_LimitedReader":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


class AtomicFileCheckpoint:
    """One owner-only binary file with streamed raw standing and atomic replacement."""

    def __init__(self, path: os.PathLike[str] | str):
        self.path = Path(path)
        self._secure_parent()

    def _secure_parent(self) -> None:
        self.path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        parent = self.path.parent.stat()
        if hasattr(os, "getuid") and parent.st_uid != os.getuid():
            raise CheckpointError("checkpoint parent must be owned by this user")
        os.chmod(self.path.parent, 0o700)
        if self.path.is_symlink():
            raise CheckpointError("checkpoint path may not be a symlink")

    def write(self, metadata: Mapping[str, Any], standing: BinaryIO,
              standing_length: int) -> FileCheckpoint:
        """Stream exactly `standing_length` bytes from a reader into one atomic file."""
        def copy_region(out: BinaryIO) -> None:
            remaining = standing_length
            while remaining:
                chunk = standing.read(min(_COPY_SIZE, remaining))
                if not chunk:
                    raise CheckpointError("standing source ended before declared length")
                if not isinstance(chunk, (bytes, bytearray, memoryview)):
                    raise CheckpointError("standing source must yield bytes")
                chunk = bytes(chunk)
                if len(chunk) > remaining:
                    raise CheckpointError("standing source exceeded requested read size")
                out.write(chunk)
                remaining -= len(chunk)
            if standing.read(1):
                raise CheckpointError("standing source exceeds declared length")

        return self.write_generated(metadata, standing_length, copy_region)

    def write_generated(self, metadata: Mapping[str, Any], standing_length: int | None,
                        emit_standing: Callable[[BinaryIO], None]) -> FileCheckpoint:
        """Atomically commit metadata and a standing region emitted directly to the temp file.

        `emit_standing` writes raw bytes. If length is supplied it must match; with `None`,
        the emitted length is measured and patched into the header before fsync. Exceptions
        leave the previous checkpoint intact; the candidate temp file is removed.
        """
        if standing_length is not None and (type(standing_length) is not int or standing_length < 0):
            raise CheckpointError("standing length must be a nonnegative integer")
        meta = _metadata_bytes(metadata)
        if len(meta) >= 1 << 64 or (standing_length is not None and standing_length >= 1 << 64):
            raise CheckpointError("checkpoint region exceeds format length")
        self._secure_parent()
        fd, temp_name = tempfile.mkstemp(prefix=".athena-checkpoint-", dir=self.path.parent)
        try:
            os.fchmod(fd, 0o600)
            with os.fdopen(fd, "wb") as out:
                out.write(MAGIC)
                out.write(len(meta).to_bytes(8, "big"))
                length_offset = out.tell()
                out.write((standing_length or 0).to_bytes(8, "big"))
                out.write(meta)
                start = out.tell()
                emit_standing(out)
                actual_length = out.tell() - start
                if standing_length is not None and actual_length != standing_length:
                    raise CheckpointError("standing writer emitted a different length")
                if actual_length >= 1 << 64:
                    raise CheckpointError("checkpoint standing exceeds format length")
                if standing_length is None:
                    out.seek(length_offset)
                    out.write(actual_length.to_bytes(8, "big"))
                    out.seek(0, os.SEEK_END)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp_name, self.path)
            dir_fd = os.open(self.path.parent, os.O_RDONLY)
            try:
                os.fsync(dir_fd)
            finally:
                os.close(dir_fd)
        finally:
            if os.path.exists(temp_name):
                os.unlink(temp_name)
        return self.read()

    def read(self) -> FileCheckpoint:
        self._secure_parent()
        if not self.path.exists():
            raise FileNotFoundError(self.path)
        flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
        try:
            fd = os.open(self.path, flags)
        except OSError as exc:
            raise CheckpointError("checkpoint path may not be a symlink") from exc
        with os.fdopen(fd, "rb") as stream:
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode) or info.st_mode & 0o077:
                raise CheckpointError("checkpoint must be an owner-only regular file")
            header = stream.read(_HEADER_SIZE)
            if len(header) != _HEADER_SIZE or header[:len(MAGIC)] != MAGIC:
                raise CheckpointError("invalid checkpoint header")
            meta_len = int.from_bytes(header[len(MAGIC):len(MAGIC) + 8], "big")
            standing_len = int.from_bytes(header[len(MAGIC) + 8:], "big")
            offset = _HEADER_SIZE + meta_len
            if offset + standing_len != info.st_size:
                raise CheckpointError("checkpoint length mismatch or trailing bytes")
            raw = stream.read(meta_len)
        try:
            parsed = json.loads(raw.decode("utf-8"), parse_float=_reject_float,
                                parse_constant=_reject_constant)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise CheckpointError("invalid checkpoint metadata") from exc
        if not isinstance(parsed, dict) or parsed.get("version") != VERSION or type(parsed.get("version")) is not int:
            raise CheckpointError("unsupported checkpoint version")
        metadata = {key: value for key, value in parsed.items() if key != "version"}
        if _metadata_bytes(metadata) + b"" != raw:
            raise CheckpointError("noncanonical checkpoint metadata")
        return FileCheckpoint(self.path, metadata, offset, standing_len,
                              info.st_dev, info.st_ino, info.st_size)
