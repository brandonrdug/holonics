"""Selectively acquire the SoundCam treated-room raw music/loopback pair.

This is an exterior codec and provenance operation.  It range-reads only the two
requested NPY members from the small Stanford ZIP sample; it does not acquire the
digital music source, deconvolved RIRs, adjusted recordings, or any room/person
labels.  The electrical loopback is retained as the measured excitation witness.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import struct
import time
import urllib.request
import urllib.error
import wave
import zipfile
import zlib

import numpy as np


ARCHIVE_URL = "https://downloads.cs.stanford.edu/viscam/SoundCam/TreatedRoomSmallSet.zip"
EXPECTED_ARCHIVE_SIZE = 659_806_886
EXPECTED_ARCHIVE_ETAG = '"6700980d-2753daa6"'
TAIL_BYTES = 1 << 20
MAX_ENTRY_COMPRESSED = 64 << 20
MAX_ENTRY_UNCOMPRESSED = 64 << 20
MAX_EXPANSION_RATIO = 100
SAMPLE_RATE = 48_000
FRAME_COUNT = 672_000
ROW_COUNT = 3
MICROPHONE_COUNT = 10
ROOT_MEMBER = "TreatedRoomSmallSet/Human1"
AUDIO_MEMBER = f"{ROOT_MEMBER}/music_audio.npy"
LOOPBACK_MEMBER = f"{ROOT_MEMBER}/music_directlines.npy"
SOURCE_MEMBER = f"{ROOT_MEMBER}/music_sources.npy"
EMPTY_SOURCE_MEMBER = "TreatedRoomSmallSet/Empty/music_sources.npy"

EXPECTED_ENTRIES = {
    AUDIO_MEMBER: {"size": 40_320_128, "crc": 0x74320442},
    LOOPBACK_MEMBER: {"size": 4_032_128, "crc": 0x52BF1D9C},
    SOURCE_MEMBER: {"size": 16_128_128, "crc": 0x6C3D954C},
    EMPTY_SOURCE_MEMBER: {"size": 16_128_128, "crc": 0x6C3D954C},
}


class AcquisitionError(RuntimeError):
    pass


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def safe_member(name: str) -> None:
    path = PurePosixPath(name)
    if "\\" in name or path.is_absolute() or any(part == ".." for part in path.parts):
        raise AcquisitionError(f"unsafe ZIP member path: {name!r}")


class RangeFetcher:
    def __init__(self, url: str) -> None:
        self.url = url
        self.ranges: list[dict[str, object]] = []
        request = urllib.request.Request(url, method="HEAD")
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                headers = response.headers
                self.size = int(headers.get("Content-Length", "0"))
                self.etag = headers.get("ETag")
                self.last_modified = headers.get("Last-Modified")
                self.accept_ranges = headers.get("Accept-Ranges")
        except Exception as error:  # pragma: no cover - network failure is environment-specific
            raise AcquisitionError(f"SoundCam archive HEAD failed: {error}") from error
        if self.size != EXPECTED_ARCHIVE_SIZE:
            raise AcquisitionError(
                f"archive size changed: expected {EXPECTED_ARCHIVE_SIZE}, got {self.size}"
            )
        if self.etag != EXPECTED_ARCHIVE_ETAG:
            raise AcquisitionError(
                f"archive ETag changed: expected {EXPECTED_ARCHIVE_ETAG}, got {self.etag!r}"
            )
        if self.accept_ranges != "bytes":
            raise AcquisitionError(f"archive does not advertise byte ranges: {self.accept_ranges!r}")

    def get_range(self, start: int, end: int, purpose: str) -> bytes:
        if start < 0 or end < start or end >= self.size:
            raise AcquisitionError(f"invalid archive range {start}-{end} for {purpose}")
        request = urllib.request.Request(
            self.url,
            headers={"Range": f"bytes={start}-{end}", "Accept-Encoding": "identity"},
        )
        for attempt in range(3):
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    status = getattr(response, "status", None)
                    etag = response.headers.get("ETag")
                    content_range = response.headers.get("Content-Range", "")
                    match = re.fullmatch(r"bytes (\d+)-(\d+)/(\d+)", content_range)
                    if status != 206 or match is None:
                        raise AcquisitionError(
                            f"range response was not 206 for {purpose}: {status}, {content_range!r}"
                        )
                    response_start, response_end, response_size = map(int, match.groups())
                    if (response_start, response_end, response_size) != (start, end, self.size):
                        raise AcquisitionError(
                            f"archive range mismatch for {purpose}: {content_range!r}"
                        )
                    if etag != self.etag:
                        raise AcquisitionError(f"archive ETag changed during {purpose}: {etag!r}")
                    expected_bytes = end - start + 1
                    body = response.read(expected_bytes + 1)
                    if len(body) != expected_bytes:
                        raise AcquisitionError(
                            f"short or oversized archive range for {purpose}: {len(body)} bytes"
                        )
                break
            except urllib.error.HTTPError as error:
                if error.code not in (429, 503) or attempt == 2:
                    raise AcquisitionError(f"archive range failed for {purpose}: {error}") from error
                time.sleep(2**attempt)
            except Exception as error:  # pragma: no cover - network failure is environment-specific
                raise AcquisitionError(f"archive range failed for {purpose}: {error}") from error
        self.ranges.append(
            {"purpose": purpose, "start": start, "end": end, "bytes": len(body), "etag": etag}
        )
        return body


def inspect_entries(tail: bytes, tail_start: int) -> dict[str, zipfile.ZipInfo]:
    try:
        with zipfile.ZipFile(io.BytesIO(tail)) as archive:
            infos = archive.infolist()
    except Exception as error:
        raise AcquisitionError(f"SoundCam ZIP central directory refused: {error}") from error
    for info in infos:
        safe_member(info.filename)
    by_name = {info.filename: info for info in infos}
    for name, expected in EXPECTED_ENTRIES.items():
        info = by_name.get(name)
        if info is None or info.is_dir():
            raise AcquisitionError(f"required ZIP member absent: {name}")
        if info.file_size != expected["size"] or info.CRC != expected["crc"]:
            raise AcquisitionError(
                f"ZIP member changed: {name} size={info.file_size} crc={info.CRC:08x}"
            )
        if info.compress_type != zipfile.ZIP_DEFLATED or info.flag_bits & 0x1:
            raise AcquisitionError(f"unsupported ZIP member encoding: {name}")
        if info.compress_size > MAX_ENTRY_COMPRESSED or info.file_size > MAX_ENTRY_UNCOMPRESSED:
            raise AcquisitionError(f"ZIP member exceeds bounded extraction size: {name}")
        if info.compress_size == 0 or info.file_size > info.compress_size * MAX_EXPANSION_RATIO:
            raise AcquisitionError(f"ZIP member expansion bound refused: {name}")
        actual_offset = tail_start + info.header_offset
        if actual_offset < 0 or actual_offset >= EXPECTED_ARCHIVE_SIZE:
            raise AcquisitionError(f"invalid ZIP member offset: {name}")
    return by_name


def extract_member(
    fetcher: RangeFetcher, info: zipfile.ZipInfo, name: str, tail_start: int
) -> bytes:
    actual_offset = tail_start + info.header_offset
    header = fetcher.get_range(actual_offset, min(actual_offset + 4095, fetcher.size - 1), f"{name} local header")
    if len(header) < 30:
        raise AcquisitionError(f"short local ZIP header: {name}")
    signature, _version, flags, method, _time, _date, _crc, _compressed, _uncompressed, filename_len, extra_len = struct.unpack(
        "<4s5H3L2H", header[:30]
    )
    if signature != b"PK\x03\x04" or method != zipfile.ZIP_DEFLATED or flags & 0x1:
        raise AcquisitionError(f"local ZIP header refused: {name}")
    data_start = actual_offset + 30 + filename_len + extra_len
    header_end = data_start - 1
    if header_end >= actual_offset + len(header):
        raise AcquisitionError(f"local ZIP header exceeds bounded read: {name}")
    local_name = header[30 : 30 + filename_len].decode("utf-8")
    if local_name != name:
        raise AcquisitionError(f"local ZIP member name mismatch: {local_name!r}")
    data_end = data_start + info.compress_size - 1
    compressed = fetcher.get_range(data_start, data_end, f"{name} compressed payload")
    try:
        decompressor = zlib.decompressobj(-15)
        payload = decompressor.decompress(compressed, info.file_size + 1)
        if len(payload) > info.file_size or decompressor.unconsumed_tail:
            raise AcquisitionError(f"ZIP member exceeds bounded output size: {name}")
        payload += decompressor.flush(info.file_size + 1 - len(payload))
    except zlib.error as error:
        raise AcquisitionError(f"ZIP deflate refused for {name}: {error}") from error
    if (
        len(payload) != info.file_size
        or not decompressor.eof
        or decompressor.unused_data
        or decompressor.unconsumed_tail
        or zlib.crc32(payload) & 0xFFFFFFFF != info.CRC
    ):
        raise AcquisitionError(f"ZIP member integrity mismatch after extraction: {name}")
    return payload


def load_pcm16(payload: bytes, name: str, shape: tuple[int, ...]) -> np.ndarray:
    try:
        value = np.load(io.BytesIO(payload), allow_pickle=False)
    except Exception as error:
        raise AcquisitionError(f"NPY refused for {name}: {error}") from error
    if not isinstance(value, np.ndarray) or value.dtype.str != "<i2" or value.shape != shape:
        raise AcquisitionError(
            f"unexpected NPY schema for {name}: dtype={getattr(value, 'dtype', None)!r}, "
            f"shape={getattr(value, 'shape', None)!r}"
        )
    if not value.flags.c_contiguous:
        raise AcquisitionError(f"non-contiguous NPY array: {name}")
    return value


def exact_write(path: Path, payload: bytes) -> None:
    if path.exists():
        if path.is_symlink() or not path.is_file() or path.read_bytes() != payload:
            raise AcquisitionError(f"pre-existing incompatible output: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("xb") as output:
            output.write(payload)
    except FileExistsError as error:
        raise AcquisitionError(f"output appeared during acquisition: {path}") from error


def wav_bytes(samples: np.ndarray) -> bytes:
    if samples.dtype.str != "<i2" or samples.ndim != 1 or samples.shape[0] != FRAME_COUNT:
        raise AcquisitionError("invalid PCM16 row for WAV export")
    output = io.BytesIO()
    with wave.open(output, "wb") as writer:
        writer.setnchannels(1)
        writer.setsampwidth(2)
        writer.setframerate(SAMPLE_RATE)
        writer.writeframes(samples.tobytes(order="C"))
    encoded = output.getvalue()
    with wave.open(io.BytesIO(encoded), "rb") as reader:
        if (reader.getnchannels(), reader.getsampwidth(), reader.getframerate(), reader.getnframes()) != (
            1,
            2,
            SAMPLE_RATE,
            FRAME_COUNT,
        ):
            raise AcquisitionError("WAV round-trip chart mismatch")
    return encoded


def output_root(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    if path.is_symlink() or not path.is_dir():
        raise AcquisitionError(f"unsafe output root: {path}")
    return path.resolve()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(".local/datasets/soundcam"))
    args = parser.parse_args()
    root = output_root(args.output)
    fetcher = RangeFetcher(ARCHIVE_URL)
    tail_start = max(0, fetcher.size - TAIL_BYTES)
    tail = fetcher.get_range(tail_start, fetcher.size - 1, "ZIP central directory")
    infos = inspect_entries(tail, tail_start)

    audio_payload = extract_member(fetcher, infos[AUDIO_MEMBER], AUDIO_MEMBER, tail_start)
    loopback_payload = extract_member(fetcher, infos[LOOPBACK_MEMBER], LOOPBACK_MEMBER, tail_start)
    audio = load_pcm16(audio_payload, AUDIO_MEMBER, (ROW_COUNT, MICROPHONE_COUNT, FRAME_COUNT))
    loopback = load_pcm16(loopback_payload, LOOPBACK_MEMBER, (ROW_COUNT, FRAME_COUNT))

    raw_audio_path = root / "raw" / "TreatedRoomSmallSet" / "Human1" / "music_audio.npy"
    raw_loopback_path = root / "raw" / "TreatedRoomSmallSet" / "Human1" / "music_directlines.npy"
    outputs: list[dict[str, object]] = []
    pairs: list[dict[str, object]] = []
    audio_sha256 = sha256_bytes(audio_payload)
    loopback_sha256 = sha256_bytes(loopback_payload)
    exact_write(raw_audio_path, audio_payload)
    exact_write(raw_loopback_path, loopback_payload)

    for row in range(ROW_COUNT):
        loopback_wav = wav_bytes(loopback[row])
        loopback_path = root / "wav" / f"row_{row:03d}" / "loopback.wav"
        exact_write(loopback_path, loopback_wav)
        outputs.append(
            {
                "path": str(loopback_path.relative_to(root)),
                "array": "music_directlines.npy",
                "row": row,
                "channel": "loopback",
                "sample_rate_hz": SAMPLE_RATE,
                "frame_count": FRAME_COUNT,
                "origin_frame": 0,
                "pcm16_sha256": sha256_bytes(loopback[row].tobytes(order="C")),
                "wav_sha256": sha256_bytes(loopback_wav),
                "wav_bytes": len(loopback_wav),
            }
        )
        for channel in range(MICROPHONE_COUNT):
            microphone_wav = wav_bytes(audio[row, channel])
            microphone_path = root / "wav" / f"row_{row:03d}" / f"microphone_{channel:02d}.wav"
            exact_write(microphone_path, microphone_wav)
            outputs.append(
                {
                    "path": str(microphone_path.relative_to(root)),
                    "array": "music_audio.npy",
                    "row": row,
                    "channel": channel,
                    "sample_rate_hz": SAMPLE_RATE,
                    "frame_count": FRAME_COUNT,
                    "origin_frame": 0,
                    "pcm16_sha256": sha256_bytes(audio[row, channel].tobytes(order="C")),
                    "wav_sha256": sha256_bytes(microphone_wav),
                    "wav_bytes": len(microphone_wav),
                }
            )
            pairs.append(
                {
                    "row": row,
                    "microphone": channel,
                    "sample_rate_hz": SAMPLE_RATE,
                    "origin_frame": 0,
                    "loopback": {
                        "path": str(loopback_path.relative_to(root)),
                        "wav_sha256": sha256_bytes(loopback_wav),
                        "frames": FRAME_COUNT,
                        "source_array": "music_directlines.npy",
                        "source_array_sha256": loopback_sha256,
                        "selector": {"row": row, "channel": "loopback"},
                    },
                    "microphone_recording": {
                        "path": str(microphone_path.relative_to(root)),
                        "wav_sha256": sha256_bytes(microphone_wav),
                        "frames": FRAME_COUNT,
                        "source_array": "music_audio.npy",
                        "source_array_sha256": audio_sha256,
                        "selector": {"row": row, "channel": channel},
                    },
                }
            )

    receipt = {
        "schema": "soundcam-selective-acquisition.v1",
        "dataset": "SoundCam",
        "project_url": "https://masonlwang.com/soundcam/",
        "dataset_url": "https://purl.stanford.edu/xq364hd5023",
        "doi": "https://doi.org/10.25740/xq364hd5023",
        "paper_url": "https://arxiv.org/pdf/2311.03517.pdf",
        "license": {
            "name": "MIT",
            "url": "https://opensource.org/license/mit/",
            "basis": "SoundCam datasheet and Stanford repository metadata",
        },
        "archive": {
            "url": ARCHIVE_URL,
            "etag": fetcher.etag,
            "last_modified": fetcher.last_modified,
            "size_bytes": fetcher.size,
            "selected_ranges": fetcher.ranges,
            "downloaded_archive": False,
        },
        "collection_clock": {
            "sample_rate_hz": SAMPLE_RATE,
            "frame_count": FRAME_COUNT,
            "origin_frame": 0,
            "origin_seconds": "0",
            "citation": "SoundCam paper Appendix D.3: synchronized MOTU 8M interfaces at 48 kHz",
        },
        "selectors": {
            "folder": ROOT_MEMBER,
            "rows": list(range(ROW_COUNT)),
            "microphone_channels": list(range(MICROPHONE_COUNT)),
            "loopback_channel": "music_directlines.npy",
        },
        "entries": {
            "music_audio.npy": {
                "archive_member": AUDIO_MEMBER,
                "zip_crc32": f"{infos[AUDIO_MEMBER].CRC:08x}",
                "compressed_bytes": infos[AUDIO_MEMBER].compress_size,
                "uncompressed_bytes": len(audio_payload),
                "sha256": sha256_bytes(audio_payload),
                "dtype": "<i2",
                "shape": list(audio.shape),
            },
            "music_directlines.npy": {
                "archive_member": LOOPBACK_MEMBER,
                "zip_crc32": f"{infos[LOOPBACK_MEMBER].CRC:08x}",
                "compressed_bytes": infos[LOOPBACK_MEMBER].compress_size,
                "uncompressed_bytes": len(loopback_payload),
                "sha256": sha256_bytes(loopback_payload),
                "dtype": "<i2",
                "shape": list(loopback.shape),
            },
            "music_sources.npy": {
                "archive_member": SOURCE_MEMBER,
                "downloaded": False,
                "zip_crc32": f"{infos[SOURCE_MEMBER].CRC:08x}",
                "uncompressed_bytes": infos[SOURCE_MEMBER].file_size,
                "sha256": None,
                "sha256_available": False,
                "sha256_reason": "member intentionally not acquired",
                "dtype": "<f8",
                "shape": [ROW_COUNT, FRAME_COUNT],
                "used_as_native_input": False,
                "reason": "float64 digital source intentionally not acquired; electrical loopback is the measured excitation witness",
            },
            "empty_music_sources_provenance": {
                "archive_member": EMPTY_SOURCE_MEMBER,
                "downloaded": False,
                "zip_crc32": f"{infos[EMPTY_SOURCE_MEMBER].CRC:08x}",
                "same_crc_as_human1_source": infos[EMPTY_SOURCE_MEMBER].CRC == infos[SOURCE_MEMBER].CRC,
            },
        },
        "not_acquired": [
            "music_sources.npy",
            "music_deconvolved.npy",
            "adjusted_music.npy",
            "all other archive members",
        ],
        "raw_outputs": {
            "music_audio_npy": str(raw_audio_path.relative_to(root)),
            "music_directlines_npy": str(raw_loopback_path.relative_to(root)),
        },
        "wav_outputs": outputs,
        "pairs": pairs,
        "semantic_conditions": False,
        "native_current_formation": False,
    }
    receipt_bytes = (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode()
    exact_write(root / "acquisition.json", receipt_bytes)
    print(json.dumps({"output": str(root), "wav_count": len(outputs), "acquisition_sha256": sha256_bytes(receipt_bytes)}, indent=2))


if __name__ == "__main__":
    main()
