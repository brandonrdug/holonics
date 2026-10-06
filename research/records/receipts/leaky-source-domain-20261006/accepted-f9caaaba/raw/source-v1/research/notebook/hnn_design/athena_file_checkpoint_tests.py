"""Fixture tests for the exterior streaming checkpoint transport."""
import io
import json
import os
import tempfile
import unittest
from pathlib import Path

from athena_file_checkpoint import (AtomicFileCheckpoint, CheckpointError, MAGIC,
                                   VERSION)


def metadata(cursor=0, output=None, sequence=None):
    return {"cursor": cursor, "pending_comparisons": [{"ratio": "1/2"}],
            "input_tail_b64": "", "pending_output_b64": output,
            "pending_sequence": sequence}


class FailingReader:
    def __init__(self, prefix):
        self.prefix = io.BytesIO(prefix)
        self.first = True

    def read(self, size=-1):
        if self.first:
            self.first = False
            return self.prefix.read(size)
        raise OSError("fixture interrupted standing stream")


class FileCheckpointTests(unittest.TestCase):
    def test_whole_and_chunked_standing_writes_are_byte_identical(self):
        standing = bytes(range(251)) * 41
        with tempfile.TemporaryDirectory() as directory:
            whole = AtomicFileCheckpoint(Path(directory) / "whole")
            split = AtomicFileCheckpoint(Path(directory) / "split")
            whole.write(metadata(), io.BytesIO(standing), len(standing))

            class Chunks:
                def __init__(self, raw):
                    self.raw = io.BytesIO(raw)
                    self.turn = 0

                def read(self, size=-1):
                    self.turn += 1
                    return self.raw.read(min(size, 37 + self.turn % 113))

            split.write(metadata(), Chunks(standing), len(standing))
            self.assertEqual(whole.path.read_bytes(), split.path.read_bytes())

    def test_interrupted_stream_preserves_old_checkpoint(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            store.write(metadata(1), io.BytesIO(b"old standing"), 12)
            old = store.path.read_bytes()
            with self.assertRaises(OSError):
                store.write(metadata(2), FailingReader(b"partial"), 30)
            self.assertEqual(old, store.path.read_bytes())
            self.assertEqual([], list(Path(directory).glob(".athena-checkpoint-*")))

    def test_metadata_and_pending_delivery_commit_with_standing(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            output = "eyJzZXF1ZW5jZSI6N30="
            saved = store.write(metadata(7, output, 7), io.BytesIO(b"native"), 6)
            loaded = store.read()
            self.assertEqual(VERSION, 2)
            self.assertEqual(7, loaded.metadata["cursor"])
            self.assertEqual(output, loaded.metadata["pending_output_b64"])
            self.assertEqual(saved.standing_offset, loaded.standing_offset)
            with loaded.open_standing() as region:
                self.assertEqual(b"native", region.read())

    def test_native_writer_callback_targets_the_candidate_file(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            observed = []

            def emit(out):
                observed.append(os.fstat(out.fileno()).st_ino)
                out.write(b"joined-native-standing")

            saved = store.write_generated(metadata(4), len(b"joined-native-standing"), emit)
            self.assertEqual(observed[0], store.path.stat().st_ino)
            with saved.open_standing() as region:
                self.assertEqual(b"joined-native-standing", region.read())

    def test_writer_can_measure_standing_length_without_a_second_encode(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            saved = store.write_generated(metadata(), None,
                                          lambda out: (out.write(b"first"), out.write(b"second")))
            self.assertEqual(11, saved.standing_length)
            with saved.open_standing() as region:
                self.assertEqual(b"firstsecond", region.read())

    def test_default_region_read_is_bounded(self):
        standing = b"s" * (2 * 1024 * 1024 + 7)
        with tempfile.TemporaryDirectory() as directory:
            saved = AtomicFileCheckpoint(Path(directory) / "state").write(
                metadata(), io.BytesIO(standing), len(standing))
            with saved.open_standing() as region:
                self.assertEqual(1024 * 1024, len(region.read()))

    def test_replacement_after_metadata_read_refuses_old_region_handle(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            old = store.write(metadata(), io.BytesIO(b"same"), 4)
            store.write(metadata(), io.BytesIO(b"new!"), 4)
            with self.assertRaises(CheckpointError):
                old.open_standing()

    def test_pending_sequence_and_base64_must_be_canonical(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            with self.assertRaises(CheckpointError):
                store.write(metadata(3, "YQ==", 2), io.BytesIO(b""), 0)
            with self.assertRaises(CheckpointError):
                store.write(metadata(3, "YR==", 3), io.BytesIO(b""), 0)

    def test_no_history_or_duplicate_archive_is_written(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state"
            AtomicFileCheckpoint(path).write(metadata(), io.BytesIO(b"x"), 1)
            self.assertEqual(["state"], sorted(item.name for item in path.parent.iterdir()))

    def test_malformed_version_trailing_and_noncanonical_metadata_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            store = AtomicFileCheckpoint(Path(directory) / "state")
            store.write(metadata(), io.BytesIO(b"x"), 1)
            valid = store.path.read_bytes()
            store.path.write_bytes(valid + b"x")
            with self.assertRaises(CheckpointError):
                store.read()
            store.path.write_bytes(valid.replace(b'"version":2', b'"version":3'))
            with self.assertRaises(CheckpointError):
                store.read()
            store.path.write_bytes(valid.replace(b'"cursor":0', b'"cursor": 0'))
            with self.assertRaises(CheckpointError):
                store.read()

    def test_owner_only_permissions_and_binary_header(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state"
            store = AtomicFileCheckpoint(path)
            store.write(metadata(), io.BytesIO(b"xy"), 2)
            raw = path.read_bytes()
            self.assertEqual(MAGIC, raw[:len(MAGIC)])
            self.assertEqual(0o600, path.stat().st_mode & 0o777)
            self.assertEqual(0o700, path.parent.stat().st_mode & 0o777)


if __name__ == "__main__":
    unittest.main()
