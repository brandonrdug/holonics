"""Synthetic fixtures for the bounded, file-backed protocol transition."""
import io
import json
import os
import tempfile
import unittest
from pathlib import Path

from athena_file_checkpoint import AtomicFileCheckpoint
from athena_file_protocol import (FileProtocol, FileTransition, initialize)
from athena_protocol import ProtocolError


def frame(sequence=1, command="Inspect", payload=None):
    return json.dumps({"version": 1, "sequence": sequence, "command": command,
                       "payload": payload or {}}, sort_keys=True,
                       separators=(",", ":")).encode()


class Engine:
    def __init__(self, *, ask_result=None, fail_writer=False):
        self.calls = 0
        self.ask_result = ask_result or {"kind": "candidate"}
        self.fail_writer = fail_writer

    def inspect(self, payload, standing):
        self.calls += 1
        prefix = standing.read(3)
        return FileTransition({"kind": "inspection", "prefix": prefix.hex()},
                              ({"comparison": "pending-1"},),
                              self._writer(b"new synthetic standing"))

    def ask(self, payload, standing):
        self.calls += 1
        standing.read(1)
        return FileTransition(self.ask_result, (), self._writer(b"must not commit"))

    def _writer(self, raw):
        def emit(out):
            if self.fail_writer:
                out.write(raw[:5])
                raise OSError("synthetic interruption before atomic replace")
            out.write(raw)
        return emit


class FileProtocolTests(unittest.TestCase):
    def make(self, directory, engine, initial=b"old synthetic standing"):
        store = AtomicFileCheckpoint(Path(directory) / "checkpoint.bin")
        initialize(store, io.BytesIO(initial), len(initial))
        return store, FileProtocol(store, engine)

    def test_transition_and_pending_replay_survive_restart_without_engine_call(self):
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine()
            store, protocol = self.make(directory, engine)
            output = protocol.process(frame())
            self.assertEqual(1, engine.calls)
            before = store.read()
            self.assertEqual(1, before.metadata["cursor"])
            self.assertEqual([{"comparison": "pending-1"}], before.metadata["pending_comparisons"])
            with before.open_standing() as region:
                self.assertEqual(b"new synthetic standing", region.read())

            restarted = FileProtocol(store, engine)
            replay = restarted.process(frame())
            self.assertEqual(output, replay)
            self.assertEqual(1, engine.calls)
            after = store.read()
            self.assertEqual(before.metadata, after.metadata)
            with after.open_standing() as region:
                self.assertEqual(b"new synthetic standing", region.read())

    def test_interrupted_candidate_writer_retains_staged_frame_and_retries_after_restart(self):
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine(fail_writer=True)
            store, protocol = self.make(directory, engine)
            with self.assertRaises(OSError):
                protocol.feed(frame() + b"\n")
            self.assertEqual(0, store.read().metadata["cursor"])
            self.assertEqual(frame() + b"\n", __import__("base64").b64decode(
                store.read().metadata["input_tail_b64"]))
            engine.fail_writer = False
            restarted = FileProtocol(store, engine)
            result = restarted.feed(b"")
            self.assertEqual(1, len(result))
            self.assertEqual(2, engine.calls)
            self.assertEqual(1, store.read().metadata["cursor"])
            self.assertEqual([], list(Path(directory).glob(".athena-checkpoint-*")))

    def test_ask_without_complete_health_provenance_fibre_decoder_and_cost_refuses(self):
        incomplete = {"text": "synthetic candidate", "numerical_health": {"radius": "0"},
                      "provenance": None, "decoder": None, "grain_fibre": None,
                      "costs": None, "simplex_covering": False}
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine(ask_result=incomplete)
            store, protocol = self.make(directory, engine)
            output = protocol.process(frame(command="Ask"))
            receipt = json.loads(output)
            self.assertEqual("refused", receipt["status"])
            self.assertEqual("incomplete-release-receipt", receipt["result"]["type"])
            with store.read().open_standing() as region:
                self.assertEqual(b"old synthetic standing", region.read())

    def test_complete_ask_is_accepted_only_with_full_exact_receipt(self):
        result = {"numerical_health": {"radius": "0", "robust_count": 1,
                                        "operator_bound": "1", "contraction": "0"},
                  "provenance": {"source": "fixture"}, "decoder": {"kind": "utf8"},
                  "grain_fibre": {"kind": "singleton"}, "costs": {"bits": 1},
                  "simplex_covering": False, "response": "synthetic"}
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine(ask_result=result)
            store, protocol = self.make(directory, engine)
            receipt = json.loads(protocol.process(frame(command="Ask")))
            self.assertEqual("ok", receipt["status"])
            self.assertEqual("synthetic", receipt["result"]["response"])

    def test_incomplete_input_is_durable_across_restart_and_checkpoint_is_private(self):
        with tempfile.TemporaryDirectory() as directory:
            store, protocol = self.make(directory, Engine())
            self.assertEqual(0o600, store.path.stat().st_mode & 0o777)
            self.assertEqual(0o700, store.path.parent.stat().st_mode & 0o777)
            partial = frame()[:9]
            self.assertEqual([], protocol.feed(partial))
            saved = store.read()
            self.assertEqual(partial, __import__("base64").b64decode(saved.metadata["input_tail_b64"]))
            restarted = FileProtocol(store, Engine())
            outputs = restarted.feed(frame()[9:] + b"\n")
            self.assertEqual(1, len(outputs))

    def test_whole_split_and_restart_input_have_identical_output_and_checkpoint(self):
        wire = frame() + b"\n"
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            whole_engine, split_engine = Engine(), Engine()
            whole_store, whole = self.make(first, whole_engine)
            split_store, split = self.make(second, split_engine)
            whole_output = whole.feed(wire)[0]
            self.assertEqual([], split.feed(wire[:7]))
            split = FileProtocol(split_store, split_engine)
            split_output = split.feed(wire[7:])[0]
            self.assertEqual(whole_output, split_output)
            self.assertEqual(whole_store.path.read_bytes(), split_store.path.read_bytes())
            self.assertEqual(1, whole_engine.calls)
            self.assertEqual(1, split_engine.calls)

    def test_two_frames_wait_in_tail_until_pending_output_acknowledged(self):
        second = frame(2, "Checkpoint") + b"\n"
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine()
            store, protocol = self.make(directory, engine)
            first_wire = frame(1) + b"\n"
            output1 = protocol.feed(first_wire + second)
            self.assertEqual(1, len(output1))
            self.assertEqual(second, __import__("base64").b64decode(
                store.read().metadata["input_tail_b64"]))
            self.assertEqual([], protocol.feed(b""))
            self.assertEqual(output1[0], FileProtocol(store, engine).replay_pending())
            self.assertEqual(1, engine.calls)
            protocol.acknowledge_output(1)
            output2 = protocol.feed(b"")
            self.assertEqual(1, len(output2))
            self.assertEqual(2, store.read().metadata["cursor"])
            self.assertEqual(1, engine.calls)

    def test_acknowledgement_stream_copies_standing_and_keeps_pending_comparisons(self):
        with tempfile.TemporaryDirectory() as directory:
            engine = Engine()
            store, protocol = self.make(directory, engine)
            protocol.process(frame())
            protocol.acknowledge_output(1)
            saved = store.read()
            self.assertIsNone(saved.metadata["pending_output_b64"])
            self.assertEqual([{"comparison": "pending-1"}], saved.metadata["pending_comparisons"])
            with saved.open_standing() as region:
                self.assertEqual(b"new synthetic standing", region.read())


if __name__ == "__main__":
    unittest.main()
