"""Protocol durability and privacy checks; fixtures make no product claim."""
import json
import os
import tempfile
import unittest
from pathlib import Path

from athena_protocol import (AtomicCheckpoint, Checkpoint, EngineTransition, Protocol, ProtocolError,
                             RefusingFixtureEngine, render_human, render_json,
                             render_jsonl)


def frame(sequence, command="Ask", payload=None):
    return json.dumps({"version": 1, "sequence": sequence, "command": command,
                       "payload": payload or {}}, separators=(",", ":")).encode() + b"\n"


class CountingEngine:
    def __init__(self):
        self.calls = 0

    def ask(self, payload, standing):
        self.calls += 1
        return EngineTransition({"answer": "fixture", "health": "not-provided"}, standing)

    def inspect(self, payload, standing):
        self.calls += 1
        return EngineTransition({"kind": "inspection"}, standing)


class InterruptOnceEngine(CountingEngine):
    def ask(self, payload, standing):
        self.calls += 1
        if self.calls == 1:
            raise RuntimeError("interrupted before native transition returned")
        return EngineTransition({"answer": "fixture", "health": "not-provided"}, standing)


class AskTransitionEngine:
    def __init__(self, receipt):
        self.receipt = receipt

    def ask(self, payload, standing):
        return EngineTransition(self.receipt, standing)

    def inspect(self, payload, standing):
        return EngineTransition({}, standing)


class FailingStore:
    def __init__(self, inner):
        self.inner = inner
        self.fail = False

    def load(self):
        return self.inner.load()

    def save(self, checkpoint):
        if self.fail:
            raise OSError("simulated atomic-save failure")
        return self.inner.save(checkpoint)


class ProtocolTests(unittest.TestCase):
    def test_split_input_emits_only_after_complete_frame(self):
        with tempfile.TemporaryDirectory() as d:
            p = Protocol(AtomicCheckpoint(Path(d) / "state"), RefusingFixtureEngine())
            data = frame(1)
            self.assertEqual([], p.feed(data[:13]))
            out = p.feed(data[13:])
            self.assertEqual(1, len(out))
            self.assertEqual("refused", json.loads(out[0])["status"])

    def test_partial_frame_survives_restart_byte_identically(self):
        with tempfile.TemporaryDirectory() as d:
            whole_path = Path(d) / "whole"
            whole = Protocol(AtomicCheckpoint(whole_path), RefusingFixtureEngine())
            whole_output = whole.feed(frame(1))
            whole.acknowledge_output(1)
            whole_bytes = whole_path.read_bytes()

            split_path = Path(d) / "split"
            first = Protocol(AtomicCheckpoint(split_path), RefusingFixtureEngine())
            wire = frame(1)
            self.assertEqual([], first.feed(wire[:17]))
            self.assertEqual(wire[:17], first.state.input_tail)
            resumed = Protocol(AtomicCheckpoint(split_path), RefusingFixtureEngine())
            split_output = resumed.feed(wire[17:])
            self.assertEqual(whole_output, split_output)
            resumed.acknowledge_output(1)
            self.assertEqual(whole_bytes, split_path.read_bytes())

    def test_two_staged_frames_wait_for_first_output_acknowledgment(self):
        with tempfile.TemporaryDirectory() as d:
            path = AtomicCheckpoint(Path(d) / "state")
            engine = CountingEngine()
            p = Protocol(path, engine)
            first, second = frame(1), frame(2, "Inspect")
            outputs = p.feed(first + second)
            self.assertEqual(1, len(outputs))
            self.assertEqual(second, p.state.input_tail)
            self.assertEqual(1, engine.calls)
            restarted = Protocol(path, engine)
            self.assertEqual(outputs[0], restarted.replay_pending())
            restarted.acknowledge_output(1)
            more = restarted.feed(b"")
            self.assertEqual(1, len(more))
            self.assertEqual(2, engine.calls)
            self.assertEqual(b"", restarted.state.input_tail)

    def test_interruption_before_native_commit_retains_complete_input(self):
        with tempfile.TemporaryDirectory() as d:
            path = AtomicCheckpoint(Path(d) / "state")
            engine = InterruptOnceEngine()
            p = Protocol(path, engine)
            with self.assertRaises(RuntimeError):
                p.feed(frame(1))
            self.assertEqual(0, p.state.cursor)
            self.assertEqual(frame(1), path.load().input_tail)
            restarted = Protocol(path, engine)
            output = restarted.feed(b"")
            self.assertEqual(1, len(output))
            self.assertEqual(b"", restarted.state.input_tail)
            self.assertEqual(1, restarted.state.cursor)

    def test_restart_has_byte_identical_checkpoint_and_output(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "state"
            uninterrupted = Protocol(AtomicCheckpoint(path), CountingEngine())
            first = uninterrupted.process(frame(1))
            uninterrupted.acknowledge_output(1)
            final_bytes = path.read_bytes()
            resumed = Protocol(AtomicCheckpoint(path), CountingEngine())
            second = resumed.process(frame(2, "Inspect"))
            resumed.acknowledge_output(2)
            resumed_checkpoint = path.read_bytes()

            other = Path(d) / "other"
            original = Protocol(AtomicCheckpoint(other), CountingEngine())
            self.assertEqual(first, original.process(frame(1)))
            original.acknowledge_output(1)
            self.assertEqual(final_bytes, other.read_bytes())
            self.assertEqual(second, original.process(frame(2, "Inspect")))
            original.acknowledge_output(2)
            self.assertEqual(resumed_checkpoint, other.read_bytes())

    def test_broken_write_replays_same_sequence_without_native_reexecution(self):
        with tempfile.TemporaryDirectory() as d:
            path = AtomicCheckpoint(Path(d) / "state")
            engine = CountingEngine()
            p = Protocol(path, engine)
            output = p.process(frame(1))
            self.assertEqual(1, engine.calls)
            restarted = Protocol(path, engine)
            self.assertEqual(output, restarted.replay_pending())
            self.assertEqual(output, restarted.process(frame(1)))
            self.assertEqual(1, engine.calls)
            restarted.acknowledge_output(1)
            with self.assertRaises(ProtocolError):
                restarted.process(frame(1))

    def test_exact_views_and_private_payload_exclusion(self):
        with tempfile.TemporaryDirectory() as d:
            secret = "PRIVATE-CONTEXT-MUST-NOT-LEAK"
            p = Protocol(AtomicCheckpoint(Path(d) / "state"), RefusingFixtureEngine())
            output = p.process(frame(1, payload={"context": secret}))
            receipt = json.loads(output)
            self.assertEqual(output, render_jsonl(output))
            self.assertEqual(json.loads(render_json(output)), receipt)
            self.assertNotIn(secret, render_human(output))
            self.assertNotIn(secret, output.decode())
            self.assertEqual(0o600, os.stat(Path(d) / "state").st_mode & 0o777)

    def test_checkpoint_has_one_opaque_standing_and_no_tape(self):
        state = Checkpoint(standing=b"\x00\xffopaque", cursor=7,
                           pending_comparisons=[{"comparison": "opaque-pending"}])
        raw = state.encode()
        restored = Checkpoint.decode(raw)
        self.assertEqual(state.standing, restored.standing)
        self.assertEqual(raw, restored.encode())
        obj = json.loads(raw)
        self.assertEqual({"version", "standing", "cursor", "pending_comparisons",
                          "pending_output", "pending_sequence", "input_tail"}, set(obj))
        self.assertNotIn("events", obj)

    def test_checkpoint_rejects_float_and_noninteger_sequence_fields(self):
        state = Checkpoint().encode()
        obj = json.loads(state)
        obj["cursor"] = 1.0
        with self.assertRaises(ProtocolError):
            Checkpoint.decode(json.dumps(obj).encode())
        obj = json.loads(state)
        obj["pending_comparisons"] = [{"covector": 0.5}]
        with self.assertRaises(ProtocolError):
            Checkpoint.decode(json.dumps(obj).encode())
        obj = json.loads(state)
        obj["pending_sequence"] = True
        with self.assertRaises(ProtocolError):
            Checkpoint.decode(json.dumps(obj).encode())

    def test_input_payload_refuses_float_before_native_call(self):
        with tempfile.TemporaryDirectory() as d:
            engine = CountingEngine()
            p = Protocol(AtomicCheckpoint(Path(d) / "state"), engine)
            with self.assertRaises(ProtocolError):
                p.process(frame(1, payload={"foreign_value": 0.5}))
            self.assertEqual(0, engine.calls)
            self.assertEqual(0, p.state.cursor)
            invalid_version = frame(1).replace(b'"version":1', b'"version":1.0')
            with self.assertRaises(ProtocolError):
                p.process(invalid_version)
            self.assertEqual(0, engine.calls)

    def test_failed_save_does_not_publish_candidate_or_ack_in_memory(self):
        with tempfile.TemporaryDirectory() as d:
            inner = AtomicCheckpoint(Path(d) / "state")
            store = FailingStore(inner)
            engine = CountingEngine()
            p = Protocol(store, engine)
            before = p.state.encode()
            store.fail = True
            with self.assertRaises(OSError):
                p.process(frame(1, "Inspect"))
            self.assertEqual(before, p.state.encode())
            store.fail = False
            output = p.process(frame(1, "Inspect"))
            store.fail = True
            pending_before = p.state.encode()
            with self.assertRaises(OSError):
                p.acknowledge_output(1)
            self.assertEqual(pending_before, p.state.encode())
            self.assertEqual(output, p.replay_pending())

    def test_ask_refuses_missing_receipt_or_simplex_covering_face(self):
        complete = {"response": "must not publish without certificate",
                    "numerical_health": {"radius": "0", "robust_count": 1,
                                         "operator_bound": "1", "contraction": "1/2"},
                    "provenance": {"keys": []}, "decoder": {"id": "fixture"},
                    "grain_fibre": {"grain": "fixture", "fibre": []},
                    "costs": {"release": 0}, "simplex_covering": False}
        with tempfile.TemporaryDirectory() as d:
            p = Protocol(AtomicCheckpoint(Path(d) / "state"),
                         AskTransitionEngine({"response": "unsafe"}))
            missing = json.loads(p.process(frame(1)))
            self.assertEqual("refused", missing["status"])
            self.assertNotIn("unsafe", json.dumps(missing))
            p.acknowledge_output(1)
            complete["simplex_covering"] = True
            p.engine = AskTransitionEngine(complete)
            covering = json.loads(p.process(frame(2)))
            self.assertEqual("refused", covering["status"])
            self.assertNotIn("must not publish", json.dumps(covering))
            p.acknowledge_output(2)
            complete["simplex_covering"] = False
            del complete["response"]
            missing_text = json.loads(p.process(frame(3)))
            self.assertEqual("refused", missing_text["status"])

    def test_checkpoint_parent_is_owner_only(self):
        with tempfile.TemporaryDirectory() as d:
            parent = Path(d) / "private"
            parent.mkdir(mode=0o755)
            os.chmod(parent, 0o755)
            AtomicCheckpoint(parent / "state")
            self.assertEqual(0o700, os.stat(parent).st_mode & 0o777)

    def test_duplicate_sequence_cannot_reexecute_after_delivery(self):
        with tempfile.TemporaryDirectory() as d:
            engine = CountingEngine()
            p = Protocol(AtomicCheckpoint(Path(d) / "state"), engine)
            p.process(frame(1))
            p.acknowledge_output(1)
            with self.assertRaises(ProtocolError):
                p.process(frame(1))
            self.assertEqual(1, engine.calls)


if __name__ == "__main__":
    unittest.main()
