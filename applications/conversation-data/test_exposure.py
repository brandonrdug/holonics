import json
import os
from pathlib import Path
import tempfile
import unittest

from conversation_data import package
from exposure import EXPOSURE_SCHEMA, export_exposure


def message(role, identity, text, timestamp=None, content=None, parent=None):
    value = {
        "type": "response_item",
        "payload": {
            "type": "message",
            "role": role,
            "id": identity,
            "content": content if content is not None else [
                {"type": "input_text" if role == "user" else "output_text", "text": text}
            ],
        },
    }
    if timestamp is not None:
        value["timestamp"] = timestamp
    if parent is not None:
        value["payload"]["parent_id"] = parent
    return value


class ExposureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def source(self, name, records):
        path = self.root / name
        path.write_text("".join(json.dumps(record) + "\n" for record in records))
        return path

    def dataset(self, records, name="input.jsonl"):
        source = self.source(name, records)
        dataset = self.root / f"{name}.sqlite"
        package([("codex", source)], dataset)
        return dataset

    def read_lines(self, path):
        return [json.loads(line) for line in path.read_text().splitlines()]

    def test_occurrence_frames_keep_roles_and_future_material_separate(self):
        dataset = self.dataset([
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request", "2026-09-03T00:01:00Z"),
            message("assistant", "a", "answer", "2026-09-03T00:02:00Z", [
                {"type": "output_text", "text": "answer"},
                {"type": "reasoning", "text": "hidden reasoning"},
            ]),
            message("user", "later", "later observation", "2026-09-03T00:03:00Z"),
        ])
        output = self.root / "exposure.jsonl"
        result = export_exposure(dataset, output)
        rows = self.read_lines(output)
        self.assertEqual(result["schema"], EXPOSURE_SCHEMA)
        self.assertEqual(result["families"], 3)
        self.assertEqual(result["development_families"], 3)
        families = [row for row in rows if row["kind"] == "occurrence-family"]
        user = next(row for row in families if row["family"]["record_group"] == "declared:u")
        agent = next(row for row in families if row["family"]["record_group"] == "declared:a")
        later = next(row for row in families if row["family"]["record_group"] == "declared:later")
        self.assertEqual([p["text"] for p in user["views"][0]["visible_parts"]], ["request"])
        self.assertEqual([p["text"] for p in agent["views"][0]["visible_parts"]], ["answer"])
        self.assertIn("reasoning", [p["kind"] for p in agent["views"][0]["nonvisible_part_references"]])
        self.assertNotIn("later observation", json.dumps(user))
        self.assertNotIn("answer", json.dumps(user))
        self.assertTrue(any(link["kind"] == "comparison-request" for link in agent["views"][0]["links"]))
        self.assertFalse(any(link["kind"] == "comparison-request" for link in user["views"][0]["links"]))
        self.assertTrue(any(link["kind"] == "later-human-after-agent" for link in later["views"][0]["links"]))
        self.assertNotIn("path", user["views"][0])
        self.assertIn("private_path", rows[0]["private_sources"][0])
        self.assertNotIn("agent_response_is_gold", json.dumps(rows))
        self.assertNotIn("loss", json.dumps(rows))

    def test_explicit_parent_reference_is_metadata_only(self):
        dataset = self.dataset([
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "parent", "earlier", "2026-09-03T00:01:00Z"),
            message("assistant", "old", "old answer", "2026-09-03T00:02:00Z"),
            message("user", "u", "request", "2026-09-03T00:03:00Z", parent="parent"),
            message("assistant", "a", "answer", "2026-09-03T00:04:00Z", parent="u"),
        ], "parent.jsonl")
        output = self.root / "parent-exposure.jsonl"
        export_exposure(dataset, output)
        family = next(row for row in self.read_lines(output) if row.get("kind") == "occurrence-family" and row["family"]["record_group"] == "declared:a")
        links = family["views"][0]["links"]
        parent_link = next(link for link in links if link["kind"] == "provider-parent")
        self.assertEqual(parent_link["availability"], "prior")
        self.assertIn("record_group", parent_link["target"])
        self.assertIn("normalized_timestamp", parent_link["target"])
        self.assertNotIn("visible_parts", parent_link["target"])

    def test_all_captured_views_stay_in_one_family_and_cut_is_evaluation(self):
        records = [
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request", "2026-09-03T00:01:00Z"),
            message("assistant", "a", "answer", "2026-09-03T00:02:00Z"),
            {"type": "session_meta", "timestamp": "2026-09-04T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request", "2026-09-04T00:01:00Z"),
            message("assistant", "a", "answer", "2026-09-04T00:02:00Z"),
        ]
        dataset = self.dataset(records)
        output = self.root / "evaluation.jsonl"
        result = export_exposure(dataset, output)
        family = next(row for row in self.read_lines(output) if row["kind"] == "occurrence-family" and row["family"]["record_group"] == "declared:u")
        self.assertEqual(result["families"], 2)
        self.assertEqual(len(family["views"]), 2)
        self.assertEqual(family["partition"], "deferred")
        self.assertIn("timestamp-at-or-after-development-cut", family["partition_reasons"])
        self.assertIn("conflicting-view-timestamps", family["partition_reasons"])

    def test_missing_contradictory_and_conflicting_views_defer_without_selection(self):
        missing = self.dataset([
            {"type": "session_meta", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request"),
            message("assistant", "a", "answer"),
        ], "missing.jsonl")
        output = self.root / "missing-exposure.jsonl"
        export_exposure(missing, output)
        family = next(row for row in self.read_lines(output) if row.get("kind") == "occurrence-family" and row["family"]["record_group"] == "declared:u")
        self.assertEqual(family["partition"], "deferred")
        self.assertIn("missing-or-invalid-timestamp", family["partition_reasons"])

        contradictory = self.dataset([
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request", "2026-09-03T00:03:00Z"),
            message("assistant", "a", "answer", "2026-09-03T00:02:00Z"),
        ], "contradictory.jsonl")
        output = self.root / "contradictory-exposure.jsonl"
        export_exposure(contradictory, output)
        family = next(row for row in self.read_lines(output) if row.get("kind") == "occurrence-family" and row["family"]["record_group"] == "declared:a")
        self.assertEqual(family["partition"], "deferred")
        self.assertIn("contradictory-request-response-order", family["partition_reasons"])

        conflict = self.dataset([
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "first", "2026-09-03T00:01:00Z"),
            message("assistant", "a", "answer", "2026-09-03T00:02:00Z"),
            message("user", "u", "second", "2026-09-03T00:03:00Z"),
        ], "conflict.jsonl")
        output = self.root / "conflict-exposure.jsonl"
        export_exposure(conflict, output)
        family = next(row for row in self.read_lines(output) if row.get("kind") == "occurrence-family" and row["family"]["record_group"] == "declared:u")
        self.assertEqual(family["partition"], "deferred")
        self.assertIn("conflicting-view-material", family["partition_reasons"])
        self.assertEqual(len(family["conflicts"]), 2)
        self.assertEqual(len(family["views"]), 2)

    def test_multiple_replies_do_not_repeat_request_or_reverse_parent_edges(self):
        dataset = self.dataset([
            {"type":"session_meta","payload":{"id":"s","thread_source":"user"}},
            message("user","u","request","2026-09-03T00:01:00Z"),
            message("assistant","progress","progress","2026-09-03T00:02:00Z", parent="u"),
            message("assistant","final","answer","2026-09-03T00:03:00Z", parent="progress"),
        ], "multiple.jsonl")
        output = self.root / "multiple-exposure.jsonl"
        export_exposure(dataset, output)
        frames = [r for r in self.read_lines(output) if r["kind"] == "occurrence-family"]
        self.assertEqual([r["family"]["record_group"] for r in frames],
                         ["declared:u", "declared:progress", "declared:final"])
        self.assertEqual(frames[0]["views"][0]["links"], [])
        self.assertFalse(any(l["target"]["record_group"] == "declared:final"
                             for l in frames[1]["views"][0]["links"] if l["target"]))

    def test_equivalent_clock_presentations_do_not_disagree_and_position_is_one_view(self):
        first = self.source("clock-one.jsonl", [
            {"type":"session_meta","payload":{"id":"s","thread_source":"user"}},
            message("user","u","request","2026-09-03T00:01:00Z"),
            message("assistant","a","answer","2026-09-03T00:02:00Z"),
        ])
        second = self.source("clock-two.jsonl", [
            {"type":"session_meta","payload":{"id":"s","thread_source":"user"}},
            message("user","u","request","2026-09-02T17:01:00-07:00"),
            message("assistant","a","answer","2026-09-02T17:02:00-07:00"),
        ])
        dataset = self.root / "clocks.sqlite"
        package([("codex", first),("codex", second)], dataset)
        output = self.root / "clock-exposure.jsonl"
        export_exposure(dataset, output)
        for frame in self.read_lines(output)[1:]:
            self.assertEqual(frame["partition"], "development")
            self.assertEqual(len(frame["views"]),2)
            position = frame["position"]
            self.assertIn((position["first_source"],position["first_record"],position["first_event"]),
                [(v["source"],v["record"]["number"],v["event"]) for v in frame["views"]])

    def test_unpaired_visible_material_and_unresolved_parent_are_not_omitted(self):
        dataset = self.dataset([
            {"type":"session_meta","payload":{"id":"s","thread_source":"user"}},
            message("assistant","orphan","visible with unresolved parent","2026-09-03T00:01:00Z", parent="missing"),
            message("user","unpaired","ordinary unpaired input","2026-09-03T00:02:00Z"),
        ], "unpaired.jsonl")
        output = self.root / "unpaired-exposure.jsonl"
        export_exposure(dataset, output)
        frames = self.read_lines(output)[1:]
        self.assertEqual({r["family"]["record_group"] for r in frames}, {"declared:orphan","declared:unpaired"})
        orphan = next(r for r in frames if r["family"]["record_group"] == "declared:orphan")
        link = next(l for l in orphan["views"][0]["links"] if l["kind"] == "provider-parent")
        self.assertIsNone(link["target"])
        self.assertEqual(link["availability"], "unresolved")

    def test_provider_generation_and_actual_branch_origin_survive_exposure(self):
        agent = message("assistant","record-id","worker material","2026-09-03T00:01:00Z")
        agent["payload"]["api_message_id"] = "generation-id"
        dataset = self.dataset([
            {"type":"session_meta","payload":{"id":"child","thread_source":"subagent",
             "source":{"subagent":{"thread_spawn":{"parent_thread_id":"parent","agent_path":"/root/child"}}}}},
            agent,
        ], "origin.jsonl")
        output = self.root / "origin-exposure.jsonl"
        export_exposure(dataset, output)
        view = self.read_lines(output)[1]["views"][0]
        self.assertEqual(view["native_id"], "record-id")
        self.assertEqual(view["provider_metadata"]["api_message_id"], "generation-id")
        self.assertEqual(view["provider_metadata"]["parent_session"], "parent")
        self.assertEqual(view["provider_metadata"]["agent_path"], "/root/child")

    def test_no_overwrite_and_private_mode(self):
        dataset = self.dataset([
            {"type": "session_meta", "timestamp": "2026-09-03T00:00:00Z", "payload": {"id": "s", "thread_source": "user"}},
            message("user", "u", "request", "2026-09-03T00:01:00Z"),
            message("assistant", "a", "answer", "2026-09-03T00:02:00Z"),
        ])
        output = self.root / "exposure.jsonl"
        export_exposure(dataset, output)
        self.assertEqual(os.stat(output).st_mode & 0o777, 0o600)
        with self.assertRaises(FileExistsError):
            export_exposure(dataset, output)


if __name__ == "__main__":
    unittest.main()
