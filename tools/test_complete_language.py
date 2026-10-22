"""Synthetic exterior controls; no GSM8K or HNN/model execution."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import complete_language as cli


class CompleteLanguageControls(unittest.TestCase):
    def test_missing_or_partial_output_barrier_never_opens_targets(self):
        with tempfile.TemporaryDirectory() as name:
            out = Path(name)
            plan = {"prompts": [{"row": x} for x in [1, 2, 3, 4]], "data_manifest_sha256": "fixed"}
            with self.assertRaises(FileNotFoundError):
                cli.score(plan, out)
            cli.write_new(out/"ALL_OUTPUTS_TERMINAL.json", {"all_declared_attempts_terminal": True,
                "data_manifest_sha256": "fixed", "records": []})
            with self.assertRaises(ValueError):
                cli.score(plan, out)
            self.assertFalse((out/"SCORING_OPEN_EVENT.json").exists())

    def test_budget_flag_cannot_default_into_model_execution(self):
        with mock.patch.object(cli, "checked_plan", return_value={"data_eligible": True, "status": "CODE_READY_PENDING_BUDGET_APPROVAL"}), \
             mock.patch.object(cli.subprocess, "Popen", side_effect=AssertionError("must not launch")):
            with self.assertRaises(PermissionError):
                cli.execute("unused", "unused", 0)

    def test_reviewed_plan_digest_refuses_post_prepare_mutation_before_launch(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name)/"plan.json"
            cli.write_new(path, {"scope": "synthetic plan"})
            original = cli.digest(path)
            path.write_text('{"scope":"changed"}')
            with mock.patch.object(cli.subprocess, "Popen", side_effect=AssertionError("must not launch")):
                with self.assertRaises(ValueError): cli.execute(path, "unused", cli.CAP_NS, original)

    def test_policy_commands_pin_independent_baseline_and_one_cold_replay(self):
        files = {n: {"absolute": "/prepared/"+n, "sha256": "pinned"} for n in
                 ["train-five-pass.bin", "causal-cuts.tsv", "public-keys.bin"]}
        plan = {"binary": "/never-executed", "backend": "host-reference", "files": files,
                "data_root": "/prepared", "prompts": [{"row": i, "path": f"q{i}", "sha256": "pinned"} for i in range(4)]}
        training, samples = cli.commands(plan, "/evidence")
        self.assertEqual(training[-4:-1], ["16384", "11280", "1128"])
        self.assertEqual(len(samples), 16)
        self.assertEqual(sum("cold-replay" in x["argv"] for x in samples), 1)
        self.assertEqual(sum("fresh.state" in x["argv"][4] for x in samples), 4)
        for item in samples:
            self.assertIn("host-reference", item["argv"])
            self.assertNotIn("answer", " ".join(item["argv"]))

    def test_scoring_skips_unselected_lines_before_json_decode_and_binds_seal(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            source = root/"synthetic.jsonl"
            source.write_bytes(b"this unselected line is deliberately invalid JSON\n" +
                json.dumps({"question": "synthetic-one", "answer": "A"}).encode()+b"\n"+
                json.dumps({"question": "synthetic-two", "answer": "B"}).encode()+b"\n")
            for row in [10, 11]: (root/f"target{row}").write_bytes(b"A\n")
            data = {"retention_scoring": {"targets": [{"row": row, "path": f"target{row}"} for row in [10, 11]]}}
            cli.write_new(root/"manifest.json", data)
            plan = {"prompts": [{"row": row} for row in [10, 11, 1, 2]], "data_manifest_sha256": "fixed",
                    "data_manifest": str(root/"manifest.json"), "data_root": str(root),
                    "development_score_source": {"path": str(source), "sha256": cli.digest(source),
                       "rows": [{"row": row, "question_sha256": hashlib.sha256(q.encode()).hexdigest()}
                                for row, q in [(1, "synthetic-one"), (2, "synthetic-two")]]}}
            records = []
            for row in [10, 11, 1, 2]:
                for policy in cli.POLICIES:
                    raw = root/f"{row}-{policy}.bin"; raw.write_bytes(b"A"*32)
                    meta = root/f"{row}-{policy}.json"; cli.write_new(meta, {"scope": "synthetic serialization fixture"})
                    records.append({"row": row, "policy": policy, "raw": str(raw), "raw_sha256": cli.digest(raw),
                                    "metadata": str(meta), "metadata_sha256": cli.digest(meta)})
            cli.write_new(root/"ALL_OUTPUTS_TERMINAL.json", {"records": records,
                "all_declared_attempts_terminal": True, "data_manifest_sha256": "fixed"})
            cli.score(plan, root)
            event = cli.load(root/"SCORING_OPEN_EVENT.json")
            self.assertEqual(event["output_manifest_sha256"], cli.digest(root/"ALL_OUTPUTS_TERMINAL.json"))
            self.assertEqual(len(cli.load(root/"POST_OUTPUT_SCORES.json")["literal_comparisons"]), 16)
            # A modified output invalidates the barrier before any second target access.
            Path(records[0]["raw"]).write_bytes(b"changed")
            with self.assertRaises(ValueError): cli.verified_output_barrier(plan, root)

    def test_seal_preserves_invalid_bytes_in_readable_target_free_transcript(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            prompts = []
            samples = []
            for row in range(4):
                (root/f"q{row}").write_bytes(b"synthetic\n")
                prompts.append({"row": row, "path": f"q{row}"})
                for policy in cli.POLICIES:
                    directory = root/f"row-{row}-{policy}"; directory.mkdir()
                    (directory/"OUTPUT.bin").write_bytes(bytes([0,255]))
                    cli.write_new(directory/"OUTPUT.json", {"raw_bytes": [0,255],
                        "output_cells_requested": 128, "stop": "Unresolved"})
                    samples.append({"row": row, "policy": policy, "directory": str(directory)})
            plan = {"prompts": prompts, "data_root": str(root), "data_manifest_sha256": "fixture"}
            seal = cli.seal_outputs(plan, root, samples)
            self.assertFalse(seal["all_full32bytes"])
            text = (root/"TRANSCRIPT.txt").read_text()
            self.assertIn("00ff", text)
            self.assertIn("null", text)
            self.assertEqual(len(seal["records"]), 16)
            cli.verified_output_barrier(plan, root)


if __name__ == "__main__":
    unittest.main()
