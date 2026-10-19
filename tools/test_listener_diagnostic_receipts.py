"""Synthetic receipt-wrapper controls; only the successful fixture starts a harmless Python child."""
from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path

import listener_diagnostic_receipts as receipts
import listener_diagnostic_stage as stage


class ReceiptControls(unittest.TestCase):
    @staticmethod
    def _complete_result(plan: stage.DeadlinePlan) -> stage.ProcessResult:
        return stage.ProcessResult(
            status="complete", reason="synthetic_exit", returncode=0,
            deadline_evidence=False, term_sent=False, kill_sent=False,
            peak_group_rss_bytes=1, start_ns=plan.start_ns, term_ns=plan.term_ns,
            native_ns=plan.native_ns, total_ns=plan.total_ns,
            finished_ns=plan.start_ns + 1, group_alive_at_return=False,
            cleanup_uncertain=False, waited_child_cpu_user_us=0,
            waited_child_cpu_system_us=0, term_sent_ns=None, kill_sent_ns=None,
        )

    def _config(self, root: Path) -> tuple[Path, Path, dict, Callable[..., receipts.RepoState]]:
        repo = root / "repo"
        repo.mkdir()
        input_path = root / "passage.bin"
        input_path.write_bytes(b"synthetic input marker\n")
        cargo_lock = root / "Cargo.lock"
        cargo_lock.write_text("# synthetic lock pin\n", encoding="utf-8")
        output_dir = root / "fresh-output"
        log_path = root / "fresh.log"
        receipt_path = root / "terminal.json"
        files = [
            {"role": "wrapper", "path": str(Path(receipts.__file__).resolve())},
            {"role": "supervisor", "path": str(Path(stage.__file__).resolve())},
            {"role": "binary", "path": str(Path(sys.executable).resolve())},
            {"role": "input", "path": str(input_path)},
            {"role": "cargo_lock", "path": str(cargo_lock)},
        ]
        for item in files:
            item["sha256"] = hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest()
        config = {
            "repo_root": str(repo),
            "repo": {"head": "pinned-head", "tree": "pinned-tree", "clean": True},
            "files": files,
            "argv": [
                str(Path(sys.executable).resolve()),
                "-c",
                "import os,pathlib; p=pathlib.Path(os.environ['REQ063_OUTPUT_DIR']); p.joinpath('env.txt').write_text(os.environ['CUDA_VISIBLE_DEVICES']+'|'+os.environ['RAYON_NUM_THREADS']); print('receipt-fixture-ok')",
            ],
            "cwd": str(repo),
            "output_dir": str(output_dir),
            "log_path": str(log_path),
            "receipt_path": str(receipt_path),
            "disk_root": str(root),
            "evidence_reserve_ns": receipts.EVIDENCE_RESERVE_NS,
        }
        config_path = root / "config.json"
        config_path.write_text(json.dumps(config, sort_keys=True), encoding="utf-8")
        config_sha = hashlib.sha256(config_path.read_bytes()).hexdigest()

        def repo_reader(_root, *, deadline_ns, clock):
            return receipts.RepoState("pinned-head", "pinned-tree", True)

        return config_path, receipt_path, config, repo_reader

    @staticmethod
    def _disk(_path: Path) -> dict[str, int]:
        return {"total_bytes": 4 * 1024**3, "free_bytes": 2 * 1024**3}

    def test_preflight_pin_or_disk_mismatch_records_failure_without_launch(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, config, _ = self._config(root)
            config["repo"]["head"] = "expected-head-that-does-not-match"
            config_path.write_text(json.dumps(config, sort_keys=True), encoding="utf-8")
            config_sha = hashlib.sha256(config_path.read_bytes()).hexdigest()
            calls = []

            def mismatched_repo(_root, *, deadline_ns, clock):
                return receipts.RepoState("different-head", "pinned-tree", True)

            def forbidden_supervisor(*_args, **_kwargs):
                calls.append("launched")
                raise AssertionError("preflight mismatch must refuse native launch")

            result = receipts.run_receipted_stage(
                config_path,
                config_sha,
                receipt_path,
                repo_reader=mismatched_repo,
                disk_reader=lambda _path: {"total_bytes": 1024, "free_bytes": 1},
                supervise=forbidden_supervisor,
                install_limits=False,
            )
            self.assertEqual(result["status"], "preflight_failed")
            self.assertFalse(calls)
            self.assertTrue(any("HEAD differs" in item for item in result["failures"]))
            self.assertTrue(any("512 MiB floor" in item for item in result["failures"]))
            self.assertIsNone(result["process"])
            self.assertEqual(json.loads(receipt_path.read_text(encoding="utf-8"))["status"], "preflight_failed")
            self.assertFalse((root / "fresh-output").exists())

    def test_external_config_hash_failure_still_writes_terminal_create_only_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, _repo = self._config(root)
            result = receipts.run_receipted_stage(config_path, "0" * 64, receipt_path)
            self.assertEqual(result["status"], "preflight_failed")
            self.assertIn("configuration SHA-256", result["failures"][0])
            self.assertEqual(json.loads(receipt_path.read_text(encoding="utf-8"))["status"], "preflight_failed")

    def test_postflight_rehash_refuses_success_after_a_pinned_input_changes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, config, repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()
            input_path = Path(next(item["path"] for item in config["files"] if item["role"] == "input"))

            def mutate_synthetic_input(_argv, **kwargs):
                input_path.write_bytes(b"changed synthetic fixture\n")
                return self._complete_result(kwargs["plan"])

            result = receipts.run_receipted_stage(
                config_path, expected, receipt_path, repo_reader=repo_reader,
                disk_reader=self._disk, supervise=mutate_synthetic_input,
                install_limits=False,
            )
            self.assertEqual(result["process"]["status"], "complete")
            self.assertEqual(result["status"], "integrity_failure")
            self.assertTrue(any("pinned input file digest differs" in reason for reason in result["failures"]))

    def test_preflight_time_and_evidence_reserve_do_not_restart_the_deadline(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, _repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()
            started = 10_000_000_000
            now = [started]
            seen = []

            def delayed_repo(_root, *, deadline_ns, clock):
                now[0] += 5_000_000_000
                return receipts.RepoState("pinned-head", "pinned-tree", True)

            def record_plan(_argv, **kwargs):
                plan = kwargs["plan"]
                seen.append((plan, kwargs["kill_cutoff_ns"], kwargs["clock"]()))
                return self._complete_result(plan)

            result = receipts.run_receipted_stage(
                config_path, expected, receipt_path, clock=lambda: now[0],
                repo_reader=delayed_repo, disk_reader=self._disk,
                supervise=record_plan, install_limits=False,
            )
            self.assertEqual(len(seen), 1)
            plan, kill_cutoff, launch_clock = seen[0]
            self.assertGreater(launch_clock, started)
            self.assertEqual(plan.start_ns, started)
            self.assertEqual(plan.native_ns, started + 290_000_000_000)
            self.assertEqual(plan.term_ns, started + 295_000_000_000)
            self.assertEqual(kill_cutoff, started + 299_000_000_000)
            self.assertEqual(plan.total_ns, started + 300_000_000_000)
            self.assertEqual(result["status"], "complete")

    def test_harmless_child_receipt_captures_pins_samples_cpu_and_create_only_outputs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, repo_reader = self._config(root)
            config_sha = hashlib.sha256(config_path.read_bytes()).hexdigest()
            result = receipts.run_receipted_stage(
                config_path,
                config_sha,
                receipt_path,
                repo_reader=repo_reader,
                disk_reader=self._disk,
                install_limits=False,
            )
            self.assertEqual(result["status"], "complete")
            self.assertEqual(result["process"]["status"], "complete")
            self.assertEqual(result["process"]["group_alive_at_return"], False)
            self.assertIsNotNone(result["process"]["waited_child_cpu_user_us"])
            self.assertIsNotNone(result["process"]["term_ns"])
            self.assertTrue(result["process_samples"])
            self.assertGreaterEqual(len(result["disk_samples"]), 2)
            self.assertEqual(result["log"]["status"], "verified")
            self.assertGreater(result["log"]["bytes"], 0)
            self.assertEqual(
                result["log"]["sha256"],
                hashlib.sha256(Path(result["log_path"]).read_bytes()).hexdigest(),
            )
            self.assertFalse(result["deadline_overrun"])
            self.assertEqual(result["preflight"]["pins"]["repo"]["head"], "pinned-head")
            self.assertEqual(result["postflight"]["pins"]["repo"]["tree"], "pinned-tree")
            output_dir = Path(result["output_dir"])
            self.assertEqual((output_dir / "env.txt").read_text(encoding="utf-8"), "|1")
            self.assertIn("receipt-fixture-ok", Path(result["log_path"]).read_text(encoding="utf-8"))
            with self.assertRaises(FileExistsError):
                receipts.run_receipted_stage(
                    config_path,
                    config_sha,
                    receipt_path,
                    repo_reader=repo_reader,
                    disk_reader=self._disk,
                    install_limits=False,
                )


if __name__ == "__main__":
    unittest.main()
