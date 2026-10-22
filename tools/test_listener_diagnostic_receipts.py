"""Synthetic receipt-wrapper controls; only the successful fixture starts a harmless Python child."""
from __future__ import annotations

import dataclasses
import hashlib
import json
import signal
import sys
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path
from unittest import mock

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
        child_cwd = repo / "runner"
        child_cwd.mkdir()
        data_dir = repo / "data"
        data_dir.mkdir()
        input_path = data_dir / "passage.bin"
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
            {"role": "input", "path": "data/passage.bin"},
            {"role": "cargo_lock", "path": str(cargo_lock)},
        ]
        for item in files:
            pinned_file = Path(item["path"])
            if not pinned_file.is_absolute():
                pinned_file = repo / pinned_file
            item["sha256"] = hashlib.sha256(pinned_file.read_bytes()).hexdigest()
        child_script = (
            "import hashlib,json,os,pathlib,sys; "
            "p=pathlib.Path(sys.argv[sys.argv.index('--learn')+1]).resolve(); "
            "b=p.read_bytes(); o=pathlib.Path(os.environ['REQ063_OUTPUT_DIR']); "
            "o.joinpath('env.txt').write_text(os.environ['CUDA_VISIBLE_DEVICES']+'|'+os.environ['RAYON_NUM_THREADS']); "
            "o.joinpath('consumed.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'content':b.decode()})); "
            "print('receipt-fixture-ok')"
        )
        config = {
            "repo_root": str(repo),
            "repo": {"head": "pinned-head", "tree": "pinned-tree", "clean": True},
            "files": files,
            "argv": [
                str(Path(sys.executable).resolve()),
                "-c",
                child_script,
                "--learn",
                "../data/passage.bin",
            ],
            "cwd": str(child_cwd),
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

    @staticmethod
    def _landing_path(receipt_path: Path) -> Path:
        return receipt_path.with_name(receipt_path.name + ".landing.json")

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

    def test_invalid_learn_binding_and_input_pin_contracts_refuse_launch(self):
        cases = (
            ("missing learn", lambda c: c["argv"].__setitem__(slice(-2, None), []), "exactly one separate --learn"),
            ("duplicate learn", lambda c: c["argv"].extend(["--learn", "../data/passage.bin"]), "exactly one separate --learn"),
            ("equals form", lambda c: c["argv"].append("--learn=../data/passage.bin"), "--learn=VALUE"),
            ("missing input pin", lambda c: c["files"].__setitem__(slice(None), [p for p in c["files"] if p["role"] != "input"]), "exactly one input pin"),
            ("duplicate input pin", lambda c: c["files"].append(next(p.copy() for p in c["files"] if p["role"] == "input")), "exactly one input pin"),
            ("different child-relative path", lambda c: c["argv"].__setitem__(-1, "data/passage.bin"), "does not resolve to the pinned input"),
        )
        for label, mutate, expected_failure in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                config_path, receipt_path, config, repo_reader = self._config(root)
                mutate(config)
                config_path.write_text(json.dumps(config, sort_keys=True), encoding="utf-8")
                config_sha = hashlib.sha256(config_path.read_bytes()).hexdigest()
                calls = []

                def forbidden_supervisor(*_args, **_kwargs):
                    calls.append("launched")
                    raise AssertionError("invalid input binding must refuse launch")

                result = receipts.run_receipted_stage(
                    config_path,
                    config_sha,
                    receipt_path,
                    repo_reader=repo_reader,
                    disk_reader=self._disk,
                    supervise=forbidden_supervisor,
                    install_limits=False,
                )
                self.assertEqual(result["status"], "preflight_failed")
                self.assertFalse(calls)
                self.assertIsNone(result["process"])
                self.assertTrue(any(expected_failure in item for item in result["failures"]))
                self.assertFalse((root / "fresh-output").exists())
                self.assertEqual(result["preflight"]["input_binding"]["status"], "invalid")

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
            input_path = Path(config["repo_root"]) / next(
                item["path"] for item in config["files"] if item["role"] == "input"
            )

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

    def test_terminal_write_landing_is_separate_and_late_write_does_not_rewrite_work_status(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()
            started = 10_000_000_000
            now = [started]
            original_write = receipts._write_receipt
            terminal_write_count = []

            def delayed_terminal_write(stream, value):
                original_write(stream, value)
                if "finished_monotonic_ns" in value:
                    terminal_write_count.append(1)
                    now[0] = started + stage.TOTAL_NS + 17

            def complete_without_launch(_argv, **kwargs):
                return self._complete_result(kwargs["plan"])

            with mock.patch.object(receipts, "_write_receipt", delayed_terminal_write):
                result = receipts.run_receipted_stage(
                    config_path,
                    expected,
                    receipt_path,
                    clock=lambda: now[0],
                    repo_reader=repo_reader,
                    disk_reader=self._disk,
                    supervise=complete_without_launch,
                    install_limits=False,
                )

            sidecar = json.loads(self._landing_path(receipt_path).read_text(encoding="utf-8"))
            self.assertEqual(result["status"], "complete")
            self.assertFalse(result["deadline_overrun"])
            self.assertEqual(sidecar["landing_status"], "landed_late")
            self.assertFalse(sidecar["within_total_deadline"])
            self.assertEqual(sidecar["work_status"], "complete")
            self.assertFalse(sidecar["sidecar_write_latency_measured"])
            self.assertIn("terminal receipt fsync", sidecar["observation"])
            self.assertEqual(terminal_write_count, [1])
            self.assertEqual(len(self._landing_path(receipt_path).read_text(encoding="utf-8").splitlines()), 1)

    def test_missing_landing_sidecar_does_not_claim_receipt_landing(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()

            def complete_without_launch(_argv, **kwargs):
                return self._complete_result(kwargs["plan"])

            with mock.patch.object(receipts, "_write_landing_sidecar", side_effect=OSError("controlled sidecar refusal")):
                result = receipts.run_receipted_stage(
                    config_path, expected, receipt_path, repo_reader=repo_reader,
                    disk_reader=self._disk, supervise=complete_without_launch,
                    install_limits=False,
                )
            durable = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(result["status"], "complete")
            self.assertEqual(durable["status"], "complete")
            self.assertFalse(self._landing_path(receipt_path).exists())
            self.assertIn("absent or invalid means unknown", durable["landing_verdict_source"])

    def _finish_after_total_with_verified_postflight(self, *, cleanup_uncertain: bool):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()
            started = 10_000_000_000
            now = [started]

            real_hash = receipts._sha256
            config_hash_calls = []

            def last_postflight_hash(path, **kwargs):
                digest = real_hash(path, **kwargs)
                if path == config_path:
                    config_hash_calls.append(1)
                    if len(config_hash_calls) == 2:
                        # All integrity evidence remains verified; only final work completion
                        # crosses the total. Do not accidentally test an integrity failure.
                        now[0] = started + stage.TOTAL_NS + 1
                return digest

            def controlled_result(_argv, **kwargs):
                result = self._complete_result(kwargs["plan"])
                if cleanup_uncertain:
                    return dataclasses.replace(
                        result, status="cleanup_uncertain", reason="controlled cleanup uncertainty",
                        returncode=None, group_alive_at_return=True, cleanup_uncertain=True,
                    )
                return result

            with mock.patch.object(receipts, "_sha256", last_postflight_hash):
                result = receipts.run_receipted_stage(
                    config_path, expected, receipt_path, clock=lambda: now[0],
                    repo_reader=repo_reader, disk_reader=self._disk,
                    supervise=controlled_result, install_limits=False,
                )
            sidecar = json.loads(self._landing_path(receipt_path).read_text(encoding="utf-8"))
            self.assertEqual(config_hash_calls, [1, 1])
            return result, sidecar

    def test_work_finish_after_total_is_marked_deadline_overrun(self):
        result, sidecar = self._finish_after_total_with_verified_postflight(cleanup_uncertain=False)
        self.assertTrue(result["deadline_overrun"])
        self.assertEqual(result["status"], "deadline_overrun")
        self.assertFalse(sidecar["within_total_deadline"])
        self.assertEqual(sidecar["work_status"], "deadline_overrun")

    def test_cleanup_uncertain_status_survives_a_simultaneous_deadline_overrun(self):
        result, sidecar = self._finish_after_total_with_verified_postflight(cleanup_uncertain=True)
        self.assertTrue(result["deadline_overrun"])
        self.assertEqual(result["status"], "cleanup_uncertain")
        self.assertTrue(result["process"]["group_alive_at_return"])
        self.assertTrue(result["process"]["cleanup_uncertain"])
        self.assertEqual(sidecar["work_status"], "cleanup_uncertain")
        self.assertFalse(sidecar["within_total_deadline"])

    def test_term_ignoring_child_is_killed_at_cleanup_cutoff_and_never_complete(self):
        class FakeClock:
            def __init__(self, start_ns: int):
                self.now_ns = start_ns

            def __call__(self) -> int:
                return self.now_ns

            def sleep(self, delay_ns: int) -> None:
                self.now_ns += delay_ns

        class StubbornProcess:
            pid = 12345

            @staticmethod
            def poll() -> None:
                return None

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config_path, receipt_path, _config, repo_reader = self._config(root)
            expected = hashlib.sha256(config_path.read_bytes()).hexdigest()
            clock = FakeClock(10_000_000_000)
            signals: list[int] = []

            def stubborn_supervisor(command, **kwargs):
                return stage.supervise(
                    command,
                    plan=kwargs["plan"],
                    clock=kwargs["clock"],
                    popen_factory=lambda *_args, **_kwargs: StubbornProcess(),
                    group_alive=lambda _pgid: True,
                    rss_reader=lambda _pgid: 1,
                    signal_group=lambda _pgid, sig: signals.append(sig),
                    sleep_ns=clock.sleep,
                    sample_hook=kwargs["sample_hook"],
                    kill_cutoff_ns=kwargs["kill_cutoff_ns"],
                    install_limits=False,
                )

            with mock.patch.object(stage, "group_cpu_ticks", lambda _pgid: (0, 0)):
                result = receipts.run_receipted_stage(
                    config_path,
                    expected,
                    receipt_path,
                    clock=clock,
                    repo_reader=repo_reader,
                    disk_reader=self._disk,
                    supervise=stubborn_supervisor,
                    install_limits=False,
                )
            process = result["process"]
            sidecar = json.loads(self._landing_path(receipt_path).read_text(encoding="utf-8"))
            self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
            self.assertEqual(process["term_sent_ns"], process["term_ns"])
            self.assertEqual(process["kill_sent_ns"], process["total_ns"] - receipts.EVIDENCE_RESERVE_NS)
            self.assertTrue(process["group_alive_at_return"])
            self.assertTrue(process["cleanup_uncertain"])
            self.assertNotEqual(result["status"], "complete")
            self.assertTrue(sidecar["within_total_deadline"])

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
            binding = result["preflight"]["input_binding"]
            self.assertEqual(binding["status"], "verified")
            self.assertTrue(binding["same_file"])
            self.assertEqual(binding["learn_resolved"], str((root / "repo" / "data" / "passage.bin").resolve()))
            self.assertEqual(result["postflight"]["input_binding"], binding)
            output_dir = Path(result["output_dir"])
            self.assertEqual((output_dir / "env.txt").read_text(encoding="utf-8"), "|1")
            consumed = json.loads((output_dir / "consumed.json").read_text(encoding="utf-8"))
            self.assertEqual(consumed["path"], binding["learn_resolved"])
            self.assertEqual(consumed["sha256"], binding["input_pin_sha256"])
            self.assertEqual(consumed["content"], "synthetic input marker\n")
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
