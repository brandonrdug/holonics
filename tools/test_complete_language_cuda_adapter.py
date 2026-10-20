"""Synthetic command/receipt/ownership controls; no dataset or model process."""
import copy
import unittest
import tempfile
import time
from unittest.mock import patch
from pathlib import Path
from complete_language_v92_repair_regression import commands
from complete_language_cuda_guard import classify, verify_card_receipt, run_gpu_training


class CudaAdapterControls(unittest.TestCase):
    def test_training_card_and_all_sixteen_host_outputs_share_fixed_inputs(self):
        plan = {"binary": "HOST", "backend": "host-reference", "data_root": "/prepared",
                "files": {name: {"absolute": "/prepared/" + name, "sha256": name}
                    for name in ("train-five-pass.bin", "causal-cuts.tsv", "public-keys.bin")},
                "prompts": [{"row": row, "path": str(row), "sha256": str(row)}
                    for row in (2348, 6469, 1026, 1077)]}
        old_train, old_samples = commands(plan, Path("/out"))
        card = copy.deepcopy(plan)
        card.update(training_binary="CARD", training_backend="cuda-observed-epoch-device0",
                    output_backend="host-reference", backend="cuda-assisted-training-host-evaluation")
        train, samples = commands(card, Path("/out"))
        self.assertEqual(train[0], "CARD")
        self.assertEqual(train[3], "cuda-observed-epoch-device0")
        self.assertEqual(train[4:], old_train[4:])
        self.assertEqual(samples, old_samples)
        self.assertEqual(len(samples), 16)
        self.assertTrue(all(x["argv"][0] == "HOST" and x["argv"][3] == "host-reference" for x in samples))

    def test_actual_card_return_and_statistics_are_required(self):
        good = {"backend": "cuda-observed-epoch-device0", "device_ordinal": 0,
                "host_fallback": False, "completed": True, "successful_card_forwards": 20,
                "successful_retained_card_returns": 20, "successful_card_aggregates": 3}
        verify_card_receipt(good)
        for key, value in (("successful_card_forwards", 0), ("successful_retained_card_returns", 0),
                           ("successful_card_aggregates", 0), ("host_fallback", True),
                           ("device_ordinal", 1), ("completed", False)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify_card_receipt(dict(good, **{key: value}))

    def test_only_own_group_is_owned_and_display_utilization_is_not_a_gate(self):
        rows = [{"pid": 1, "memory_MiB": 280}, {"pid": 2, "memory_MiB": 10}]
        own, foreign = classify(rows, 100, lambda pid: {1: 100, 2: 200}[pid])
        self.assertEqual(own, rows[:1])
        self.assertEqual(foreign, rows[1:])
        self.assertEqual(classify([], 100), ([], []))

    def test_unavailable_or_busy_card_never_launches_a_host_or_card_child(self):
        for result in (RuntimeError("host visibility unavailable"), [{"pid": 123, "memory_MiB": 280}]):
            with self.subTest(result=result), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                lock = root / "gpu.lock"
                lock.touch()
                guard = {"device_ordinal": 0, "own_sampled_memory_limit_MiB": 2048,
                         "graphics_allowed": True, "foreign_compute_allowed": False,
                         "project_lock": str(lock)}
                with patch("complete_language_cuda_guard.compute_apps", side_effect=(result if isinstance(result, Exception) else None),
                           return_value=result), patch("complete_language_cuda_guard.subprocess.Popen") as launch:
                    with self.assertRaises(RuntimeError):
                        run_gpu_training(["MUST_NOT_LAUNCH"], root / "training.log",
                                         time.monotonic_ns() + 1_000_000_000, guard)
                    launch.assert_not_called()
                self.assertTrue((root / "training.gpu-guard.json").exists())


if __name__ == "__main__":
    unittest.main()
