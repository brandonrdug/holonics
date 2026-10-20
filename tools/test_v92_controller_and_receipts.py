"""Bounded synthetic controls for the V92 phase projection and receipt refusals."""
import json
from pathlib import Path
import tempfile
import unittest

from complete_language_v92_repair_regression import (
    verify_output_receipt,
    verify_training_receipts,
)
from rate_guard_v92 import training_projection, validate_v92_budget


class V92TrainingRateControls(unittest.TestCase):
    def test_projection_uses_explicit_1128_epoch_1800s_boundary(self):
        exact = training_projection(
            "complete-language epoch=1128 cells=11280 elapsed_ns=1800000000000 backend=host-reference",
            epochs=1128, phase_ns=1_800_000_000_000)
        self.assertEqual(exact["projected_training_ns"], 1_800_000_000_000)
        self.assertFalse(exact["exceeds_cap"])
        over = training_projection(
            "complete-language epoch=1128 cells=11280 elapsed_ns=1800000000001 backend=host-reference",
            epochs=1128, phase_ns=1_800_000_000_000)
        self.assertTrue(over["exceeds_cap"])
        self.assertIsNone(training_projection("no completed epoch", epochs=1128,
                                              phase_ns=1_800_000_000_000))

    def test_controller_rejects_phase_or_resource_drift(self):
        config = {
            "total_reservation_ns": 2_400_000_000_000,
            "maximum_process_ns": 2_390_000_000_000,
            "maximum_cleanup_ns": 10_000_000_000,
            "training_phase_ns": 1_800_000_000_000,
            "evaluation_phase_ns": 500_000_000_000,
            "receipts_phase_ns": 90_000_000_000,
            "training_epochs": 1128,
            "cpus": 4,
            "memory_bytes": 8_589_934_592,
        }
        self.assertTrue(validate_v92_budget(config))
        for key, value in (("training_phase_ns", 1_500_000_000_000),
                           ("cpus", 8), ("memory_bytes", 16_000_000_000),
                           ("total_reservation_ns", 2_500_000_000_000)):
            changed = dict(config, **{key: value})
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_v92_budget(changed)


class V92ReceiptControls(unittest.TestCase):
    def test_training_receipt_workers_and_law_are_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "CLOCK_CONTRACT.json").write_text(json.dumps({"actual_rayon_workers": 4}))
            (root / "TRAINING_COMPLETE.json").write_text(json.dumps({
                "actual_rayon_workers": 4, "receiving_law": "retained-fibre-v1",
                "accepted_cells": 11280, "actual_epochs": 1128,
            }))
            verify_training_receipts(root)
            for receipt_name, bad in (
                ("CLOCK_CONTRACT.json", {"actual_rayon_workers": 1}),
                ("CLOCK_CONTRACT.json", {}),
                ("TRAINING_COMPLETE.json", {"actual_rayon_workers": 4,
                    "receiving_law": "coarse-grain-v1", "accepted_cells": 11280,
                    "actual_epochs": 1128}),
                ("TRAINING_COMPLETE.json", {"receiving_law": "retained-fibre-v1",
                    "accepted_cells": 11280, "actual_epochs": 1128}),
            ):
                old = (root / receipt_name).read_text()
                (root / receipt_name).write_text(json.dumps(bad))
                with self.subTest(receipt=receipt_name, bad=bad), self.assertRaises(ValueError):
                    verify_training_receipts(root)
                (root / receipt_name).write_text(old)

    def test_output_receipt_requires_worker_law_and_fresh_opening(self):
        valid = {"actual_rayon_workers": 1, "receiving_law": "retained-fibre-v1",
                 "opening_accepted_cells": 0}
        verify_output_receipt(valid, "fresh-native")
        verify_output_receipt(valid, "native")
        for bad in (
            {"receiving_law": "retained-fibre-v1", "opening_accepted_cells": 0},
            {"actual_rayon_workers": 4, "receiving_law": "retained-fibre-v1",
             "opening_accepted_cells": 0},
            {"actual_rayon_workers": 1, "receiving_law": "coarse-grain-v1",
             "opening_accepted_cells": 0},
            {"actual_rayon_workers": 1, "receiving_law": "retained-fibre-v1",
             "opening_accepted_cells": 1},
            {"actual_rayon_workers": 1, "receiving_law": "retained-fibre-v1"},
        ):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                verify_output_receipt(bad, "fresh-native")


if __name__ == "__main__":
    unittest.main()
