"""Fixture checks for the private F5 blind judging surface; contains no source data."""
from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path

from athena_blind import (BlindError, mark, prepare, unblind)


def _private(path: Path, data: bytes) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    path.write_bytes(data)
    os.chmod(path, 0o600)


def _fixture() -> dict:
    return {
        "schema": "holonics.athena-blind-input.v1",
        "coordinate_order": ["response:request-2", "response:request-9"],
        "cases": [
            {"coordinate": "response:request-9", "request": "Question nine?",
             "context": "Declared context nine.", "grain": "conversation turn",
             "responses": {"athena": {"label": "PRIVATE_ATHENA_LABEL", "text": "Candidate A nine."},
                           "control": {"label": "PRIVATE_CONTROL_LABEL", "text": "Candidate B nine."}}},
            {"coordinate": "response:request-2", "request": "Question two?",
             "context": "Declared context two.", "grain": "conversation turn",
             "responses": {"athena": {"label": "PRIVATE_ATHENA_LABEL", "text": "Candidate A two."},
                           "control": {"label": "PRIVATE_CONTROL_LABEL", "text": "Candidate B two."}}},
        ],
    }


class BlindSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.input = self.root / "source.json"
        self.seed = self.root / "seed"
        _private(self.input, json.dumps(_fixture(), ensure_ascii=False).encode())
        _private(self.seed, b"fixture-only-secret-seed")

    def tearDown(self):
        self.tmp.cleanup()

    def _prepare(self, dest: Path) -> Path:
        package = dest / "cases.json"
        prepare(self.input, self.seed, package)
        return package

    def test_order_is_reproducible_for_same_seed_and_pinned_coordinate_order(self):
        first = self._prepare(self.root / "first")
        second = self._prepare(self.root / "second")
        self.assertEqual(first.read_bytes(), second.read_bytes())
        package = json.loads(first.read_bytes())
        self.assertEqual(["response:request-2", "response:request-9"],
                         [case["coordinate"] for case in package["cases"]])
        self.assertEqual(package["cases"], json.loads(second.read_bytes())["cases"])

    def test_premark_package_contains_no_source_labels_or_key(self):
        package_path = self._prepare(self.root / "premark")
        raw = package_path.read_bytes()
        self.assertNotIn(b"PRIVATE_ATHENA_LABEL", raw)
        self.assertNotIn(b"PRIVATE_CONTROL_LABEL", raw)
        package = json.loads(raw)
        self.assertEqual({"schema", "seed_commitment", "input_sha256", "cases"}, set(package))
        self.assertNotIn("seed", package)
        self.assertNotIn("sources", package)
        self.assertEqual(0o700, os.stat(package_path.parent).st_mode & 0o777)
        self.assertEqual(0o600, os.stat(package_path).st_mode & 0o777)

    def test_incomplete_marks_refuse_unblind_without_key(self):
        package = self._prepare(self.root / "incomplete")
        marks = package.parent / "marks.json"
        key = package.parent / "unblinding-key.json"
        mark(package, marks, "response:request-2", "answers", "fails", "left")
        with self.assertRaisesRegex(BlindError, "all case marks"):
            unblind(self.input, self.seed, package, marks, key)
        self.assertFalse(key.exists())
        self.assertEqual(0o600, os.stat(marks).st_mode & 0o777)

    def test_complete_marks_unblind_and_recover_source_labels(self):
        package = self._prepare(self.root / "complete")
        marks = package.parent / "marks.json"
        key_path = package.parent / "unblinding-key.json"
        mark(package, marks, "response:request-2", "answers", "fails", "left")
        mark(package, marks, "response:request-9", "justified-refusal", "answers", "tie")
        receipt = unblind(self.input, self.seed, package, marks, key_path)
        key = json.loads(key_path.read_bytes())
        self.assertEqual(2, receipt["unblinded"])
        self.assertEqual("holonics.athena-blind-key.v1", key["schema"])
        self.assertEqual(2, len(key["sources"]))
        all_sources = {label for item in key["sources"]
                       for label in (item["left_source"], item["right_source"])}
        self.assertEqual({"PRIVATE_ATHENA_LABEL", "PRIVATE_CONTROL_LABEL"}, all_sources)
        self.assertTrue(all(item["left_source"] != item["right_source"] for item in key["sources"]))
        self.assertEqual(0o600, os.stat(key_path).st_mode & 0o777)

    def test_marks_are_single_file_and_duplicate_coordinate_is_refused(self):
        package = self._prepare(self.root / "strict")
        marks = package.parent / "marks.json"
        mark(package, marks, "response:request-2", "answers", "fails", "left")
        with self.assertRaisesRegex(BlindError, "already has a committed"):
            mark(package, marks, "response:request-2", "answers", "fails", "left")
        files = sorted(path.name for path in package.parent.iterdir())
        self.assertEqual(["cases.json", "marks.json"], files)


if __name__ == "__main__":
    unittest.main()
