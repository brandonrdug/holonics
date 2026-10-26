"""Synthetic exterior-contract tests; no dataset or model is required."""
import importlib.util
import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parent


def run(name, *args):
    return subprocess.check_output(
        [sys.executable, "-I", str(TOOLS / name), *map(str, args)], text=True
    )


def sections(path):
    data = path.read_bytes()
    assert data[:6] == b"HLSN1\n"
    at = 6
    result = []
    while at < len(data):
        assert struct.unpack_from(">I", data, at)[0] == 1
        at += 4
        assert data[at] == 0
        at += 1
        n = struct.unpack_from(">I", data, at)[0]
        at += 4
        question = data[at:at + n]
        at += n
        n = struct.unpack_from(">I", data, at)[0]
        at += 4
        target = data[at:at + n]
        at += n
        result.append((question, target))
    assert at == len(data)
    return result


class ExteriorTools(unittest.TestCase):
    def test_partition_keeps_normalized_questions_together(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rows = [{"question": q, "answer": "#### 1"} for q in
                    ["Ａ  b", "a B", "third", "fourth", "fifth", "sixth"]]
            source = root / "train.jsonl"
            source.write_text("\n".join(map(json.dumps, rows)))
            target = root / "partition.json"
            run("partition.py", source, target)
            partition = json.loads(target.read_text())
            train, dev = map(set, (partition["train_indices"], partition["dev_indices"]))
            self.assertFalse(train & dev)
            self.assertEqual(train | dev, set(range(len(rows))))
            self.assertEqual(0 in dev, 1 in dev)
            original = target.read_bytes()
            run("partition.py", source, target)
            self.assertEqual(original, target.read_bytes())

    def test_framing_excludes_development_answers_from_release(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rows = [{"question": "train?", "answer": "#### 1"},
                    {"question": "dev?", "answer": "unique solution #### 2"}]
            source = root / "train.jsonl"
            source.write_text("\n".join(map(json.dumps, rows)))
            partition = root / "partition.json"
            partition.write_text(json.dumps({"train_indices": [0], "dev_indices": [1]}))
            run("frame_gsm8k.py", source, partition, root)
            self.assertEqual(sections(root / "learn.hlsn"), [(b"train?", b"#### 1")])
            self.assertEqual(sections(root / "development_release.hlsn"), [(b"dev?", b"")])
            self.assertEqual(sections(root / "development_read.hlsn"),
                             [(b"dev?", b"unique solution #### 2")])


    def test_written_rules_read_an_expression_outside_their_grammar_as_none(self):
        spec = importlib.util.spec_from_file_location("written_rules", TOOLS / "written_rules.py")
        rules = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(rules)
        self.assertEqual(rules.value("2*12"), 24)
        self.assertIsNone(rules.value("8(2/3)"))
        self.assertIsNone(rules.value("2**3"))

    def test_written_rules_bin_each_calculation_by_its_hearings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            held = root / "held.txt"
            held.write_bytes(b"Two and three?\nSum <<2+3=5>>5 then <<5*4=20>>20\n\n")
            train = root / "train.txt"
            train.write_bytes(b"Q?\nA <<2+3=5>>5\n\nQ?\nB <<2+3=5>>5 <<5*4=21>>\n\n")
            release = root / "release"
            release.mkdir()
            (release / "FREE.tsv").write_text("0\tSum\\n\n")
            (release / "MARKS.tsv").write_text("0\t0\t2+3\t5>>\n0\t1\t5*4\t21>>\n")
            out = run("written_rules.py", held, train, "heard", release).splitlines()
            self.assertIn("met=1/1 never_met=0/1", out[0])
            self.assertEqual(out[1], f"HEARD dir={release} 0=0/1 1=0/0 2-3=1/1 4-7=0/0 8-15=0/0 16+=0/0")


if __name__ == "__main__":
    unittest.main()
