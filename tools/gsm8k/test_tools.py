"""Synthetic exterior-contract tests; no dataset or model is required."""
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



if __name__ == "__main__":
    unittest.main()
