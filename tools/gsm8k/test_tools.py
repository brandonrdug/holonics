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


    def test_written_rules_read_never_met_sums_on_their_rings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            held = root / "held.txt"
            held.write_bytes(b"Q?\nA <<12+30=42>>42 <<50-8=42>>42 <<7+7=14>>14 <<2*3=6>>6 <<9+2=11>>11\n\n")
            train = root / "train.txt"
            train.write_bytes(b"Q?\nA <<1+1=2>>2\n\n")
            release = root / "release"
            release.mkdir()
            (release / "FREE.tsv").write_text("0\tA\\n\n")
            (release / "MARKS.tsv").write_text(
                "0\t0\t12+30\t42>>\n0\t1\t50-8\t53>>\n0\t2\t7+7\t24>>\n0\t3\t2*3\t6>>\n0\t4\t9+2\t1\n"
            )
            out = run("written_rules.py", held, train, "rings", release).splitlines()
            # Written 42, 53, 24 and an unfinished 1 against exact 42, 42, 14, 11 (differences 0,
            # 11, 10); the foil reads 53, 24, the unfinished one and 42 against them (11, 18, -, 31).
            self.assertEqual(
                out[1],
                f"RINGS dir={release} n=4 mod9=1 foil9=1 mod10=2 foil10=0 mod11=2 foil11=1 mod990=1 foil990=0",
            )


    def test_written_rules_read_how_far_each_wrong_value_falls_and_what_it_was_written_from(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            held = root / "held.txt"
            held.write_bytes(
                b"Q?\nA <<12+30=42>>42 <<50-8=42>>42 <<7+7=14>>14 <<2*3=6>>6 <<9+2=11>>11 "
                b"<<300*4=1200>>1200\n\n"
            )
            train = root / "train.txt"
            train.write_bytes(b"Q?\nA <<1+1=2>>2 <<3+4=7>>7 <<2*3=6>>6\n\n")
            release = root / "release"
            release.mkdir()
            (release / "FREE.tsv").write_text("0\tA\\n\n")
            (release / "MARKS.tsv").write_text(
                "0\t0\t12+30\t24>>\n0\t1\t50-8\t58>>\n0\t2\t7+7\t7>>\n0\t3\t2*3\t6>>\n"
                "0\t4\t9+2\t1\n0\t5\t300*4\tabc>>\n"
            )
            out = run("written_rules.py", held, train, "gaps", release).splitlines()
            # Written 24, 58 and 7 against 42, 42 and 14; the foil reads them against the next
            # wrong number's exact value, 42, 14 and 42. 58 is 50+8 and 7 an operand and heard.
            self.assertEqual(out[1:7], [
                f"GAPS dir={release} set=all n=6 right=1 wrong=5 unfinished=1 not_number=1 unread=0 numbers=3",
                f"GAP_SIZE dir={release} set=all n=3 x2=3 x10=3 tenth=0 opposite_sign=0 smaller=2 larger=1 "
                "digits=2 foil_digits=2/3",
                f"GAP_RINGS dir={release} set=all n=3 mod9=1 foil9=1/3 mod10=0 foil10=0/3 mod11=0 foil11=1/3 "
                "mod7=1 foil7=1/3 mod13=0 foil13=0/3",
                f"GAP_FROM dir={release} set=all n=3 heard_result=1 operand=1 other_operation=1/3",
                f"GAP_WRITES dir={release} set=all written=4 distinct=4 top10=4 commonest=24:1:0",
                f"GAP_LENGTH dir={release} set=all 1=1/1 2=0/4 3=0/0 4=0/1 5+=0/0",
            ])
            self.assertEqual(out[7], f"GAPS dir={release} set=met n=1 right=1 wrong=0 unfinished=0 not_number=0 unread=0 numbers=0")
            self.assertEqual(out[13], f"GAPS dir={release} set=never n=5 right=0 wrong=5 unfinished=1 not_number=1 unread=0 numbers=3")


    def test_numeral_rings_name_the_last_digit_of_each_whole_numeral(self):
        spec = importlib.util.spec_from_file_location("numeral_rings", TOOLS / "numeral_rings.py")
        rings = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(rings)
        text = b"Pay 120 or 1,500 now?\nIt is <<120*3=360>>360 and 2.500 or 45\n\nQ 1000?\nA 7\n\n"
        # Framed: a blank line, the question and its line end, then the answer. 1,500 and 2.500 are
        # not whole numerals of three digits, 45 and 7 are too short.
        framed = b"\n\nPay 120 or 1,500 now?\nIt is <<120*3=360>>360 and 2.500 or 45\n"
        found = rings.named("numerals", text)
        self.assertEqual([(i, framed[b - 2 : b + 1] if i == 0 else None, v["numeral"]) for i, b, v in found],
                         [(0, b"120", 120), (0, b"120", 120), (0, b"360", 360), (0, b"360", 360), (1, None, 1000)])
        self.assertEqual(found[-1][1], len(b"\n\nQ 1000") - 1)
        # The equals of a two-numeral sum or difference only: 120*3 is a product.
        text = b"Q?\nA <<12+30=42>>42 <<120*3=360>>360 <<50-8=42>>42 <<1.5+2=3.5>>\n\n"
        framed = b"\n\nQ?\nA <<12+30=42>>42 <<120*3=360>>360 <<50-8=42>>42 <<1.5+2=3.5>>\n"
        found = rings.named("equals", text)
        self.assertEqual([(framed[b - 5 : b + 1], v) for _, b, v in found],
                         [(b"12+30=", {"a": 12, "b": 30, "result": 42}), (b"<50-8=", {"a": 50, "b": 8, "result": 42})])

if __name__ == "__main__":
    unittest.main()
