"""Tests of tools/copy_length.py, the exterior copy-length receipt.

    python3 -m unittest tools/test_copy_length.py

Every input is synthetic. The reference is the quadratic definition: the longest common substring
of the release and one passage file, and the bytes covered by windows of K release bytes that
occur in one passage file.
"""

import contextlib
import io
import json
import os
import random
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import copy_length as cl  # noqa: E402


class Case(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.count = 0

    def file(self, data):
        self.count += 1
        path = os.path.join(self.dir.name, f"f{self.count}")
        with open(path, "wb") as handle:
            handle.write(data)
        return path

    def run_tool(self, release, passages, min_run=8, **kw):
        return cl.copy_length(release, [self.file(p) for p in passages], min_run, **kw)

    def cli(self, release, passages, *extra):
        argv = ["--release", self.file(release), "--passage"]
        argv += [self.file(p) for p in passages]
        argv += list(extra)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(cl.main(argv), 0)
        return out.getvalue()


def reference(release, passages, min_run):
    """(copy length, release start, file index, covered count) from the definition."""
    longest, start, index = 0, -1, -1
    covered = set()
    for f, passage in enumerate(passages):
        for a in range(len(release)):
            for b in range(a + 1, len(release) + 1):
                if release[a:b] not in passage:
                    break
                if (-(b - a), a, f) < (-longest, start if longest else a, index):
                    longest, start, index = b - a, a, f
        for a in range(len(release) - min_run + 1):
            if release[a:a + min_run] in passage:
                covered.update(range(a, a + min_run))
    return longest, start, index, len(covered)


class Overlap(Case):
    def test_no_overlap_is_zero(self):
        r = self.run_tool(b"abcdef", [b"uvwxyz", b"ghijkl"])
        self.assertEqual(r["copy_length"], 0)
        self.assertEqual(
            (r["release_start"], r["passage_file"], r["passage_offset"], r["covered_bytes"]),
            (-1, -1, -1, 0))
        self.assertEqual(r["release_bytes"], 6)
        self.assertEqual(r["passage_bytes"], 12)

    def test_release_inside_passage(self):
        passage = b"the quick brown fox jumps over the lazy dog"
        release = b"brown fox jumps"
        r = self.run_tool(release, [passage])
        self.assertEqual(r["copy_length"], len(release))
        self.assertEqual((r["release_start"], r["passage_file"]), (0, 0))
        self.assertEqual(r["passage_offset"], passage.index(release))
        self.assertEqual(r["covered_bytes"], len(release))

    def test_passage_inside_release_and_embedded_run(self):
        run = b"0123456789"
        r = self.run_tool(b"XX" + run + b"YYY", [b"aa" + run + b"bb"])
        self.assertEqual(r["copy_length"], len(run))
        self.assertEqual((r["release_start"], r["passage_offset"]), (2, 2))
        r = self.run_tool(b"abc", [b"zzabcdefzz"])
        self.assertEqual(r["copy_length"], 3)

    def test_identical_release_and_passage(self):
        data = bytes(random.Random(1).randrange(256) for _ in range(500))
        r = self.run_tool(data, [data])
        self.assertEqual(r["copy_length"], 500)
        self.assertEqual(r["covered_bytes"], 500)

    def test_a_run_never_spans_two_passage_files(self):
        # "abcdef" is in the release; "abc" ends file 0 and "def" begins file 1.
        r = self.run_tool(b"..abcdef..", [b"xxabc", b"defyy"], min_run=4)
        self.assertEqual(r["copy_length"], 3)
        self.assertEqual((r["release_start"], r["passage_file"]), (2, 0))
        self.assertEqual(r["covered_bytes"], 0)
        # The same text as one file is a run of six.
        r = self.run_tool(b"..abcdef..", [b"xxabcdefyy"], min_run=4)
        self.assertEqual(r["copy_length"], 6)
        self.assertEqual(r["covered_bytes"], 6)

    def test_ties_take_the_earliest_release_start_then_the_first_file(self):
        r = self.run_tool(b"QQabQQcd", [b"xxcdxx", b"yyabyy"], min_run=2)
        self.assertEqual((r["copy_length"], r["release_start"], r["passage_file"]), (2, 2, 1))
        r = self.run_tool(b"abcd", [b"zzcdzz", b"zzabzz"], min_run=2)
        self.assertEqual((r["release_start"], r["passage_file"]), (0, 1))
        r = self.run_tool(b"abcd", [b"zzabzz", b"zzabzz"], min_run=2)
        self.assertEqual(r["passage_file"], 0)

    def test_the_longest_run_is_found_over_all_files(self):
        r = self.run_tool(b"abc-defgh", [b"abc", b"defgh"], min_run=3)
        self.assertEqual((r["copy_length"], r["release_start"], r["passage_file"]), (5, 4, 1))

    def test_first_offset_in_the_passage(self):
        r = self.run_tool(b"ab", [b"xxabyyab"])
        self.assertEqual(r["passage_offset"], 2)


class Bytes(Case):
    def test_multibyte_runs_count_in_bytes(self):
        r = self.run_tool("日本語".encode(), ["日本人".encode()])
        self.assertEqual(r["copy_length"], 6)  # 日本 is 3 + 3 bytes
        r = self.run_tool("é".encode(), ["é".encode()])
        self.assertEqual(r["copy_length"], 2)

    def test_a_run_may_end_inside_a_character(self):
        # é = C3 A9 and è = C3 A8 share the lead byte only.
        r = self.run_tool("é".encode(), ["è".encode()])
        self.assertEqual(r["copy_length"], 1)
        # 本 = E6 9C AC and 木 = E6 9C A8 share two bytes of three.
        r = self.run_tool("本".encode(), ["木".encode()])
        self.assertEqual(r["copy_length"], 2)

    def test_a_run_may_start_inside_a_character(self):
        # ü = C3 BC and ö = C3 B6 share only C3; the suffix of the lead-in is distinct.
        r = self.run_tool(b"\xbc" + b"abc", ["ä".encode() + b"\xbcabc"])
        self.assertEqual(r["copy_length"], 4)  # BC 61 62 63

    def test_all_byte_values(self):
        data = bytes(range(256)) * 2
        r = self.run_tool(data, [bytes(range(256))])
        self.assertEqual(r["copy_length"], 256)


class Coverage(Case):
    def release(self):
        # Two copied runs (10 and 8 bytes) separated by novel bytes.
        a, b = b"ABCDEFGHIJ", b"klmnopqr"
        return b"1234" + a + b"5678" + b + b"90", [b"zz" + a + b"zz" + b"yy" + b + b"yy"]

    def test_covered_by_runs_of_at_least_k(self):
        # The digits are novel, so the covered count is the runs of length >= K: both (18) for
        # K <= 8, only the 10-run for K = 9 and 10, none above.
        release, passages = self.release()
        for k, expect in [(1, 18), (8, 18), (9, 10), (10, 10), (11, 0)]:
            r = self.run_tool(release, passages, min_run=k)
            self.assertEqual(r["covered_bytes"], expect, f"K={k}")
            self.assertEqual(r["copy_length"], 10)

    def test_default_threshold_is_eight(self):
        release, passages = self.release()
        argv_out = self.cli(release, passages)
        self.assertIn("min_run 8", argv_out)
        self.assertIn("covered_bytes 18", argv_out)

    def test_short_runs_do_not_count(self):
        r = self.run_tool(b"a-b-c-d", [b"abcd"], min_run=2)
        self.assertEqual(r["copy_length"], 1)
        self.assertEqual(r["covered_bytes"], 0)
        r = self.run_tool(b"a-b-c-d", [b"abcd"], min_run=1)
        self.assertEqual(r["covered_bytes"], 4)

    def test_coverage_is_the_union_across_files(self):
        # File 0 holds bytes 0..5 of the release and file 1 holds bytes 3..8: the union is 9.
        release = b"abcdefghi"
        r = self.run_tool(release, [b"..abcdef..", b"..defghi.."], min_run=4)
        self.assertEqual(r["covered_bytes"], 9)
        self.assertEqual(r["copy_length"], 6)

    def test_overlapping_runs_in_one_file_are_not_double_counted(self):
        release = b"abcabcabc"
        r = self.run_tool(release, [b"abcabc"], min_run=3)
        self.assertEqual(r["covered_bytes"], 9)

    def test_threshold_must_be_positive(self):
        with self.assertRaises(ValueError):
            cl.copy_length(b"abc", [], 0)


class Empty(Case):
    def test_empty_release(self):
        r = self.run_tool(b"", [b"abc"])
        self.assertEqual((r["copy_length"], r["covered_bytes"], r["release_bytes"]), (0, 0, 0))
        self.assertEqual(r["passage_bytes"], 3)

    def test_empty_passage(self):
        r = self.run_tool(b"abc", [b""])
        self.assertEqual((r["copy_length"], r["covered_bytes"], r["passage_bytes"]), (0, 0, 0))
        self.assertEqual(r["release_start"], -1)

    def test_empty_both_and_no_passage(self):
        r = self.run_tool(b"", [b""])
        self.assertEqual(r["copy_length"], 0)
        self.assertEqual(cl.copy_length(b"abc", [], 2)["copy_length"], 0)

    def test_an_empty_file_among_others(self):
        r = self.run_tool(b"hello world", [b"", b"say hello", b""])
        self.assertEqual((r["copy_length"], r["passage_file"]), (5, 1))


class Streaming(Case):
    def test_chunk_size_does_not_change_the_result(self):
        rng = random.Random(7)
        passage = bytes(rng.choice(b"ab") for _ in range(300))
        release = bytes(rng.choice(b"ab") for _ in range(60)) + passage[100:140]
        whole = self.run_tool(release, [passage], 4)
        for size in (1, 2, 3, 7, 50, 1000):
            self.assertEqual(self.run_tool(release, [passage], 4, chunk_size=size), whole)

    def test_a_run_across_a_chunk_boundary(self):
        passage = b"xx" + b"0123456789" + b"yy"
        r = self.run_tool(b"-0123456789-", [passage], 4, chunk_size=3)
        self.assertEqual(r["copy_length"], 10)


class Brute(Case):
    def test_against_the_quadratic_definition(self):
        rng = random.Random(20261005)
        for trial in range(250):
            alphabet = rng.choice([b"ab", b"abc", b"abcdefgh", bytes(range(200, 256))])
            release = bytes(rng.choice(alphabet) for _ in range(rng.randrange(0, 40)))
            passages = [bytes(rng.choice(alphabet) for _ in range(rng.randrange(0, 60)))
                        for _ in range(rng.randrange(0, 4))]
            k = rng.randrange(1, 7)
            longest, start, index, covered = reference(release, passages, k)
            r = self.run_tool(release, passages, k, chunk_size=rng.randrange(1, 20))
            self.assertEqual(
                (r["copy_length"], r["release_start"], r["passage_file"], r["covered_bytes"]),
                (longest, start, index, covered),
                f"trial {trial}: release={release!r} passages={passages!r} k={k}")
            if longest:
                run = release[start:start + longest]
                self.assertEqual(r["passage_offset"], passages[index].find(run))


class Cli(Case):
    def test_plain_output_is_integers_only(self):
        out = self.cli(b"hello brave new world", [b"say hello brave friends"], "--min-run", "5")
        pairs = [line.split(" ") for line in out.splitlines()]
        self.assertEqual([p[0] for p in pairs], [
            "copy_length", "release_start", "passage_file", "passage_offset",
            "covered_bytes", "min_run", "release_bytes", "passage_bytes"])
        values = {k: int(v) for k, v in pairs}  # every value parses as an integer
        self.assertEqual(values["copy_length"], 12)  # "hello brave "
        self.assertEqual(values["release_start"], 0)
        self.assertEqual(values["passage_offset"], 4)
        self.assertEqual(values["min_run"], 5)

    def test_passage_text_and_paths_are_not_printed_by_default(self):
        secret = b"a private passage sentence about nothing"
        out = self.cli(b"x " + secret + b" y", [secret])
        self.assertNotIn("private", out)
        self.assertNotIn(self.dir.name, out)
        self.assertFalse([l for l in out.splitlines() if l.startswith("run ")])

    def test_show_prints_the_longest_run(self):
        out = self.cli(b"xx private run yy", [b"aa private run bb"], "--show")
        self.assertIn('run " private run "', out)

    def test_show_escapes_newlines_and_invalid_bytes(self):
        out = self.cli(b"\xffab\ncd", [b"\xffab\ncd"], "--show")
        run_line = [line for line in out.splitlines() if line.startswith("run ")]
        self.assertEqual(len(run_line), 1)
        self.assertIn("\\n", run_line[0])

    def test_json(self):
        out = self.cli(b"abcdefgh", [b"zabcdefghz"], "--json")
        data = json.loads(out)
        self.assertEqual(data["copy_length"], 8)
        self.assertEqual(data["covered_bytes"], 8)
        self.assertTrue(all(type(v) is int for v in data.values()))
        self.assertNotIn("run", data)
        shown = json.loads(self.cli(b"abcdefgh", [b"zabcdefghz"], "--json", "--show"))
        self.assertEqual(shown["run"], "abcdefgh")

    def test_bad_threshold_is_refused(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.cli(b"a", [b"a"], "--min-run", "0")


if __name__ == "__main__":
    unittest.main()
