"""Checks tools/reproduction.py on synthetic logs: equal lines pass with timings and the schedule fields differing, and a differing section or
save field fails with its name printed."""
import os
import subprocess
import sys
import tempfile
import unittest

TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reproduction.py")


def section(k, code, ms):
    return f"STORE_SECTION k={k} sites=40 code={code} regions_ms={ms} deposit_ms={ms} ms={ms}\n"


def save(k, moved, batches, peak, ms):
    return f"STORE_SAVE k={k} sections={k} moved={moved} batches={batches} peak_store={peak} ms={ms}\n"


class Reproduction(unittest.TestCase):
    def run_tool(self, build, line, sections, *flags):
        with tempfile.TemporaryDirectory() as d:
            a, b = os.path.join(d, "build.log"), os.path.join(d, "line.log")
            open(a, "w").write(build)
            open(b, "w").write(line)
            p = subprocess.run([sys.executable, "-I", TOOL, a, b, str(sections), *flags], capture_output=True, text=True)
            return p.returncode, p.stdout

    def test_equal_with_timings_and_schedule_aside(self):
        line = "".join(section(k, 100 + k, 400) for k in range(3)) + save(3, 7, 3, 8410613236, 1200) + section(3, 9, 1)
        build = "".join(section(k, 100 + k, 300) for k in range(3)) + save(3, 7, 4, 8400000000, 900)
        code, out = self.run_tool(build, line, 3)
        self.assertEqual(code, 0, out)
        self.assertIn("GATE_REPRO sections=3 line_lines=3 equal=3 EQUAL", out)
        self.assertIn("GATE_SAVE k=3 EQUAL timings_and_schedule_aside batches=4 line_batches=3 peak_store=8400000000 line_peak_store=8410613236", out)

    def test_a_differing_section_names_its_field(self):
        line = "".join(section(k, 100 + k, 400) for k in range(3))
        build = section(0, 100, 1) + section(1, 999, 1) + section(2, 102, 1)
        code, out = self.run_tool(build, line, 3)
        self.assertEqual(code, 1, out)
        self.assertIn("equal=2 DIFFERS", out)
        self.assertIn("first_differing_section=1 fields=code", out)

    def test_a_differing_save_field_fails(self):
        line = section(0, 1, 1) + save(1, 7, 1, 5, 1)
        build = section(0, 1, 2) + save(1, 8, 1, 5, 2)
        code, out = self.run_tool(build, line, 1)
        self.assertEqual(code, 1, out)
        self.assertIn("GATE_SAVE differing_fields=moved", out)

    def test_a_save_the_line_lacks_differs_unless_set_aside(self):
        line = "".join(section(k, k, 1) for k in range(30)) + save(1000, 7, 1, 5, 1)
        build = "".join(section(k, k, 2) for k in range(24)) + save(24, 3, 1, 5, 2)
        code, out = self.run_tool(build, line, 24)
        self.assertEqual(code, 1, out)
        self.assertIn("GATE_SAVE k=24 line_save=absent DIFFERS", out)
        code, out = self.run_tool(build, line, 24, "--no-save")
        self.assertEqual(code, 0, out)
        self.assertIn("equal=24 EQUAL", out)
        self.assertIn("GATE_SAVE aside", out)
        code, out = self.run_tool(section(0, 0, 1) + section(1, 9, 1), line, 2, "--no-save")
        self.assertEqual(code, 1, out)

    def test_short_build_differs(self):
        line = "".join(section(k, k, 1) for k in range(3))
        code, out = self.run_tool(section(0, 0, 1), line, 3)
        self.assertEqual(code, 1, out)
        self.assertIn("sections=1 line_lines=3 equal=1 DIFFERS", out)


if __name__ == "__main__":
    unittest.main()
