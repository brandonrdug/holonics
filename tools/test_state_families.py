"""Checks tools/state_families.py on synthetic states: a state's parts read from its head lines (its field's, its level's and its units'),
a parity state that carries every part the line's state does passes, one without the line's fades fails with them named (the case of
November 28: LINE_W109's state held no fade while the line trained it), and an unknown head line is refused."""
import os
import subprocess
import sys
import tempfile
import unittest

TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "state_families.py")
# W134's head line: the carry, the opening, the mark, the pump, the friction and its gate, the rings' fades and the classes' fade rates.
FADED = "hnn-field-v14s 257 224 4 8 2 1088 4 4 3771 7 0 512 0 1 0 1 0 0 0 1 0 2 3"
# W108's: the same parts without the fades (`hnn-field-v14r`, its friction word two).
UNFADED = "hnn-field-v14r 257 224 4 8 2 1088 4 4 3771 7 0 512 0 1 0 1 0 0 0 1 0 2"


def state(head, level=True, units=True, learner=True):
    out = "hnn-field-learner-v3 12 2115584 81 -\n" if learner else ""
    out += head + "\n" + " ".join(["128", "-256"] * 50) + "\n"
    if level:
        out += "level 6 2\nhnn-field-v14 2 64 4 8 2 128 2 4 3771 2 0\n" + " ".join(["7"] * 40) + "\n" + " ".join(["1"] * 30) + "\n"
    if units:
        out += "units 4096 8\n0 0 427 810\n1 0 0 1\n"
    return out


class StateFamilies(unittest.TestCase):
    def run_tool(self, *states, covers=False):
        with tempfile.TemporaryDirectory() as d:
            paths = []
            for k, text in enumerate(states):
                p = os.path.join(d, f"STATE{k}")
                open(p, "w").write(text)
                paths.append(p)
            args = ["--covers", *paths] if covers else paths
            p = subprocess.run([sys.executable, "-I", TOOL, *args], capture_output=True, text=True)
            return p.returncode, p.stdout

    def test_a_states_parts(self):
        code, out = self.run_tool(state(FADED))
        self.assertEqual(code, 0, out)
        self.assertIn("parts=carry,fade,fade_rate,friction,friction_gate,level,mark,opening,pump,units", out)

    def test_a_bare_field_and_the_older_heads(self):
        code, out = self.run_tool(state("hnn-field-v14 100 64 4 8 2 64 4 4 3771 2 0", level=False, units=False, learner=False))
        self.assertEqual(code, 0, out)
        self.assertIn("parts=-", out)
        code, out = self.run_tool(state("hnn-field-v14m 100 64 4 8 2 64 4 4 3771 2 0 4 0 1 0 1", level=False, units=False))
        self.assertEqual(code, 0, out)
        self.assertIn("parts=carry,mark,opening", out)

    def test_a_parity_state_carrying_every_part_passes(self):
        code, out = self.run_tool(state(FADED), state(FADED, units=False), covers=True)
        self.assertEqual(code, 0, out)
        self.assertIn("GATE_PARITY_FAMILIES covered", out)

    def test_a_parity_state_without_the_lines_fades_fails(self):
        code, out = self.run_tool(state(UNFADED, units=False), state(FADED), covers=True)
        self.assertEqual(code, 1, out)
        self.assertIn("GATE_PARITY_FAMILIES missing fade,fade_rate,units", out)

    def test_a_level_field_part_is_named_under_the_level(self):
        line = state(FADED).replace("hnn-field-v14 2 64 4 8 2 128 2 4 3771 2 0", "hnn-field-v14s 2 64 4 8 2 128 2 4 3771 2 0 0 0 0 0 0 0 0 0 0 0 0 1")
        code, out = self.run_tool(state(FADED), line, covers=True)
        self.assertEqual(code, 1, out)
        self.assertIn("GATE_PARITY_FAMILIES missing level.fade", out)

    def test_an_unknown_head_is_refused(self):
        code, out = self.run_tool(state("hnn-field-v14z 257 224 4 8 2 1088 4 4 3771 7 0 512"))
        self.assertEqual(code, 1, out)
        self.assertIn("GATE_PARITY_FAMILIES refused", out)


if __name__ == "__main__":
    unittest.main()
