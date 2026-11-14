#!/usr/bin/env -S python3 -I
"""Controls for measure.py: the command's status passes through, and the line carries the name, the status, a wall time and a peak."""
import os
import re
import subprocess
import sys

TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "measure.py")


def run(*args):
    return subprocess.run([sys.executable, "-I", TOOL, *args], capture_output=True, text=True)


def main():
    ok = run("a", sys.executable, "-c", "x = bytearray(64 << 20); print('child')")
    assert ok.returncode == 0, ok
    lines = ok.stdout.splitlines()
    assert lines[0] == "child", lines
    m = re.fullmatch(r"MEASURE lap=a rc=0 wall_s=(\d+\.\d) peak_rss_kib=(\d+)", lines[1])
    assert m and int(m.group(2)) >= 64 << 10, lines
    bad = run("b", sys.executable, "-c", "import sys; sys.exit(3)")
    assert bad.returncode == 3 and re.fullmatch(r"MEASURE lap=b rc=3 wall_s=\d+\.\d peak_rss_kib=\d+", bad.stdout.strip()), bad
    print("measure controls: 2 passed")


if __name__ == "__main__":
    main()
