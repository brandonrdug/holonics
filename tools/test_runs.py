#!/usr/bin/env -S python3 -I
"""Controls of runs.py's failure lines and of the lap notes `start` prints (host text only; no run is dispatched, read or stopped).

A log line reports a failure when a failure word stands outside the counts that read zero: every FIELD_LAP line prints
next_refused=0, and the watch flagged each lap line of the P8 laps (November 11) until counts at zero were set aside.
A count above zero, an error, a panic, a kill, a traceback and a busy lock still read as failures.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import runs  # noqa: E402

CASES = {
    "FIELD_LAP lap=1 section=12 own=1.72 next_refused=0 halvings=0 ms=3401": False,
    "FIELD_SECTION refused=00 next_refused=0": False,
    "refused=0 error_count=0.000 panics=0": False,
    "FIELD_LAP lap=1 section=12 next_refused=3": True,
    "next_refused=0.5": True,
    "error: the card refused the field: a sum outgrew its 128-bit carrier": True,
    "thread 'main' panicked at src/lib.rs": True,
    "Killed": True,
    "Traceback (most recent call last):": True,
    "LOCK_BUSY .local/gpu.lock": True,
}


def lap_notes_control():
    """`start` prints the lap procedure's notes and never depends on them: a training script without its loudness read gets
    that note, a script that trains nothing gets none, and a script that cannot be read gets one line and no exception."""
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        lap = os.path.join(d, "lap.sh")
        with open(lap, "w", encoding="utf-8") as f:
            f.write("# G-1118-1\n( flock 9; timeout 9 athena train complete-language train-store ) 9>.local/gpu.lock\n"
                    "athena train complete-language read-cavity MEAN.3000 known\nathena host complete-language write-next\n")
        read = os.path.join(d, "read.sh")
        with open(read, "w", encoding="utf-8") as f:
            f.write("athena train complete-language read-cavity STATE.3000\n")
        notes = runs.lap_notes(lap)
        assert len(notes) == 1 and "rule=7" in notes[0] and notes[0].startswith("LAP_CHECK lap.sh "), notes
        assert runs.lap_notes(read) == []
        missing = runs.lap_notes(os.path.join(d, "absent.sh"))
        assert len(missing) == 1 and missing[0].startswith("LAP_CHECK not read: "), missing


def main():
    wrong = [(text, want) for text, want in CASES.items() if runs.failure(text) != want]
    assert not wrong, wrong
    lap_notes_control()
    print(f"runs failure lines: {len(CASES)} lines, the controls hold; the lap notes print at start and never stop it")


if __name__ == "__main__":
    main()
